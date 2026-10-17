/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Lens

/-!
# Charge bounds on a register-machine command signature

The commands of a register machine with oracle ports are local operations on the current
register and calls of a port on a factor of the register. Their responses are lifted to a common
universe, and programs are `IFreeM` trees over registers whose leaf families may live in any
universe. This is the shape of downstream quantum query models.

A per-port query bound and a cost bound on local operations are `IFreeM.IsChargeBound`s. Their
command-level characterizations follow from the generic unfolding, the per-port bound agrees
with its direct recursive definition, and both budgets add under sequencing across leaf
universes.

The command signature is also the lifted coproduct of its local operations and its oracle calls,
at the same universes, and a program of local operations keeps its cost bound when it is
embedded into the coproduct.
-/

@[expose] public section

universe u v u₁ v₁ w w₁

namespace IPFunctorBoundTests

open IPFunctor

/-- Registers, with carriers in `Type`, so that `Reg : Type 1`. -/
structure Reg : Type 1 where
  /-- The carrier of the register. -/
  carrier : Type

instance : CoeSort Reg Type := ⟨Reg.carrier⟩

/-- The register with carrier `α`. -/
def Reg.of (α : Type) : Reg := ⟨α⟩

/-- Local operations on each register, their outcomes, and the register after each outcome. -/
structure LocalSig where
  /-- The operations on a register. -/
  Op : Reg → Type u
  /-- The outcomes of an operation. -/
  Outcome : {A : Reg} → Op A → Type v
  /-- The register after an outcome. -/
  next : {A : Reg} → (o : Op A) → Outcome o → Reg

/-- Oracle ports, each with an input register, an output register and a classical result. -/
structure PortSig where
  /-- The ports. -/
  Port : Type u₁
  /-- The input register of a port. -/
  In : Port → Reg
  /-- The output register of a port. -/
  Out : Port → Reg
  /-- The classical result of a port. -/
  Result : Port → Type v₁

/-- The commands at register `A`: a local operation, or a call of port `i` on the factor of `A`
that `ℓ` exposes. -/
inductive Cmd (L : LocalSig.{u, v}) (S : PortSig.{u₁, v₁}) (A : Reg) : Type (max 1 u u₁)
  | prim (o : L.Op A)
  | query (i : S.Port) (E : Reg) (ℓ : A ≃ S.In i × E)

variable {L : LocalSig.{u, v}} {S : PortSig.{u₁, v₁}}

/-- Responses, lifted to a common universe. -/
def Cmd.Resp {A : Reg} : Cmd L S A → Type (max v v₁)
  | .prim o => ULift.{v₁} (L.Outcome o)
  | .query i _ _ => ULift.{v} (S.Result i)

/-- The register after a command, given its response. -/
def Cmd.next {A : Reg} : (c : Cmd L S A) → c.Resp → Reg
  | .prim o, b => L.next o b.down
  | .query i E _, _ => Reg.of (S.Out i × E)

variable (L S) in
/-- The commands as an indexed polynomial endofunctor on registers. -/
def cmdIPF : IPFunctor.Endo.{1, max 1 u u₁, max v v₁} Reg where
  A := Cmd L S
  B _ c := c.Resp
  src _ c b := c.next b

/-- A continuation on a type, read as a continuation on its lift. -/
def onDown {α : Type v} {β : α → Sort w} (k : (a : α) → β a) :
    (b : ULift.{v₁} α) → β b.down :=
  fun b => k b.down

variable {X : Reg → Type w} {Y : Reg → Type w₁} {A : Reg}

/-- A local operation followed by a continuation on its outcome. -/
def primBind (o : L.Op A) (k : (b : L.Outcome o) → IFreeM (cmdIPF L S) X (L.next o b)) :
    IFreeM (cmdIPF L S) X A :=
  IFreeM.liftBind (P := cmdIPF L S) (.prim o) (onDown k)

/-- A call of port `i` followed by a continuation on its result. -/
def queryBind (i : S.Port) (E : Reg) (ℓ : A ≃ S.In i × E)
    (k : S.Result i → IFreeM (cmdIPF L S) X (Reg.of (S.Out i × E))) :
    IFreeM (cmdIPF L S) X A :=
  IFreeM.liftBind (P := cmdIPF L S) (.query i E ℓ) (onDown k)

/-! ## The charges -/

open scoped Classical in
/-- The charge of a call of port `j` toward the budget of port `i`. Port equality is decided
classically, so the ports need no decidable equality. -/
noncomputable def portCharge (i j : S.Port) : ℕ := if j = i then 1 else 0

/-- One charge step for port `i` at a call of port `j`, split on whether `j` is `i`. -/
lemma portCharge_step_iff (i j : S.Port) (n : ℕ) {p : ℕ → Prop} :
    (portCharge i j ≤ n ∧ p (n - portCharge i j)) ↔
      (j = i → 0 < n ∧ p (n - 1)) ∧ (j ≠ i → p n) := by
  by_cases hj : j = i
  · subst hj
    simp [portCharge, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  · simp [portCharge, hj]

/-- A call of port `i` costs one; local operations and the other ports are free. -/
noncomputable def queryCharge (i : S.Port) : (A : Reg) → (cmdIPF L S).A A → ℕ
  | _, .prim _ => 0
  | _, .query j _ _ => portCharge i j

/-- A local operation `o` costs `c o`; calls are free. -/
def primCharge (c : ∀ ⦃A : Reg⦄, L.Op A → ℕ) : (A : Reg) → (cmdIPF L S).A A → ℕ
  | _, .prim o => c o
  | _, .query _ _ _ => 0

/-! ## A per-port query bound -/

/-- Every branch of `x` calls port `i` at most `n` times. -/
def IsQueryBoundAt (x : IFreeM (cmdIPF L S) X A) (i : S.Port) (n : ℕ) : Prop :=
  IFreeM.IsChargeBound x (queryCharge i) n

variable {i : S.Port} {n m : ℕ}

theorem isQueryBoundAt_primBind_iff (o : L.Op A)
    (k : (b : L.Outcome o) → IFreeM (cmdIPF L S) X (L.next o b)) :
    IsQueryBoundAt (primBind o k) i n ↔ ∀ b, IsQueryBoundAt (k b) i n :=
  ⟨fun h b => h.2 (ULift.up b), fun h => ⟨Nat.zero_le n, fun y => h y.down⟩⟩

theorem isQueryBoundAt_queryBind_iff (j : S.Port) (E : Reg) (ℓ : A ≃ S.In j × E)
    (k : S.Result j → IFreeM (cmdIPF L S) X (Reg.of (S.Out j × E))) :
    IsQueryBoundAt (queryBind j E ℓ k) i n ↔
      (j = i → 0 < n ∧ ∀ r, IsQueryBoundAt (k r) i (n - 1)) ∧
        (j ≠ i → ∀ r, IsQueryBoundAt (k r) i n) :=
  (show _ ↔ portCharge i j ≤ n ∧ ∀ r, IsQueryBoundAt (k r) i (n - portCharge i j) from
    ⟨fun h => ⟨h.1, fun r => h.2 (ULift.up r)⟩, fun h => ⟨h.1, fun y => h.2 y.down⟩⟩).trans
    (portCharge_step_iff (p := fun m => ∀ r, IsQueryBoundAt (k r) i m) i j n)

/-- The per-port query bound by direct recursion on the tree. -/
def IsQueryBoundAtRec (i : S.Port) : {A : Reg} → IFreeM (cmdIPF L S) X A → ℕ → Prop
  | _, .pure _, _ => True
  | _, .liftBind (.prim _) k, n => ∀ b, IsQueryBoundAtRec i (k (ULift.up b)) n
  | _, .liftBind (.query j _ _) k, n =>
      (j = i → 0 < n ∧ ∀ r, IsQueryBoundAtRec i (k (ULift.up r)) (n - 1)) ∧
        (j ≠ i → ∀ r, IsQueryBoundAtRec i (k (ULift.up r)) n)

/-- The charge bound agrees with the recursive definition. -/
theorem isQueryBoundAtRec_iff (x : IFreeM (cmdIPF L S) X A) :
    IsQueryBoundAtRec i x n ↔ IsQueryBoundAt x i n := by
  induction x using IFreeM.inductionOn generalizing n with
  | pure => exact iff_of_true trivial trivial
  | liftBind A c k ih =>
    cases c with
    | prim o => exact ⟨fun h => ⟨Nat.zero_le n, fun y => (ih y).1 (h y.down)⟩,
        fun h b => (ih _).2 (h.2 (ULift.up b))⟩
    | query j E ℓ =>
      have hp (m : ℕ) : (∀ r, IsQueryBoundAtRec i (k (ULift.up r)) m) ↔
          ∀ y, IsQueryBoundAt (k y) i m :=
        ⟨fun h y => (ih y).1 (h y.down), fun h r => (ih _).2 (h _)⟩
      exact (and_congr (imp_congr_right fun _ => and_congr_right fun _ => hp _)
        (imp_congr_right fun _ => hp _)).trans
        (portCharge_step_iff (p := fun m => ∀ y, IsQueryBoundAt (k y) i m) i j n).symm

variable {x : IFreeM (cmdIPF L S) X A} {k : ∀ B, X B → IFreeM (cmdIPF L S) Y B}

theorem IsQueryBoundAt.mono (hx : IsQueryBoundAt x i n) (hnm : n ≤ m) : IsQueryBoundAt x i m :=
  IFreeM.IsChargeBound.mono hx hnm

/-- Budgets on one port add under sequencing, with the leaves of `x` and `k` in different
universes. -/
theorem IsQueryBoundAt.bind (hx : IsQueryBoundAt x i n) (hk : ∀ B y, IsQueryBoundAt (k B y) i m) :
    IsQueryBoundAt (x.bind k) i (n + m) :=
  IFreeM.isChargeBound_bind hx hk

/-! ## A cost bound on local operations -/

/-- Along every branch of `x`, the local operations cost at most `n` in total. -/
def IsCostBound (c : ∀ ⦃A : Reg⦄, L.Op A → ℕ) (x : IFreeM (cmdIPF L S) X A) (n : ℕ) : Prop :=
  IFreeM.IsChargeBound x (primCharge c) n

variable {c : ∀ ⦃A : Reg⦄, L.Op A → ℕ}

theorem isCostBound_primBind_iff (o : L.Op A)
    (k : (b : L.Outcome o) → IFreeM (cmdIPF L S) X (L.next o b)) :
    IsCostBound c (primBind o k) n ↔ c o ≤ n ∧ ∀ b, IsCostBound c (k b) (n - c o) :=
  ⟨fun h => ⟨h.1, fun b => h.2 (ULift.up b)⟩, fun h => ⟨h.1, fun y => h.2 y.down⟩⟩

theorem isCostBound_queryBind_iff (j : S.Port) (E : Reg) (ℓ : A ≃ S.In j × E)
    (k : S.Result j → IFreeM (cmdIPF L S) X (Reg.of (S.Out j × E))) :
    IsCostBound c (queryBind j E ℓ k) n ↔ ∀ r, IsCostBound c (k r) n :=
  ⟨fun h r => h.2 (ULift.up r), fun h => ⟨Nat.zero_le n, fun y => h y.down⟩⟩

/-- Costs add under sequencing, with the leaves of `x` and `k` in different universes. -/
theorem IsCostBound.bind (hx : IsCostBound c x n) (hk : ∀ B y, IsCostBound c (k B y) m) :
    IsCostBound c (x.bind k) (n + m) :=
  IFreeM.isChargeBound_bind hx hk

/-! ## The command signature as a lifted coproduct -/

variable (L) in
/-- The local operations as an indexed polynomial. -/
def primIPF : IPFunctor.Endo.{1, u, v} Reg where
  A := L.Op
  B _ o := L.Outcome o
  src _ o b := L.next o b

variable (S) in
/-- The oracle calls as an indexed polynomial: a port and an exposed factor of the register. -/
def queryIPF : IPFunctor.Endo.{1, max 1 u₁, v₁} Reg where
  A A := Σ i : S.Port, Σ E : Reg, A ≃ S.In i × E
  B _ q := S.Result q.1
  src _ q _ := Reg.of (S.Out q.1 × q.2.1)

variable (L S) in
/-- The commands as a lifted coproduct, at the universes of `cmdIPF`. -/
abbrev cmdSum : IPFunctor.Endo.{1, max 1 u u₁, max v v₁} Reg :=
  (primIPF L).sumULift (queryIPF S)

/-- The cost charge on the coproduct, by cases on the summand. -/
def sumCharge (c : ∀ ⦃A : Reg⦄, L.Op A → ℕ) : (A : Reg) → (cmdSum L S).A A → ℕ :=
  fun _ => Sum.elim (fun o => c o) fun _ => 0

/-- A program of local operations alone keeps its cost bound in the coproduct. -/
example {x : IFreeM (primIPF L) X A} (h : IFreeM.IsChargeBound x (fun _ o => c o) n) :
    IFreeM.IsChargeBound (x.mapLens (Lens.inlULift (Q := queryIPF S))) (sumCharge c) n :=
  h.mapLens _

end IPFunctorBoundTests
