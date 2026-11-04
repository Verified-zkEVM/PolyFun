/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Path.Charge
public import PolyFun.Control.Monad.Graded

/-!
# Measured programs and budgeted carriers

**Measured programs.** A `MeasuredProgram Input Result ω` computes a function by a free program
whose interface depends on a view of the input:
- the view is computed outside the program, and is not charged;
- calls are answered by a deterministic answering function (`answer`);
- each operation has a price (`cost`).

`run` interprets the program through the deterministic answers, and is the output of the one path
they pick (`run_eq_output`). `Realizes f` says the run computes `f`, and `CostAtMost B` bounds the
charge of every completed path of every view's program, so signed prices are allowed. `ofFun f`
computes `f` with no operations at cost `0`.

`comp outer inner` runs `inner`, computes `outer`'s view from the actual intermediate result, and
runs `outer`. It does this on the sum of `inner`'s operations and the dependent sum of `outer`'s
operations over its views, keeping both price lists. It computes the composite
(`run_comp`, `Realizes.comp`), and its budgets add (`CostAtMost.comp`). `contramap` precomposes an
uncharged map on inputs. A `BudgetedProgram f ω` bundles a measured program realizing `f` with a
budget, and composes the same way.

**Budgeted carriers.** `Budgeted c B α` is the subtype of free programs within budget `B`. With
budgets graded by `Multiplicative ω`, it is a `GradedMonad`: `gbind` adds budgets.
-/

@[expose] public section

universe u w

namespace PFunctor.FreeM

/-! ## Deterministic paths through binds and relabellings -/

section Deterministic

variable {P : PFunctor.{u, u}} {α β : Type u}

/-- The path an answering function picks through a sequence passes through the path it picks
through the first part. -/
theorem output_bind_ofHandler (choose : (a : P.A) → P.B a) (x : FreeM P α)
    (f : α → FreeM P β) :
    output (FreeM.bind x f) (Path.ofHandler choose (FreeM.bind x f)) =
      output (f (output x (Path.ofHandler choose x)))
        (Path.ofHandler choose (f (output x (Path.ofHandler choose x)))) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih => exact ih (choose a)

/-- Relabelling along a lens, the path an answering function picks is the path the pulled-back
answering function picks. -/
theorem output_mapLens_ofHandler {Q : PFunctor.{u, u}} (l : Lens P Q)
    (choose : (a : Q.A) → Q.B a) (x : FreeM P α) :
    output (x.mapLens l) (Path.ofHandler choose (x.mapLens l)) =
      output x (Path.ofHandler (fun a => l.toFunB a (choose (l.toFunA a))) x) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih => exact ih _

end Deterministic

/-! ## Measured programs -/

/-- A function computed by a free program over an interface that depends on an uncharged view of
the input, answered deterministically, with a price per operation. -/
structure MeasuredProgram (Input Result : Type u) (ω : Type w) where
  /-- What the program is allowed to depend on. -/
  View : Type u
  /-- The uncharged view of an input. -/
  view : Input → View
  /-- The operations the program may call. -/
  Op : Type u
  /-- The answers to an operation, which may depend on the view. -/
  Ans : View → Op → Type u
  /-- The program of each view. -/
  program : (v : View) → FreeM ⟨Op, Ans v⟩ Result
  /-- The deterministic answers of each view. -/
  answer : (v : View) → (o : Op) → Ans v o
  /-- The price of each operation. -/
  cost : Op → ω

namespace MeasuredProgram

variable {Input Mid Result : Type u} {ω : Type w}

/-- Run the program of the input's view, answering every call deterministically. -/
def run (M : MeasuredProgram Input Result ω) (i : Input) : Result :=
  ((M.program (M.view i)).liftM fun o => (pure (M.answer (M.view i) o) : Id _)).run

/-- The run is the output of the path the answers pick. -/
theorem run_eq_output (M : MeasuredProgram Input Result ω) (i : Input) :
    M.run i = output (M.program (M.view i)) (Path.ofHandler (M.answer (M.view i)) _) := by
  unfold run
  induction M.program (M.view i) using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih => exact ih _

/-- The program computes `f`. -/
def Realizes (M : MeasuredProgram Input Result ω) (f : Input → Result) : Prop :=
  ∀ i, f i = M.run i

/-- Every completed path of every view's program costs at most `B`. -/
def CostAtMost [Add ω] [Zero ω] [LE ω] (M : MeasuredProgram Input Result ω) (B : ω) : Prop :=
  ∀ v (p : Path (M.program v)), Path.charge M.cost (M.program v) p ≤ B

/-- A cost bound holds for every larger budget. -/
theorem CostAtMost.mono [Add ω] [Zero ω] [Preorder ω] {M : MeasuredProgram Input Result ω}
    {B B' : ω} (h : M.CostAtMost B) (hB : B ≤ B') : M.CostAtMost B' :=
  fun v p => (h v p).trans hB

/-- The program with no operations that computes `f` on its whole input. -/
def ofFun (f : Input → Result) : MeasuredProgram Input Result ω where
  View := Input
  view := id
  Op := PEmpty
  Ans _ _ := PEmpty
  program v := pure (f v)
  answer _ o := o.elim
  cost o := o.elim

theorem realizes_ofFun (f : Input → Result) : (ofFun f (ω := ω)).Realizes f :=
  fun _ => rfl

/-- A program with no operations costs nothing. -/
theorem costAtMost_ofFun [Add ω] [Zero ω] [Preorder ω] (f : Input → Result) :
    (ofFun f (ω := ω)).CostAtMost 0 :=
  fun _ _ => le_rfl

/-- The answers of the composite interface: `inner`'s at its view, and `outer`'s at each of its
views. -/
def CompAns (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (v : inner.View) : inner.Op ⊕ (Σ _ : outer.View, outer.Op) → Type u
  | .inl o => inner.Ans v o
  | .inr ⟨v', o⟩ => outer.Ans v' o

/-- The inclusion of `inner`'s interface into the composite interface. -/
def innerLens (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (v : inner.View) : Lens ⟨inner.Op, inner.Ans v⟩ ⟨_, CompAns outer inner v⟩ :=
  ⟨Sum.inl, fun _ b => b⟩

/-- The inclusion of `outer`'s interface at view `v'` into the composite interface. -/
def outerLens (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (v : inner.View) (v' : outer.View) : Lens ⟨outer.Op, outer.Ans v'⟩ ⟨_, CompAns outer inner v⟩ :=
  ⟨fun o => Sum.inr ⟨v', o⟩, fun _ b => b⟩

/-- Run `inner`, compute `outer`'s view from the actual intermediate result without charging it,
and run `outer`, on the sum of the two interfaces with both price lists. -/
def comp (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω) :
    MeasuredProgram Input Result ω where
  View := inner.View
  view := inner.view
  Op := inner.Op ⊕ (Σ _ : outer.View, outer.Op)
  Ans := CompAns outer inner
  program v := (inner.program v).mapLens (innerLens outer inner v) >>= fun m =>
    (outer.program (outer.view m)).mapLens (outerLens outer inner v (outer.view m))
  answer v
    | .inl o => inner.answer v o
    | .inr ⟨v', o⟩ => outer.answer v' o
  cost
    | .inl o => inner.cost o
    | .inr ⟨_, o⟩ => outer.cost o

/-- The composite computes the composite function. -/
theorem run_comp (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (i : Input) : (outer.comp inner).run i = outer.run (inner.run i) := by
  simp only [run, comp, FreeM.liftM_bind, FreeM.liftM_mapLens]
  rfl

/-- The composite realizes the composite function. -/
theorem Realizes.comp {outer : MeasuredProgram Mid Result ω} {inner : MeasuredProgram Input Mid ω}
    {g : Mid → Result} {f : Input → Mid} (ho : outer.Realizes g) (hi : inner.Realizes f) :
    (outer.comp inner).Realizes (g ∘ f) := fun i => by
  rw [run_comp, Function.comp_apply, hi i, ho]

/-- Composite budgets add. -/
theorem CostAtMost.comp [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω]
    {outer : MeasuredProgram Mid Result ω} {inner : MeasuredProgram Input Mid ω} {B₁ B₂ : ω}
    (hi : inner.CostAtMost B₁) (ho : outer.CostAtMost B₂) :
    (outer.comp inner).CostAtMost (B₁ + B₂) := by
  intro v q
  have hq := Path.charge_splitBind (c := (outer.comp inner).cost)
    ((inner.program v).mapLens (innerLens outer inner v))
    (fun m => (outer.program (outer.view m)).mapLens (outerLens outer inner v (outer.view m))) q
  refine hq.trans_le (add_le_add ?_ ?_)
  · exact (Path.charge_pullMapLens _ _ _).trans_le (hi v _)
  · exact (Path.charge_pullMapLens _ _ _).trans_le (ho _ _)

/-- Precompose with an uncharged map on inputs. -/
def contramap {Input' : Type u} (M : MeasuredProgram Input Result ω) (g : Input' → Input) :
    MeasuredProgram Input' Result ω :=
  { M with view := M.view ∘ g }

theorem run_contramap {Input' : Type u} (M : MeasuredProgram Input Result ω) (g : Input' → Input)
    (i : Input') : (M.contramap g).run i = M.run (g i) :=
  rfl

theorem Realizes.contramap {Input' : Type u} {M : MeasuredProgram Input Result ω}
    {f : Input → Result} (h : M.Realizes f) (g : Input' → Input) :
    (M.contramap g).Realizes (f ∘ g) :=
  fun i => h (g i)

theorem CostAtMost.contramap [Add ω] [Zero ω] [LE ω] {Input' : Type u}
    {M : MeasuredProgram Input Result ω} {B : ω} (h : M.CostAtMost B) (g : Input' → Input) :
    (M.contramap g).CostAtMost B :=
  h

end MeasuredProgram

/-- A measured program realizing `f`, with a budget on every completed path. -/
structure BudgetedProgram {Input Result : Type u} (f : Input → Result) (ω : Type w) [Add ω]
    [Zero ω] [LE ω] where
  /-- The measured program. -/
  program : MeasuredProgram Input Result ω
  /-- The bound on the charge of every completed path. -/
  budget : ω
  /-- The program computes `f`. -/
  realizes : program.Realizes f
  /-- Every completed path costs at most the budget. -/
  costAtMost : program.CostAtMost budget

namespace BudgetedProgram

variable {Input Mid Result : Type u} {ω : Type w}

/-- Every function has a budgeted program with budget `0` and no operations. -/
def ofFun [Add ω] [Zero ω] [Preorder ω] (f : Input → Result) : BudgetedProgram f ω :=
  ⟨MeasuredProgram.ofFun f, 0, MeasuredProgram.realizes_ofFun f,
    MeasuredProgram.costAtMost_ofFun f⟩

/-- Precompose with an uncharged map on inputs. -/
def contramap [Add ω] [Zero ω] [LE ω] {Input' : Type u} {f : Input → Result}
    (M : BudgetedProgram f ω) (g : Input' → Input) : BudgetedProgram (f ∘ g) ω :=
  ⟨M.program.contramap g, M.budget, M.realizes.contramap g, M.costAtMost.contramap g⟩

/-- Compose budgeted programs; budgets add. -/
def comp [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω] {g : Mid → Result}
    {f : Input → Mid} (outer : BudgetedProgram g ω) (inner : BudgetedProgram f ω) :
    BudgetedProgram (g ∘ f) ω :=
  ⟨outer.program.comp inner.program, inner.budget + outer.budget,
    outer.realizes.comp inner.realizes, inner.costAtMost.comp outer.costAtMost⟩

end BudgetedProgram

/-! ## Budgeted carriers -/

section Graded

variable {P : PFunctor.{u, u}} {ω : Type u} [AddCommMonoid ω] [PartialOrder ω]
  [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]

/-- Free programs within budget `B`. -/
def Budgeted (c : P.A → ω) (B : Multiplicative ω) (α : Type u) : Type u :=
  {x : FreeM P α // x.IsChargeBound c (Multiplicative.toAdd B)}

/-- Budgeted programs form a graded monad: sequencing adds budgets. -/
instance (c : P.A → ω) : GradedMonad (Multiplicative ω) (Budgeted c) where
  gpure a := ⟨pure a, isChargeBound_pure a⟩
  gbind x f := ⟨FreeM.bind x.1 fun a => (f a).1, IsChargeBound.bind x.2 fun a => (f a).2⟩

end Graded

end PFunctor.FreeM
