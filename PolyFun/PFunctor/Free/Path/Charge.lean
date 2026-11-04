/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Charge
public import PolyFun.PFunctor.Free.Cost.Value
public import PolyFun.PFunctor.Free.Path.Execution
public import PolyFun.PFunctor.Free.Displayed.Decoration

/-!
# Charges along completed paths

`Path.charge c x p` is the total charge of the calls along the completed path `p` through `x`: the
cost of one run, once every answer is fixed. It is the additive valuation of the path's event
trace (`charge_eq_traceList_charge`).

A structural bound bounds every completed path (`charge_le_of_isChargeBound`). The converse needs
every reachable call to have an answer (`isChargeBound_of_forall_charge_le`, under
`ProgramProgress`): a call with no answers ends no completed path, but `IsChargeBound` still
charges it. The worst-case cost is at least the charge of every completed path
(`charge_le_cost`).

The completed-path reading has its own calculus, valid for any ordered cost type, including
signed weights, for which a prefix may overspend a budget that every completed path respects:

* `splitBind` splits a path through `x.bind f` into a path through `x` and a path through the
  continuation at its output, and the charge adds (`charge_splitBind`);
* paths pull back along lenses and leaf maps with the pulled-back charge (`charge_pullMapLens`,
  `charge_pullMap`), and along a lens whose charges agree up to an additive map the charge is
  that map applied (`charge_mapLens_eq_map`);
* a path through a simulated program refines to a path through the source program with the
  same output and at least its charge, when each implementation is within its call's charge on
  every completed path (`exists_path_liftM`, `charge_liftM_le_of_forall`);
* with subsingleton answers there is exactly one path, so the completed-path bound is the charge
  of that path (`forall_charge_le_iff_ofHandler`).

Charges that depend on the node rather than the operation are decorations: `Path.chargeDec`
sums the weights a `Decoration (fun _ => ω)` puts on the nodes along a path. It generalizes
`Path.charge` (`chargeDec_ofCharge`), and node weights at most `b` bound it by `length • b`
(`chargeDec_le_length_nsmul`).
-/

@[expose] public section

universe uA uB uA₂ uB₂ v v' w w'

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v} {ω : Type w}

/-- A program in which every reachable call has an answer has a completed path. -/
theorem ProgramProgress.nonempty_path {x : FreeM P α} (hx : x.ProgramProgress) :
    Nonempty (Path x) := by
  induction x using FreeM.rec with
  | pure a => exact ⟨PUnit.unit⟩
  | liftBind a r ih =>
    obtain ⟨⟨b⟩, hr⟩ := hx
    obtain ⟨p⟩ := ih b (hr b)
    exact ⟨⟨b, p⟩⟩

namespace Path

/-- The total charge of the calls along a completed path. -/
def charge [Add ω] [Zero ω] (c : P.A → ω) : (x : FreeM P α) → Path x → ω
  | .pure _, _ => 0
  | .liftBind a next, ⟨answer, tail⟩ => c a + charge c (next answer) tail

variable {c : P.A → ω}

@[simp]
theorem charge_pure [Add ω] [Zero ω] (a : α) (p : Path (pure a : FreeM P α)) :
    charge c (pure a) p = 0 :=
  rfl

theorem charge_liftBind [Add ω] [Zero ω] (a : P.A) (next : P.B a → FreeM P α) (answer : P.B a)
    (tail : Path (next answer)) :
    charge c (FreeM.liftBind a next) ⟨answer, tail⟩ = c a + charge c (next answer) tail :=
  rfl

/-- The charge of a path is the valuation of its event trace by the charge of each call. -/
theorem charge_eq_traceList_charge [AddMonoid ω] (x : FreeM P α) (p : Path x) :
    charge c x p = TraceList.charge (fun i => c i.1) (trace x p) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    exact congrArg (c a + ·) (ih b p)

/-- The number of calls along a path is its unit charge. -/
theorem length_eq_charge_one (x : FreeM P α) (p : Path x) :
    length x p = charge (fun _ => 1) x p := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    rw [length_liftBind, charge_liftBind, ih, add_comm]

section Ordered

variable [AddCommMonoid ω] [PartialOrder ω] {B s : ω}

/-- A structural bound bounds the charge of every completed path. -/
theorem charge_le_of_isChargeBound {x : FreeM P α} (h : x.IsChargeBound c B s) (p : Path x) :
    s + charge c x p ≤ B := by
  induction x using FreeM.rec generalizing s with
  | pure a => simpa using h
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    rw [charge_liftBind, ← add_assoc]
    exact ih b (h.2 b) p

/-- When every reachable call has an answer, bounding the completed paths bounds the program. -/
theorem isChargeBound_of_forall_charge_le [CanonicallyOrderedAdd ω]
    {x : FreeM P α} (hx : x.ProgramProgress) (h : ∀ p : Path x, s + charge c x p ≤ B) :
    x.IsChargeBound c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => simpa using h PUnit.unit
  | liftBind a r ih =>
    obtain ⟨⟨b₀⟩, hr⟩ := hx
    obtain ⟨p₀⟩ := (hr b₀).nonempty_path
    have hpath : ∀ b (p : Path (r b)), (s + c a) + charge c (r b) p ≤ B := fun b p => by
      rw [add_assoc]; exact h ⟨b, p⟩
    exact ⟨le_self_add.trans (hpath b₀ p₀), fun b => ih b (hr b) (hpath b)⟩

end Ordered

/-- The worst-case cost is at least the charge of every completed path. -/
theorem charge_le_cost [AddCommMonoid ω] [CompleteLattice ω] [IsOrderedAddMonoid ω]
    (x : FreeM P α) (p : Path x) : charge c x p ≤ cost c x := by
  induction x using FreeM.rec with
  | pure a => exact le_rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    rw [charge_liftBind, cost_liftBind]
    exact add_le_add le_rfl ((ih b p).trans (le_iSup (fun b => cost c (r b)) b))

/-! ## The completed-path calculus -/

/-- Split a completed path through `x.bind f` into a path through `x` and a path through the
continuation at that path's output. -/
def splitBind {β : Type v'} : (x : FreeM P α) → (f : α → FreeM P β) → Path (FreeM.bind x f) →
    (p : Path x) × Path (f (output x p))
  | .pure _, _, q => ⟨⟨⟩, q⟩
  | .liftBind _ r, f, ⟨b, q⟩ =>
      let rest := splitBind (r b) f q
      ⟨⟨b, rest.1⟩, rest.2⟩

theorem output_splitBind {β : Type v'} (x : FreeM P α) (f : α → FreeM P β)
    (q : Path (FreeM.bind x f)) :
    output (FreeM.bind x f) q = output (f (output x (splitBind x f q).1)) (splitBind x f q).2 := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases q with ⟨b, q⟩
    exact ih b q

theorem charge_splitBind [AddMonoid ω] {β : Type v'} (x : FreeM P α) (f : α → FreeM P β)
    (q : Path (FreeM.bind x f)) :
    charge c (FreeM.bind x f) q =
      charge c x (splitBind x f q).1 + charge c _ (splitBind x f q).2 := by
  induction x using FreeM.rec with
  | pure a => exact (zero_add _).symm
  | liftBind a r ih =>
    rcases q with ⟨b, q⟩
    change c a + charge c _ q = (c a + charge c (r b) (splitBind (r b) f q).1) + _
    rw [ih b q, add_assoc]
    rfl

theorem output_pullMapLens {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q) (x : FreeM P α)
    (q : Path (x.mapLens l)) : output x (pullMapLens l x q) = output (x.mapLens l) q := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases q with ⟨d, q⟩
    exact ih _ q

theorem charge_pullMapLens [Add ω] [Zero ω] {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q)
    {d : Q.A → ω} (x : FreeM P α) (q : Path (x.mapLens l)) :
    charge d (x.mapLens l) q = charge (d ∘ l.toFunA) x (pullMapLens l x q) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases q with ⟨e, q⟩
    exact congrArg (d (l.toFunA a) + ·) (ih _ q)

theorem charge_pullMap [Add ω] [Zero ω] {β : Type v'} (f : α → β) (x : FreeM P α)
    (q : Path (x.map f)) : charge c (x.map f) q = charge c x (pullMap f x q) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases q with ⟨b, q⟩
    exact congrArg (c a + ·) (ih b q)

/-- The charge of a path pushes forward along an additive map. -/
theorem charge_map_addMonoidHom {ω' : Type w'} [AddMonoid ω] [AddMonoid ω'] (φ : ω →+ ω')
    (x : FreeM P α) (p : Path x) : charge (φ ∘ c) x p = φ (charge c x p) := by
  induction x using FreeM.rec with
  | pure a => exact φ.map_zero.symm
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    change φ (c a) + charge (φ ∘ c) (r b) p = φ (c a + charge c (r b) p)
    rw [ih b p, map_add]

/-- Relabelling along a lens whose target charge agrees with the source charge up to an additive
map `φ` charges every path by `φ` of the charge of its pullback. -/
theorem charge_mapLens_eq_map {ω' : Type w'} [AddMonoid ω] [AddMonoid ω']
    {Q : PFunctor.{uA₂, uB₂}} (φ : ω →+ ω') (l : Lens P Q) {d : Q.A → ω'}
    (hcd : ∀ a, d (l.toFunA a) = φ (c a)) (x : FreeM P α) (q : Path (x.mapLens l)) :
    charge d (x.mapLens l) q = φ (charge c x (pullMapLens l x q)) := by
  rw [charge_pullMapLens, ← charge_map_addMonoidHom]
  exact congrArg (charge · x _) (funext hcd)

section Refinement

variable [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω] {Q : PFunctor.{uA₂, uB}}
  {α : Type uB}

/-- **Completed-path transfer through a free handler.** If every completed path through the
implementation of a call at `a` is charged at most `c a`, then every completed path through the
simulated program refines to a completed path through the source program with the same output
and at least its charge. No sign condition on the cost type is needed. -/
theorem exists_path_liftM (h : (a : P.A) → FreeM Q (P.B a)) {d : Q.A → ω}
    (hstep : ∀ a (r : Path (h a)), charge d (h a) r ≤ c a) (x : FreeM P α)
    (q : Path (x.liftM h)) :
    ∃ p : Path x, output x p = output (x.liftM h) q ∧ charge d (x.liftM h) q ≤ charge c x p := by
  induction x using FreeM.rec with
  | pure a => exact ⟨⟨⟩, rfl, le_rfl⟩
  | liftBind a r ih =>
    let s := splitBind (h a) (fun b => (r b).liftM h) q
    obtain ⟨p, hout, hle⟩ := ih (output (h a) s.1) s.2
    refine ⟨⟨output (h a) s.1, p⟩, ?_, ?_⟩
    · exact hout.trans (output_splitBind (h a) (fun b => (r b).liftM h) q).symm
    · exact (charge_splitBind (c := d) (h a) (fun b => (r b).liftM h) q).trans_le
        (add_le_add (hstep a s.1) hle)

/-- Completed-path bounds transfer through a free handler. -/
theorem charge_liftM_le_of_forall (h : (a : P.A) → FreeM Q (P.B a)) {d : Q.A → ω} {B : ω}
    (hstep : ∀ a (r : Path (h a)), charge d (h a) r ≤ c a) {x : FreeM P α}
    (hx : ∀ p : Path x, charge c x p ≤ B) (q : Path (x.liftM h)) :
    charge d (x.liftM h) q ≤ B := by
  obtain ⟨p, -, hle⟩ := exists_path_liftM h hstep x q
  exact hle.trans (hx p)

end Refinement

/-- With subsingleton answers a program has exactly one completed path. -/
instance subsingleton [∀ a, Subsingleton (P.B a)] (x : FreeM P α) : Subsingleton (Path x) := by
  induction x using FreeM.rec with
  | pure a => exact inferInstanceAs (Subsingleton PUnit)
  | liftBind a r ih =>
    constructor
    rintro ⟨b₁, p₁⟩ ⟨b₂, p₂⟩
    obtain rfl := Subsingleton.elim b₁ b₂
    rw [Subsingleton.elim p₁ p₂]

/-- With subsingleton answers the completed-path bound is the charge of the one path, which any
answering function picks. -/
theorem forall_charge_le_iff_ofHandler [∀ a, Subsingleton (P.B a)] [Add ω] [Zero ω] [LE ω]
    (choose : (a : P.A) → P.B a) (x : FreeM P α) {B : ω} :
    (∀ p : Path x, charge c x p ≤ B) ↔ charge c x (Path.ofHandler choose x) ≤ B :=
  ⟨fun h => h _, fun h p => Subsingleton.elim (Path.ofHandler choose x) p ▸ h⟩

/-! ## Charges that depend on the node -/

/-- The node weights of `x` read off the charge of each node's operation. -/
def decorationOfCharge [Add ω] [Zero ω] (c : P.A → ω) :
    (x : FreeM P α) → Displayed.Decoration (fun _ => ω) x
  | .pure _ => PUnit.unit
  | .liftBind a r => ⟨c a, fun b => decorationOfCharge c (r b)⟩

/-- The total weight of the nodes along a completed path. -/
def chargeDec [Add ω] [Zero ω] :
    (x : FreeM P α) → Displayed.Decoration (fun _ => ω) x → Path x → ω
  | .pure _, _, _ => 0
  | .liftBind _ r, ⟨w, ds⟩, ⟨b, p⟩ => w + chargeDec (r b) (ds b) p

/-- Every node weight is at most `b`. -/
def DecorationLE [LE ω] (bound : ω) : (x : FreeM P α) → Displayed.Decoration (fun _ => ω) x → Prop
  | .pure _, _ => True
  | .liftBind _ r, ⟨w, ds⟩ => w ≤ bound ∧ ∀ b, DecorationLE bound (r b) (ds b)

/-- Position charges are the node weights read off the operations. -/
theorem chargeDec_ofCharge [Add ω] [Zero ω] (x : FreeM P α) (p : Path x) :
    chargeDec x (decorationOfCharge c x) p = charge c x p := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    exact congrArg (c a + ·) (ih b p)

/-- Node weights at most `b` bound a path's weight by its length times `b`. -/
theorem chargeDec_le_length_nsmul [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω]
    {bound : ω} (x : FreeM P α) (d : Displayed.Decoration (fun _ => ω) x)
    (hd : DecorationLE bound x d) (p : Path x) : chargeDec x d p ≤ length x p • bound := by
  induction x using FreeM.rec with
  | pure a => exact (zero_nsmul bound).ge
  | liftBind a r ih =>
    rcases d with ⟨w, ds⟩
    rcases p with ⟨b, p⟩
    change w + chargeDec (r b) (ds b) p ≤ (length (r b) p + 1) • bound
    rw [succ_nsmul']
    exact add_le_add hd.1 (ih b (ds b) (hd.2 b) p)

end Path

end PFunctor.FreeM
