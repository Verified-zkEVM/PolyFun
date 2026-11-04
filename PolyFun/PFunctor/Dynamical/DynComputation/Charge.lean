/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded
public import PolyFun.PFunctor.Resumption.Charge

/-!
# Charges on dynamical computations

A dynamical computation `M` steps from a state either to a result or to a call with one successor
state per answer. Its charge bound from a state is the safety reading on the finite unrollings
`M.unroll k state`, which are free programs: every unrolling stays within budget.

Every model that presents itself as a dynamical computation inherits this notion together with the
`FreeM` laws: free programs (`ofFreeM`), resumptions (`ofResumption`), and interaction trees with
their silent steps as calls. The bound is the resumption bound of the behaviour
(`isChargeBound_iff_behavior`), agrees with the program's bound on any machine implementing it
(`Implements.isChargeBound_init_iff`, with `isChargeBound_ofFreeM_iff` for `ofFreeM`), relabels
along lenses (`IsChargeBound.wrap`), and ignores the result type
(`isChargeBound_mapResult_iff`). `ImplementsWithinCharge` is bounded implementation with a charge
in place of a call count.
-/

@[expose] public section

universe u uA uB uA₂ uB₂ uα uβ uγ w

namespace PFunctor.DynSystem.DynComputation

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {γ : Type uγ} {ω : Type w}

/-- Every finite unrolling of `M` from `state` stays within budget `B`, with `spent` already
spent. -/
def IsChargeBound [Add ω] [LE ω] [Zero ω] (M : DynComputation.{u} p α β) (c : p.A → ω) (B : ω)
    (state : M.State) (spent : ω := 0) : Prop :=
  ∀ k, (M.unroll k state).IsChargeBound c B spent

/-- The worst-case cost of `M` from `state`: the supremum of the costs of its finite
unrollings. -/
noncomputable def cost [AddCommMonoid ω] [CompleteLattice ω] (M : DynComputation.{u} p α β)
    (c : p.A → ω) (state : M.State) : ω :=
  ⨆ k, FreeM.cost c (M.unroll k state)

variable [AddCommMonoid ω] [PartialOrder ω] {c : p.A → ω} {B s : ω}

/-- The bound of a machine is the resumption bound of its behaviour. -/
theorem isChargeBound_iff_behavior (M : DynComputation.{u} p α β) (state : M.State) :
    M.IsChargeBound c B state s ↔
      Resumption.IsChargeBound (M.toDynSystem.behavior state) c B s := by
  simp only [IsChargeBound, Resumption.IsChargeBound, unroll_eq_truncate]

/-- From an initial state, the bound of a machine is the resumption bound of its denotation. -/
theorem isChargeBound_init_iff_denote (M : DynComputation.{u} p α β) (input : α) :
    M.IsChargeBound c B (M.init input) s ↔ (M.denote input).IsChargeBound c B s := by
  simp only [IsChargeBound, Resumption.IsChargeBound, ← run_eq_truncate, run]

/-- A machine implementing a program family is within budget from each initial state exactly
when the program is. -/
theorem Implements.isChargeBound_init_iff [CanonicallyOrderedAdd ω] {M : DynComputation.{u} p α β}
    {program : α → FreeM p β} (hM : M.Implements program) (input : α) :
    M.IsChargeBound c B (M.init input) s ↔ (program input).IsChargeBound c B s := by
  rw [isChargeBound_init_iff_denote, hM input, Resumption.isChargeBound_toResumption_iff]

/-- `M` implements `program`, and every program of the family is within the uniform budget `B`
under `c`. The budget does not depend on the input: a size-dependent bound is stated by fixing the
size measure and the budget envelope separately. -/
def ImplementsWithinCharge (M : DynComputation.{u} p α β)
    (program : α → FreeM p β) (c : p.A → ω) (B : ω) : Prop :=
  M.Implements program ∧ ∀ input, (program input).IsChargeBound c B

/-- Bounded implementation is the unit-charge case. -/
theorem implementsWithin_iff_implementsWithinCharge_one (M : DynComputation.{u} p α β)
    (program : α → FreeM p β) (k : ℕ) :
    M.ImplementsWithin program k ↔ M.ImplementsWithinCharge program (fun _ => 1) k := by
  rw [implementsWithin_iff_implements_and_bound]
  simp only [ImplementsWithinCharge, FreeM.isChargeBound_one_iff_isTotalRollBound]

/-- A machine implementing a program family within budget is within budget from every initial
state. -/
theorem ImplementsWithinCharge.isChargeBound [CanonicallyOrderedAdd ω]
    {M : DynComputation.{u} p α β} {program : α → FreeM p β}
    (h : M.ImplementsWithinCharge program c B) (input : α) : M.IsChargeBound c B (M.init input) :=
  (h.1.isChargeBound_init_iff input).2 (h.2 input)

/-- The machine of a free program is within budget exactly when the program is. -/
theorem isChargeBound_ofFreeM_iff [CanonicallyOrderedAdd ω] (program : α → FreeM p β)
    (input : α) :
    (ofFreeM program).IsChargeBound c B ((ofFreeM program).init input) s ↔
      (program input).IsChargeBound c B s :=
  (implements_ofFreeM program).isChargeBound_init_iff input

/-- Relabelling a machine along a lens keeps it within budget for the pulled-back charge. -/
theorem IsChargeBound.wrap {q : PFunctor.{uA₂, uB₂}} {M : DynComputation.{u} p α β}
    (l : Lens p q) {c : q.A → ω} {state : M.State} (h : M.IsChargeBound (c ∘ l.toFunA) B state s) :
    (M.wrap l).IsChargeBound c B state s :=
  fun k => by rw [unroll_wrap]; exact (h k).mapLens l

/-- Mapping the result of a machine does not change its bound. -/
@[simp]
theorem isChargeBound_mapResult_iff {M : DynComputation.{u} p α β} (f : β → γ) {state : M.State} :
    (M.mapResult f).IsChargeBound c B state s ↔ M.IsChargeBound c B state s := by
  simp only [IsChargeBound, unroll_mapResult, FreeM.isChargeBound_map_iff]

end PFunctor.DynSystem.DynComputation
