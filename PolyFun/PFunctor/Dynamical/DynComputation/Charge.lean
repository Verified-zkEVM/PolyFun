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
(`isChargeBound_iff_behavior`), agrees with the `FreeM` bound on `ofFreeM`
(`isChargeBound_ofFreeM_iff`), relabels along lenses (`IsChargeBound.wrap`), and ignores the result
type (`isChargeBound_mapResult_iff`).
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

/-- The machine of a free program is within budget exactly when the program is. -/
theorem isChargeBound_ofFreeM_iff [CanonicallyOrderedAdd ω] (program : α → FreeM p β)
    (input : α) :
    (ofFreeM program).IsChargeBound c B ((ofFreeM program).init input) s ↔
      (program input).IsChargeBound c B s := by
  rw [isChargeBound_init_iff_denote, denote_ofFreeM, Resumption.isChargeBound_toResumption_iff]

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
