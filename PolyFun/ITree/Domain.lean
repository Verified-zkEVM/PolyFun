/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.ResumptionWithTau
public import PolyFun.ITree.Bisim.Equiv
public import PolyFun.PFunctor.Resumption.Domain

/-!
# Continuous interpretations insensitive to silent steps

Visible queries use an arbitrary continuous algebra; silent steps use the
identity algebra. Least fixed points interpret unbounded executions. Weak
bisimulation preserves this interpretation, including silent divergence.
-/

public section

open OmegaCompletePartialOrder
open PFunctor.Resumption (ContinuousAlgebra)

namespace ITree

universe uA uB uα uD uS

variable {P : PFunctor.{uA, uB}} {α : Type uα} {D : Type uD}
  [OmegaCompletePartialOrder D] [OrderBot D]

/-- Interpret the explicit silent event by its single continuation. -/
@[expose] def ContinuousAlgebra.withTau (alg : ContinuousAlgebra P D) :
    ContinuousAlgebra (P + PFunctor.y.{uA, uB}) D
  | .inl a => alg a
  | .inr _ => .ofFun (fun next => next PUnit.unit)

/-- One unfolding of continuous ITree interpretation. -/
@[expose] def domainStep (ret : α → D) (alg : ContinuousAlgebra P D) :
    (ITree P α → D) →𝒄 (ITree P α → D) :=
  .ofFun (fun meaning tree => match shape' tree with
    | .mk (.pure value) _ => ret value
    | .mk .step next => meaning (next PUnit.unit)
    | .mk (.query operation) next => alg operation (fun answer => meaning (next answer))) (by
      apply ωScottContinuous.of_apply₂
      intro tree
      rcases shape' tree with ⟨head, next⟩
      cases head with
      | pure value => exact ωScottContinuous.const
      | step => exact ωScottContinuous.apply _
      | query a =>
          exact (alg a).ωScottContinuous.comp
            (ωScottContinuous.of_apply₂ fun b => ωScottContinuous.apply (next b)))

/-- The least solution of the ITree interpretation equations. -/
@[expose] def denote (ret : α → D) (alg : ContinuousAlgebra P D) : ITree P α → D :=
  fun tree => PFunctor.Resumption.denote ret (ContinuousAlgebra.withTau alg)
    (toResumptionWithTau tree)

/-- The canonical resumption interpretation is the least solution of the ITree equations. -/
theorem denote_eq_fix (ret : α → D) (alg : ContinuousAlgebra P D) :
    denote ret alg = (domainStep ret alg).fix := by
  let pre : (PFunctor.Resumption (P + PFunctor.y) α → D) →𝒄 (ITree P α → D) :=
    .ofFun (fun f t => f (toResumptionWithTau t))
  have comm (f : PFunctor.Resumption (P + PFunctor.y) α → D) :
      pre (PFunctor.Resumption.domainStep ret (ContinuousAlgebra.withTau alg) f) =
        domainStep ret alg (pre f) := by
    funext t
    simp only [pre, ContinuousHom.ofFun_apply, PFunctor.Resumption.domainStep,
      dest_toResumptionWithTau, domainStep]
    rcases shape' t with ⟨head, next⟩
    cases head <;> rfl
  funext tree
  exact congrFun ((PFunctor.Resumption.domainStep ret (ContinuousAlgebra.withTau alg)).fix_fusion
    (domainStep ret alg) pre rfl comm) tree


/-- Bound denotation by bounding every finite semantic approximation. -/
theorem denote_le_of_approximants_le (ret : α → D) (alg : ContinuousAlgebra P D)
    (tree : ITree P α) (bound : D)
    (h : ∀ n, (domainStep ret alg).approximants n tree ≤ bound) :
    denote ret alg tree ≤ bound := by
  rw [denote_eq_fix]
  apply ωSup_le
  intro n
  simpa only [Chain.coe_map, Function.comp_apply, Pi.evalOrderHom, OrderHom.coe_mk,
    Function.eval] using h n

/-- The denotation satisfies the one-step interpretation equations. -/
theorem denote_eq (ret : α → D) (alg : ContinuousAlgebra P D) (tree : ITree P α) :
    denote ret alg tree = match shape' tree with
      | .mk (.pure value) _ => ret value
      | .mk .step next => denote ret alg (next PUnit.unit)
      | .mk (.query operation) next => alg operation (fun b => denote ret alg (next b)) := by
  simp only [denote_eq_fix]
  exact (congrFun (domainStep ret alg).map_fix tree).symm

@[simp] theorem denote_pure (ret : α → D) (alg : ContinuousAlgebra P D) (value : α) :
    denote ret alg (pure value) = ret value := by rw [denote_eq, shape'_pure]

@[simp] theorem denote_step (ret : α → D) (alg : ContinuousAlgebra P D) (tree : ITree P α) :
    denote ret alg (step tree) = denote ret alg tree := by rw [denote_eq, shape'_step]

@[simp] theorem denote_query (ret : α → D) (alg : ContinuousAlgebra P D) (a : P.A)
    (next : P.B a → ITree P α) : denote ret alg (query a next) =
      alg a (fun b => denote ret alg (next b)) := by rw [denote_eq, shape'_query]

/-- The exact resumption representation commutes with interpretation. -/
@[simp] theorem denote_toResumptionWithTau (ret : α → D) (alg : ContinuousAlgebra P D)
    (tree : ITree P α) :
    PFunctor.Resumption.denote ret (ContinuousAlgebra.withTau alg) (toResumptionWithTau tree) =
      denote ret alg tree := rfl

/-- Unfold a coalgebra using the meanings of its successor states. -/
@[expose] def corecDomainStep {S : Type uS} (next : S → (ViewPoly P α).Obj S)
    (ret : α → D) (alg : ContinuousAlgebra P D) : (S → D) →𝒄 (S → D) :=
  .ofFun (fun meaning state => match next state with
    | .mk (.pure value) _ => ret value
    | .mk .step children => meaning (children PUnit.unit)
    | .mk (.query a) children => alg a (fun b => meaning (children b))) (by
      apply ωScottContinuous.of_apply₂
      intro state
      rcases next state with ⟨head, children⟩
      cases head with
      | pure _ => exact ωScottContinuous.const
      | step => exact ωScottContinuous.apply _
      | query a =>
          exact (alg a).ωScottContinuous.comp
            (ωScottContinuous.of_apply₂ fun b => ωScottContinuous.apply (children b)))

/-- Interpreting a corecursive tree agrees with solving its state equations. -/
theorem denote_corec {S : Type uS} (next : S → (ViewPoly P α).Obj S)
    (ret : α → D) (alg : ContinuousAlgebra P D) (state : S) :
    denote ret alg (corec next state) = (corecDomainStep next ret alg).fix state := by
  let pre : (ITree P α → D) →𝒄 (S → D) := .ofFun (fun f s => f (corec next s))
  have comm (f : ITree P α → D) :
      pre (domainStep ret alg f) = corecDomainStep next ret alg (pre f) := by
    funext s
    simp only [pre, domainStep, ContinuousHom.ofFun_apply, shape'_corec_apply, corecDomainStep]
    rcases next s with ⟨head, children⟩
    cases head <;> rfl
  rw [denote_eq_fix]
  exact congrFun ((domainStep ret alg).fix_fusion
    (corecDomainStep next ret alg) pre rfl comm) state

/-- Finite silent stripping preserves denotation. -/
theorem TauSteps.denote_eq (ret : α → D) (alg : ContinuousAlgebra P D)
    {t s : ITree P α} (h : TauSteps t s) : denote ret alg t = denote ret alg s := by
  induction h with
  | refl _ => rfl
  | step next ht _ ih => rw [ITree.denote_eq, ht]; exact ih

/-- An approximation improves when leading silent steps are removed. -/
theorem TauSteps.approximants_le (ret : α → D) (alg : ContinuousAlgebra P D)
    {t s : ITree P α} (h : TauSteps t s) (n : Nat) :
    (domainStep ret alg).approximants n t ≤ (domainStep ret alg).approximants n s := by
  induction h with
  | refl _ => rfl
  | @step t t' next ht _ ih =>
      cases n with
      | zero => exact bot_le
      | succ n =>
          have hs : (domainStep ret alg).approximants (n + 1) t =
              (domainStep ret alg).approximants n (next PUnit.unit) := by
            rw [ContinuousHom.approximants_succ]
            change (match shape' t with
              | .mk (.pure v) _ => ret v
              | .mk .step k => (domainStep ret alg).approximants n (k PUnit.unit)
              | .mk (.query a) k => alg a
                  (fun b => (domainStep ret alg).approximants n (k b))) = _
            rw [ht]
          rw [hs]
          exact le_trans ((domainStep ret alg).approximants.monotone (Nat.le_succ n) _) ih

/-- Every finite semantic approximation is bounded by any weakly bisimilar tree. -/
theorem WeakBisim.approximants_le_denote (ret : α → D) (alg : ContinuousAlgebra P D)
    {t s : ITree P α} (h : WeakBisim t s) (n : Nat) :
    (domainStep ret alg).approximants n t ≤ denote ret alg s := by
  induction n generalizing t s with
  | zero => exact bot_le
  | succ n ih =>
      obtain ⟨t', s', ht, hs, hm⟩ := h.dest
      apply le_trans (ht.approximants_le ret alg (n + 1))
      rw [hs.denote_eq ret alg]
      rw [ContinuousHom.approximants_succ]
      cases hm with
      | pure r ht hs => simp [domainStep, ht, ITree.denote_eq, hs]
      | query a c c' ht hs hcc =>
          change (match shape' t' with
            | .mk (.pure v) _ => ret v
            | .mk .step k => (domainStep ret alg).approximants n (k PUnit.unit)
            | .mk (.query a) k => alg a
                (fun b => (domainStep ret alg).approximants n (k b))) ≤ _
          rw [ht, ITree.denote_eq, hs]
          exact (alg a).monotone (fun b => ih (hcc b))
      | tau c c' ht hs hcc =>
          change (domainStep ret alg ((domainStep ret alg).approximants n)) t' ≤ _
          simp only [domainStep, ContinuousHom.ofFun_apply, ht]
          rw [ITree.denote_eq, hs]
          exact ih hcc

/-- Weak bisimulation preserves every continuous-algebra denotation. -/
theorem WeakBisim.denote_eq (ret : α → D) (alg : ContinuousAlgebra P D)
    {t s : ITree P α} (h : WeakBisim t s) : denote ret alg t = denote ret alg s := by
  exact le_antisymm
    (denote_le_of_approximants_le ret alg t _ (h.approximants_le_denote ret alg))
    (denote_le_of_approximants_le ret alg s _ (h.symm.approximants_le_denote ret alg))

end ITree
