/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Domain
public import PolyFun.PFunctor.Resumption.DomainLaws

/-!
# Continuous interpretations of embedding, sequencing and iteration

The tau-free resumption embedding commutes with continuous interpretation.
Sequencing substitutes the meanings of continuation trees at return leaves.
Iteration is the least solution of its body equations, including silent divergence.
-/

public section

open OmegaCompletePartialOrder
open PFunctor.Resumption (ContinuousAlgebra)

namespace ITree

universe uA uB uα uβ uD uE uS

variable {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
  {D : Type uD} {E : Type uE} [OmegaCompletePartialOrder D] [OrderBot D]
  [OmegaCompletePartialOrder E] [OrderBot E]

/-- The canonical resumption embedding commutes with continuous interpretation. -/
theorem denote_toITree (ret : α → D) (alg : ContinuousAlgebra P D)
    (tree : PFunctor.Resumption P α) :
    denote ret alg tree.toITree = PFunctor.Resumption.denote ret alg tree := by
  let pre : (ITree P α → D) →𝒄 (PFunctor.Resumption P α → D) :=
    .ofFun (fun f t => f t.toITree)
  have comm (f : ITree P α → D) :
      pre (domainStep ret alg f) = PFunctor.Resumption.domainStep ret alg (pre f) := by
    funext t
    simp only [pre, ContinuousHom.ofFun_apply, domainStep,
      PFunctor.Resumption.domainStep, PFunctor.Resumption.shape'_toITree]
    cases PFunctor.Resumption.dest t <;> rfl
  rw [denote_eq_fix]
  exact congrFun ((domainStep ret alg).fix_fusion
    (PFunctor.Resumption.domainStep ret alg) pre rfl comm) tree

/-- A strict continuous algebra morphism commutes with interpretation, including silent steps. -/
theorem denote_fusion (ret : α → D) (alg : ContinuousAlgebra P D)
    (target : ContinuousAlgebra P E) (f : D →𝒄 E) (hbot : f ⊥ = ⊥)
    (halg : ∀ a k, f (alg a k) = target a (fun b => f (k b))) (tree : ITree P α) :
    f (denote ret alg tree) = denote (fun a => f (ret a)) target tree := by
  rw [← denote_toResumptionWithTau, ← denote_toResumptionWithTau]
  apply PFunctor.Resumption.denote_fusion _ _ _ f hbot
  intro a k
  cases a with
  | inl a => exact halg a k
  | inr tick => rfl

/-- Leastness of continuous interpretation against a prefixed interpretation. -/
theorem denote_le (ret : α → D) (alg : ContinuousAlgebra P D)
    (meaning : ITree P α → D) (h : domainStep ret alg meaning ≤ meaning) :
    denote ret alg ≤ meaning := by
  rw [denote_eq_fix]
  exact (domainStep ret alg).fix_le h

/-- Substitution changes only the interpretation of return leaves. -/
theorem denote_bind (ret : β → D) (alg : ContinuousAlgebra P D)
    (tree : ITree P α) (next : α → ITree P β) :
    denote ret alg (bind tree next) = denote (fun a => denote ret alg (next a)) alg tree := by
  simp only [denote, toResumptionWithTau_bind, PFunctor.Resumption.denote_bind]

/-- Silent divergence has the least denotation, independently of the visible algebra. -/
@[simp] theorem denote_diverge (ret : α → D) (alg : ContinuousAlgebra P D) :
    denote ret alg (diverge : ITree P α) = ⊥ := by
  apply le_antisymm _ bot_le
  apply denote_le_of_approximants_le
  intro n
  have h : (domainStep ret alg).approximants n (diverge : ITree P α) = ⊥ := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [ContinuousHom.approximants_succ]
        simpa only [domainStep, ContinuousHom.ofFun_apply, shape'_diverge] using ih
  exact h.le

variable {S : Type uS}

/-- Iteration interprets a continuation result by another iteration and a return
result by the return algebra. Silent guards have no denotational cost. -/
theorem denote_iter_eq (ret : α → D) (alg : ContinuousAlgebra P D)
    (body : S → ITree P (S ⊕ α)) (state : S) :
    denote ret alg (iter body state) =
      denote (Sum.elim (fun s => denote ret alg (iter body s)) ret) alg (body state) := by
  rw [iter_unfold, denote_bind]
  congr 1
  funext result
  cases result <;> simp

/-- Any family preserved as an upper bound by the loop body bounds the whole
iteration. The rule needs neither termination nor a bound on the number of iterations. -/
theorem denote_iter_le (ret : α → D) (alg : ContinuousAlgebra P D)
    (body : S → ITree P (S ⊕ α)) (bound : S → D)
    (h : ∀ state, denote (Sum.elim bound ret) alg (body state) ≤ bound state)
    (state : S) : denote ret alg (iter body state) ≤ bound state := by
  change denote ret alg (corec (iterStep body) (body state)) ≤ _
  rw [denote_corec]
  apply le_trans ((corecDomainStep (iterStep body) ret alg).fix_le
    (x := denote (Sum.elim bound ret) alg) ?_ (body state)) (h state)
  intro tree
  rw [denote_eq]
  simp only [corecDomainStep, ContinuousHom.ofFun_apply, iterStep]
  rcases shape' tree with ⟨head, children⟩
  cases head with
  | pure result => cases result with
    | inl state => exact h state
    | inr value => exact le_rfl
  | step => exact le_rfl
  | query a => exact le_rfl

/-- A continuous interpretation of the loop body gives exactly its least fixed
point. The supplied body equation makes continuity an explicit reusable obligation. -/
theorem denote_iter_eq_fix (ret : α → D) (alg : ContinuousAlgebra P D)
    (body : S → ITree P (S ⊕ α)) (step : (S → D) →𝒄 (S → D))
    (hstep : ∀ meaning s, step meaning s = denote (Sum.elim meaning ret) alg (body s)) :
    (fun s => denote ret alg (iter body s)) = step.fix := by
  apply le_antisymm
  · intro s
    apply denote_iter_le ret alg body step.fix _ s
    intro s
    rw [← hstep, step.map_fix]
  · apply step.fix_le
    intro s
    rw [hstep, ← denote_iter_eq]

end ITree
