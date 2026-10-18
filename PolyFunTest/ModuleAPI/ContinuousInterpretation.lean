/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.DomainLaws
public import PolyFun.ITree.Interp.Stateful
public import PolyFun.PFunctor.Resumption.DomainTruncate

/-!
# Continuous interpretations through ordinary imports

The exact explicit-tau encoding preserves substitution. Domain interpretations
then share substitution and fusion laws with resumptions. A constant query algebra
can reveal information without demanding any continuation, including at infinite depth.
-/

public section

open OmegaCompletePartialOrder PFunctor

universe uA uB uα uβ uD

namespace PolyFunTest.ModuleAPI.ContinuousInterpretation

variable {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
  {D : Type uD} [OmegaCompletePartialOrder D] [OrderBot D]

example (tree : ITree P α) (next : α → ITree P β) :
    ITree.toResumptionWithTau (ITree.bind tree next) =
      Resumption.bind (ITree.toResumptionWithTau tree)
        (fun value => ITree.toResumptionWithTau (next value)) :=
  ITree.toResumptionWithTau_bind tree next

example (ret : β → D) (alg : Resumption.ContinuousAlgebra P D)
    (tree : ITree P α) (next : α → ITree P β) :
    ITree.denote ret alg (ITree.bind tree next) =
      ITree.denote (fun value => ITree.denote ret alg (next value)) alg tree :=
  ITree.denote_bind ret alg tree next

example (ret : α → D) (alg : Resumption.ContinuousAlgebra P D) :
    Resumption.denote ret alg = ωSup (Resumption.truncationChain ret alg) :=
  Resumption.denote_eq_sup_truncations ret alg

example (ret : α → D) (alg : Resumption.ContinuousAlgebra P D)
    {left right : ITree P α} (h : ITree.WeakBisim left right) :
    ITree.denote ret alg left = ITree.denote ret alg right := h.denote_eq ret alg

example (ret : α → D) (alg : Resumption.ContinuousAlgebra P D) :
    ITree.denote ret alg (ITree.diverge : ITree P α) = ⊥ := ITree.denote_diverge ret alg

/-- Visible information need not wait for a return or for a child to produce information. -/
example (a : P.A) (next : P.B a → Resumption P α) :
    Resumption.denote (fun _ => False) (fun _ => .const True) (.query a next) = True := by
  rw [Resumption.denote_query]
  rfl

/-- Loop state and return values can inhabit different universes. -/
example (ret : α → D) (alg : Resumption.ContinuousAlgebra P D)
    (body : ULift.{uβ} ℕ → ITree P (ULift.{uβ} ℕ ⊕ α)) (bound : ULift.{uβ} ℕ → D)
    (hbody : ∀ state, ITree.denote (Sum.elim bound ret) alg (body state) ≤ bound state)
    (state : ULift.{uβ} ℕ) : ITree.denote ret alg (ITree.iter body state) ≤ bound state :=
  ITree.denote_iter_le ret alg body bound hbody state

/-- A loop which always continues silently has bottom denotation. -/
example (ret : α → D) (alg : Resumption.ContinuousAlgebra P D) (state : ℕ) :
    ITree.denote ret alg (ITree.iter (fun n : ℕ => ITree.pure (.inl (n + 1))) state) = ⊥ := by
  apply le_antisymm _ bot_le
  apply ITree.denote_iter_le ret alg _ (fun _ => ⊥) _ state
  intro n
  simp

/-- Exact stateful equations do not require a lawful equality monad and allow
larger target-operation and target-answer universes. -/
example {E : PFunctor.{0, 0}} {F : PFunctor.{uA, uB}} {S R : Type}
    (handler : PFunctor.Handler (StateT S (ITree F)) E)
    (a : E.A) (next : E.B a → ITree E R) (s : S) :
    (ITree.interp handler (ITree.query a next)).run s =
      (handler a s >>= fun out => ITree.step ((ITree.interp handler (next out.1)).run out.2)) :=
  ITree.interp_run_query handler a next s

/-- Inserting a silent guard preserves weak behavior. -/
example (value : α) :
    ITree.WeakBisim (ITree.step (ITree.pure (F := P) value)) (ITree.pure value) :=
  ITree.WeakBisim.weakBisim_of_tauSteps
    (ITree.TauSteps.step _ (ITree.shape'_step _) (ITree.TauSteps.refl _))

/-- The same weakly equivalent trees disagree at zero fuel when the clock counts silent steps. -/
example (value : α) :
    Resumption.truncate 0 (ITree.toResumptionWithTau (ITree.step (ITree.pure (F := P) value))) ≠
      Resumption.truncate 0 (ITree.toResumptionWithTau (ITree.pure (F := P) value)) := by
  simp [ITree.toResumptionWithTau_step, ITree.toResumptionWithTau_pure]

end PolyFunTest.ModuleAPI.ContinuousInterpretation
