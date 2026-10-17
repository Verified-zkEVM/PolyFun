/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.DomainLaws
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

end PolyFunTest.ModuleAPI.ContinuousInterpretation
