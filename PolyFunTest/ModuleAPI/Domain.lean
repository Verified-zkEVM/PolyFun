/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.ITree.Domain
import PolyFun.PFunctor.Resumption.DomainTruncate
import PolyFun.Control.Domain.Result

/-!
# Public continuous-domain API canaries

Ordinary imports expose fixed-point equations, finite-fold approximation, and
weak-bisimulation invariance. A visible algebra may supply information without
demanding a continuation; continuous interpretation must retain it.
-/

public section

open OmegaCompletePartialOrder

universe uA uB uα uD

example {P : PFunctor.{uA, uB}} {α : Type uα} {D : Type uD}
    [OmegaCompletePartialOrder D] [OrderBot D]
    (ret : α → D) (alg : PFunctor.Resumption.ContinuousAlgebra P D) :
    PFunctor.Resumption.denote ret alg =
      ωSup (PFunctor.Resumption.truncationChain ret alg) :=
  PFunctor.Resumption.denote_eq_sup_truncations ret alg

example {P : PFunctor.{uA, uB}} {α : Type uα} {D : Type uD}
    [OmegaCompletePartialOrder D] [OrderBot D]
    (ret : α → D) (alg : PFunctor.Resumption.ContinuousAlgebra P D)
    {t s : ITree P α} (h : ITree.WeakBisim t s) :
    ITree.denote ret alg t = ITree.denote ret alg s := h.denote_eq ret alg

example {P : PFunctor} {α : Type} (ret : α → DomainResult Unit (DiscreteOrder Nat))
    (a : P.A) (next : P.B a → PFunctor.Resumption P α) :
    PFunctor.Resumption.denote ret (fun _ => .const (.value ⟨7⟩))
      (.query a next) = .value ⟨7⟩ := by
  rw [PFunctor.Resumption.denote_query]
  rfl

example {D : Type uD} [OmegaCompletePartialOrder D] [OrderBot D]
    (f : D →𝒄 D) : f f.fix = f.fix := f.map_fix
