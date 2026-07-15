/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Resumption

/-! # Resumption foundation examples -/

@[expose] public section

universe uA uB uβ uX

namespace PFunctor.Resumption

variable {p : PFunctor.{uA, uB}} {β : Type uβ} {X : Type uX}

/-- The computational view is an equivalence even when the polynomial,
return type, and recursive carrier inhabit independent universes. -/
example (step : β ⊕ p.Obj X) :
    viewEquiv (viewEquiv.symm step) = step := by
  simp

example (step : (C.{uβ, uB} β + p).Obj X) :
    viewEquiv.symm (viewEquiv step) = step := by
  simp

/-- Corecursion does not couple the seed universe to either universe of the
polynomial or to the return-value universe. -/
def universeSeparatedCorec (step : X → β ⊕ p.Obj X) (seed : X) :
    Resumption p β :=
  corec step seed

example (step : X → β ⊕ p.Obj X) (seed : X) :
    dest (universeSeparatedCorec step seed) =
      Sum.map (fun value : β => value) (p.map (corec step)) (step seed) := by
  simp [universeSeparatedCorec]

example (computation : Resumption p β) : corec dest computation = computation := by
  simp

end PFunctor.Resumption
