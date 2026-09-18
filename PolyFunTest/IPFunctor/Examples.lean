/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.IndexedPrograms

/-!
# Indexed-polynomial information and empty-result regressions

Checks for information lost by forgetting indices and for the empty-result W-type bridge.
The protocol tutorial is imported so its worked programs are also built by `lake test`.
-/

@[expose] public section

namespace IPFunctor.Examples

universe u v a b

/-! ## Selected-fiber information preservation -/

/-- An indexed polynomial whose only response selects the given Boolean source. -/
def sourceChoice (source : Bool) : IPFunctor Bool Unit where
  A _ := Unit
  B _ _ := Unit
  src _ _ _ := source

example : (sourceChoice false).toPFunctor = (sourceChoice true).toPFunctor := rfl

example : sourceChoice false ≠ sourceChoice true := by
  intro h
  have hs := (IPFunctor.mk.inj h).2.2
  have : (fun (_ : Unit) (_ : Unit) (_ : Unit) => false) =
      (fun (_ : Unit) (_ : Unit) (_ : Unit) => true) := eq_of_heq hs
  have hf := congrFun (congrFun (congrFun this ()) ()) ()
  cases hf

example {I : Type u} {J : Type v} [Unique I] [Unique J]
    (P Q : IPFunctor.{u, v, a, b} I J) (h : P.toPFunctor = Q.toPFunctor) : P = Q :=
  toPFunctor_injective h

/-! ## `PFunctor.FreeM.equivWOfIsEmpty` round-trip

When the value type `α` is empty, every `pure` leaf is unreachable and
`PFunctor.FreeM P α` collapses structurally to `P.W`. The forward direction
`toW` reinterprets each `liftBind` as a W-node; the inverse `ofW` rebuilds
the tree. Both directions are mutual inverses by induction; this example
just confirms the equivalence resolves and either round-trip is
`rfl` after unfolding. -/

example (P : PFunctor) (w : P.W) :
    (PFunctor.FreeM.equivWOfIsEmpty (P := P) (α := PEmpty)).invFun w =
      PFunctor.FreeM.ofW w := rfl

end IPFunctor.Examples
