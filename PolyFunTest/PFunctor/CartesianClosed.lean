/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.CartesianClosed

/-!
# Examples for the cartesian-closed structure of `Poly`

Regression tests exercising the cartesian exponential `exp` together with `eval`,
`curry`/`uncurry`, the forward round-trip `uncurry_curry`, and the position-level
reverse round-trip `curry_uncurry_toFunA`, the full reverse round-trip
`curry_uncurry`, and `curryEquiv`, both abstractly and on concrete small polynomials.
-/

@[expose] public section

universe u

namespace PFunctor

open CartesianClosed

variable {p q r : PFunctor.{u, u}}

/-- The evaluation / counit lens typechecks (Spivak–Niu Example 5.32). -/
example : Lens (exp r q * q) r := eval

/-- `curry` transposes a lens `p * q ⇆ r` into `p ⇆ exp r q` (Theorem 5.31). -/
example (l : Lens (p * q) r) : Lens p (exp r q) := curry l

/-- `uncurry` transposes back. -/
example (g : Lens p (exp r q)) : Lens (p * q) r := uncurry g

/-- `uncurry` is definitionally evaluation pre-composed with `g ×ₗ id`. -/
example (g : Lens p (exp r q)) : uncurry g = eval ∘ₗ (g ×ₗ Lens.id q) := rfl

/-- Forward round-trip of the transpose bijection: `uncurry ∘ curry = id`. -/
example (l : Lens (p * q) r) : uncurry (curry l) = l := uncurry_curry l

/-- Position-level reverse round-trip: `curry (uncurry g)` and `g` agree on
positions. -/
example (g : Lens p (exp r q)) : (curry (uncurry g)).toFunA = g.toFunA :=
  curry_uncurry_toFunA g

/-- Reverse round-trip of the transpose bijection: `curry ∘ uncurry = id`. -/
example (g : Lens p (exp r q)) : curry (uncurry g) = g := curry_uncurry g

/-- Currying and uncurrying package as an equivalence of lens types. -/
example : Lens (p * q) r ≃ Lens p (exp r q) := curryEquiv

example (l : Lens (p * q) r) : curryEquiv l = curry l := rfl

example (g : Lens p (exp r q)) : curryEquiv.symm g = uncurry g := rfl

/-! ## Concrete small polynomials -/

/-- `eval` typechecks on concrete monomials, e.g. `exp (C Bool) (Bool y^ Bool)`. -/
example :
    Lens (exp (C.{0, 0} Bool) (Bool y^ Bool : PFunctor.{0, 0}) *
      (Bool y^ Bool : PFunctor.{0, 0})) (C.{0, 0} Bool) :=
  eval

/-- The exponential of the identity `y` by `y` supports evaluation. -/
example : Lens (exp y.{0, 0} y.{0, 0} * y.{0, 0}) y.{0, 0} := eval

/-- Currying a concrete handler `y * y ⇆ y` lands in `y ⇆ exp y y`. -/
example (l : Lens (y.{0, 0} * y.{0, 0}) y.{0, 0}) : Lens y.{0, 0} (exp y.{0, 0} y.{0, 0}) :=
  curry l

/-- Forward round-trip on a concrete lens. -/
example (l : Lens (y.{0, 0} * y.{0, 0}) y.{0, 0}) : uncurry (curry l) = l :=
  uncurry_curry l

/-- Reverse round-trip on a concrete lens. -/
example (g : Lens y.{0, 0} (exp y.{0, 0} y.{0, 0})) : curry (uncurry g) = g :=
  curry_uncurry g

end PFunctor
