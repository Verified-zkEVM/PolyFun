/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Multiples as a monotone additive map

`OrderAddMonoidHom.multiples a ha` is `n ↦ n • a` from `ℕ`, as a monotone additive map, for an
element `a` with `0 ≤ a` of an ordered additive monoid. It is the ordered form of Mathlib's
`multiplesHom`, and scales a call count by a price: a natural-number bound pushes forward along it
to a bound in any cost type. It belongs beside `multiplesHom`.
-/

public section

universe u

namespace OrderAddMonoidHom

variable {ω : Type u} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]

/-- `n ↦ n • a`, as a monotone additive map from `ℕ`. -/
@[expose] def multiples (a : ω) (ha : 0 ≤ a) : ℕ →+o ω where
  toFun n := n • a
  map_zero' := zero_nsmul a
  map_add' m n := add_nsmul a m n
  monotone' _ _ h := nsmul_le_nsmul_left ha h

@[simp]
theorem multiples_apply (a : ω) (ha : 0 ≤ a) (n : ℕ) : multiples a ha n = n • a :=
  rfl

end OrderAddMonoidHom
