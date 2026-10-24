/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Category.MonoEpi

/-!
# Monomorphisms and epimorphisms of lenses

Regression checks for `LensCat.mono_iff`, `LensCat.epi_iff` and the cartesian routes. The
epimorphism `coord` has no injective direction map, only an injective joint fibre map, so it
separates the book's joint condition from a fibrewise one. The Mathlib-derived consumers are
`cancel_mono`, `cancel_epi` and `isIso_of_mono_of_epi` through `Balanced LensCat`.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.Category.MonoEpi

open CategoryTheory _root_.PFunctor

/-- Two positions, each with Boolean directions. -/
abbrev twoBool : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩

/-- One position whose directions are pairs of Booleans. -/
abbrev pairs : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool × Bool⟩

/-- Both positions go to the single position; each reads one coordinate of the pair. -/
def coord : LensCat.of twoBool ⟶ LensCat.of pairs :=
  (fun _ => PUnit.unit) ⇆ fun i p => if i then p.1 else p.2

/-- `coord` is an epimorphism: the two coordinates jointly determine the pair. -/
instance : Epi coord :=
  (LensCat.epi_iff coord).2 ⟨fun _ => ⟨true, rfl⟩, fun _ d d' h =>
    Prod.ext (by simpa [coord, Lens.fiberJoint] using congrFun h ⟨true, rfl⟩)
      (by simpa [coord, Lens.fiberJoint] using congrFun h ⟨false, rfl⟩)⟩

/-- No single direction map of `coord` is injective. -/
example : ¬ Function.Injective (Lens.toFunB coord true) := fun h =>
  absurd (h (a₁ := (true, true)) (a₂ := (true, false)) rfl) (by decide)

/-- `coord` identifies two positions, so it is not a monomorphism. -/
example : ¬ Mono coord := fun h =>
  Bool.noConfusion (((LensCat.mono_iff coord).1 h).1 (a₁ := true) (a₂ := false) rfl)

/-- Epimorphisms cancel on the left. -/
example {Z : LensCat.{0, 0}} (g h : LensCat.of pairs ⟶ Z) (H : coord ≫ g = coord ≫ h) :
    g = h :=
  (cancel_epi coord).1 H

/-- Negating the positions and keeping the directions. -/
def negate : LensCat.of twoBool ⟶ LensCat.of twoBool :=
  (fun b => !b) ⇆ fun _ d => d

instance : Mono negate :=
  (LensCat.mono_iff negate).2 ⟨fun a b h => by simpa [negate] using h, fun _ d => ⟨d, rfl⟩⟩

instance : Epi negate :=
  (LensCat.epi_iff negate).2 ⟨fun b => ⟨!b, by simp [negate]⟩, fun b d d' h => by
    simpa [negate, Lens.fiberJoint] using congrFun h ⟨!b, by simp [negate]⟩⟩

/-- `LensCat` is balanced. -/
example : IsIso negate := isIso_of_mono_of_epi negate

/-- Monomorphisms cancel on the right. -/
example {Z : LensCat.{0, 0}} (g h : Z ⟶ LensCat.of twoBool) (H : g ≫ negate = h ≫ negate) :
    g = h :=
  (cancel_mono negate).1 H

/-- A cartesian lens with injective positions, such as a coproduct injection, is a
monomorphism. -/
example {P Q : PFunctor.{0, 0}} :
    Mono (show LensCat.of P ⟶ LensCat.of (P + Q) from Lens.inl) :=
  (LensCat.mono_iff_injective_of_isCartesian _ Lens.IsCartesian.inl).2 Sum.inl_injective

/-! ### Cartesian routes -/

/-- Route the left position to the left summand and the right position to the right summand,
swapping the directions on the right. -/
def route : (a : twoBool.A) →
    (Σ b : twoBool.A, twoBool.B b ≃ twoBool.B a) ⊕ (Σ c : twoBool.A, twoBool.B c ≃ twoBool.B a)
  | true => .inl ⟨true, Equiv.refl _⟩
  | false => .inr ⟨false, ⟨(! ·), (! ·), Bool.not_not, Bool.not_not⟩⟩

/-- The routed lens is computed by `ofDirectionEquiv`. -/
example : (Lens.cartesianSumEquiv.symm route).1.toFunA false = Sum.inr false := rfl

example : (Lens.cartesianSumEquiv.symm route).1.toFunB false true = false := rfl

/-- Routing a cartesian lens recovers it. -/
example : Lens.cartesianSumEquiv (Lens.cartesianSumEquiv.symm route) = route :=
  Lens.cartesianSumEquiv.apply_symm_apply route

end PolyFunTest.PFunctor.Category.MonoEpi
