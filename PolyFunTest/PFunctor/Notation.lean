/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Basic

/-!
# Book-style polynomial notation

Regression tests for the Spivak–Niu surface syntax on `PFunctor`: the
monomial infix `A y^ B`, the representable prefix `y^ B`, the composition
power `p ◃^ n`, and the indexed sum/product binders `Σₚ`/`Πₚ`. The examples
pin down definitional equality with the named primitives and the intended
grouping against `◃`, `+`, and `*`.
-/

@[expose] public section

namespace PFunctor

section Monomial

/-- The monomial infix elaborates to the `monomial` primitive. -/
example : (Bool y^ Nat) = monomial Bool Nat := rfl

/-- The representable prefix elaborates to the `purePower` primitive. -/
example : (y^ Nat) = purePower Nat := rfl

/-- Compound arguments parenthesize on either side of the infix. -/
example : ((Bool × Bool) y^ (Fin 2)) = monomial (Bool × Bool) (Fin 2) := rfl

/-- The monomial infix binds tighter than composition. -/
example : (Bool y^ Nat ◃ Nat y^ Bool) = ((Bool y^ Nat) ◃ (Nat y^ Bool)) := rfl

/-- The representable prefix can sit under composition without parentheses. -/
example : (Bool y^ Nat ◃ y^ Bool) = ((Bool y^ Nat) ◃ (y^ Bool)) := rfl

/-- The monomial infix binds tighter than sum and product. -/
example : (Bool y^ Nat + C Bool * Bool y^ Bool)
    = ((Bool y^ Nat) + ((C Bool) * (Bool y^ Bool))) := rfl

/-- The special monomials unfold to the shared `y`-spelling. -/
example : (C Bool : PFunctor.{0, 0}) = Bool y^ PEmpty := rfl
example : (linear Bool : PFunctor.{0, 0}) = Bool y^ PUnit := rfl
example : (y : PFunctor.{0, 0}) = PUnit y^ PUnit := rfl

end Monomial

section CompPower

variable {p q : PFunctor.{0, 0}}

/-- The composition power unfolds to iterated composition ending in `y`. -/
example : (p ◃^ 2) = p ◃ (p ◃ y) := rfl

/-- The composition power binds tighter than composition itself. -/
example : (p ◃^ 2 ◃ q) = ((p ◃^ 2) ◃ q) := rfl

/-- The composition power is `compNth`, not iterated product. -/
example : (p ◃^ 3) = compNth p 3 := rfl

end CompPower

section Binders

/-- The `Σₚ` binder elaborates to `PFunctor.sigma`. -/
example : (Σₚ _i : Bool, Nat y^ (Fin 2))
    = sigma (fun _ : Bool => Nat y^ (Fin 2)) := rfl

/-- The `Πₚ` binder elaborates to `PFunctor.pi`. -/
example : (Πₚ _i : Bool, Nat y^ (Fin 2))
    = pi (fun _ : Bool => Nat y^ (Fin 2)) := rfl

end Binders

section Units

/-- `y` is definitionally both the tensor unit and the composition unit. -/
example : (tensorUnit : PFunctor.{0, 0}) = y := rfl
example : (compUnit : PFunctor.{0, 0}) = y := rfl

end Units

end PFunctor
