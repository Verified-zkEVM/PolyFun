/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Coalgebra.Category

/-!
# Coalgebras on a shared state type
-/

public section

universe u v

namespace PolyFunTest.Coalgebra

/-- The output type of a structure map can live in an independent universe. -/
example {F : Type u → Type v} {S : Type u} (step : S → F S) : Coalg F S := ⟨step⟩

/-- An identity-functor coalgebra with constant output. -/
@[expose] def constant (b : Bool) : Coalg Id Bool := ⟨fun _ => b⟩

/-- Negation exchanges the two constant coalgebras. -/
@[expose] def negate : Coalg.Hom (constant false) (constant true) := ⟨Bool.not, rfl⟩

example : (Coalg.Hom.endofunctorEquiv _ _ negate).f true = false := by
  rw [Coalg.Hom.endofunctorEquiv_apply]
  rfl

example : (Coalg.Hom.endofunctorEquiv _ _).symm (Coalg.Hom.endofunctorEquiv _ _ negate) =
    negate := Equiv.symm_apply_apply _ _

example (f : Coalg.Hom (constant false) (constant true)) : f.toFun ≠ id := by
  intro h
  have comm := congrFun f.comm true
  simp [constant, h] at comm

end PolyFunTest.Coalgebra
