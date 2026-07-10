/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.InternalHom

/-!
# Examples for the ⊗-internal hom

Regression tests exercising `ihom`, `eval`, `curry`/`uncurry`, and the two
special cases `[y, r] ≅ r` and `(ihom q X).A = Lens q X`.
-/

@[expose] public section

universe u

namespace PFunctor

variable {p q r : PFunctor.{u, u}}

/-- Positions of `[q, y]` are exactly the handlers `q ⇆ y`. -/
example : (ihom q X.{u, u}).A = Lens q X.{u, u} := ihom_X_A q

/-- The tensor-unit law `[y, r] ≅ r` is realised as a lens equivalence. -/
example : Nonempty (ihom X.{u, u} r ≃ₗ r) := ⟨ihomX r⟩

/-- `curry` and `uncurry` are mutually inverse. -/
example (φ : Lens (p ⊗ q) r) : Lens.uncurry (Lens.curry φ) = φ := Lens.uncurry_curry φ

example (ψ : Lens p (ihom q r)) : Lens.curry (Lens.uncurry ψ) = ψ := Lens.curry_uncurry ψ

/-- Evaluating a curried lens in parallel with `id` recovers it (counit naturality). -/
example (φ : Lens (p ⊗ q) r) :
    Lens.eval q r ∘ₗ (Lens.curry φ ⊗ₗ Lens.id q) = φ := Lens.eval_comp_curry φ

/-- The hom-set transposition is an equivalence. -/
example : Lens (p ⊗ q) r ≃ Lens p (ihom q r) := Lens.curryEquiv

end PFunctor
