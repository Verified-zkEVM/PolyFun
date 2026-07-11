/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Comonoid

/-!
# Examples for comonoids in `(Poly, ◃, y)`

Regression tests: the state comonoid `S y^S` satisfies the comonoid laws (by
construction), is a state system, and its `n`-fold comultiplication `δ^{(n)}`
recovers the counit at `n = 0` and unfolds as expected.
-/

@[expose] public section

universe u

namespace PFunctor

variable {S : Type u}

/-- The state comonoid's comultiplication is the transition lens. -/
example : (stateComonoid S).comult = Lens.fixState := rfl

/-- The state comonoid is a state system (Spivak–Niu Ex 7.22). -/
example : (stateComonoid S).IsStateSystem := isStateSystem_stateComonoid S

/-- `δ^{(0)}` is the counit. -/
example : (stateComonoid S).comultN 0 = (stateComonoid S).counit := rfl

/-- `δ^{(1)}` unfolds through the counit. -/
example :
    (stateComonoid S).comultN 1
      = (Lens.id _ ◃ₗ (stateComonoid S).counit) ∘ₗ Lens.fixState := rfl

/-- `δ^{(n+1)}` unfolds by one composition step. -/
example (n : ℕ) :
    (stateComonoid S).comultN (n + 1)
      = (Lens.id _ ◃ₗ (stateComonoid S).comultN n) ∘ₗ Lens.fixState := rfl

/-- A fully concrete instance: `Bool` states. -/
example : (stateComonoid Bool).IsStateSystem := isStateSystem_stateComonoid Bool

end PFunctor
