/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Composite

/-!
# Examples for lenses into composites and the composition power

Regression tests: the named components of a lens into a composite are
definitionally its existing lens data, and `compNthMap` unfolds to iterated
`compMap`.
-/

@[expose] public section

universe u

namespace PFunctor

variable {p q r : PFunctor.{u, u}}

/-- The named outer component is the first component of the position map. -/
example (φ : Lens p (q ◃ r)) (i : p.A) : φ.compOuter i = (φ.toFunA i).1 := rfl

/-- The named inner component is the continuation in the position map. -/
example (φ : Lens p (q ◃ r)) (i : p.A) (u : q.B (φ.compOuter i)) :
    φ.compInner i u = (φ.toFunA i).2 u := rfl

/-- The named joint pullback is the lens's direction map. -/
example (φ : Lens p (q ◃ r)) (i : p.A) : φ.compPullback i = φ.toFunB i := rfl

/-- The composition power unfolds to iterated `compMap`. -/
example (l : Lens p q) : Lens.compNthMap l 2 = l ◃ₗ (l ◃ₗ Lens.id X) := rfl

/-- `compNthMap` of the identity is the identity. -/
example (n : ℕ) : Lens.compNthMap (Lens.id p) n = Lens.id (compNth p n) :=
  Lens.compNthMap_id p n

/-- `compNthMap` respects composition. -/
example (l₁ : Lens q r) (l₂ : Lens p q) (n : ℕ) :
    Lens.compNthMap (l₁ ∘ₗ l₂) n = Lens.compNthMap l₁ n ∘ₗ Lens.compNthMap l₂ n :=
  Lens.compNthMap_comp l₁ l₂ n

end PFunctor
