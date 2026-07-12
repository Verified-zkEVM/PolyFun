/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Composite

/-!
# Examples for lenses into composites and the composition power

Regression tests: the destructor-triple `Equiv` round-trips, and `compNthMap`
unfolds to iterated `compMap`.
-/

@[expose] public section

universe u

namespace PFunctor

variable {p q r : PFunctor.{u, u}}

/-- A lens into `q ◃ r` round-trips through its destructor triple. -/
example (φ : Lens p (q ◃ r)) : Lens.ofCompTriple (Lens.toCompTriple φ) = φ := by simp

/-- ...and every triple round-trips back through the lens. -/
example (t : Lens.CompTriple p q r) : Lens.toCompTriple (Lens.ofCompTriple t) = t := by simp

/-- The composition power unfolds to iterated `compMap`. -/
example (l : Lens p q) : Lens.compNthMap l 2 = l ◃ₗ (l ◃ₗ Lens.id X) := rfl

/-- `compNthMap` of the identity is the identity. -/
example (n : ℕ) : Lens.compNthMap (Lens.id p) n = Lens.id (compNth p n) :=
  Lens.compNthMap_id p n

end PFunctor
