/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.Equiv.Basic
public import PolyFun.PFunctor.Lens.Basic
public import PolyFun.PFunctor.Chart.Basic
public import PolyFun.PFunctor.InternalHom
public import PolyFun.PFunctor.Adjunctions
public import PolyFun.PFunctor.Cofree.FiniteProjection

/-!
  # Transitional `X`-spelling compatibility surface

  Aggregate import for deprecated aliases and parse-only notation bridging the
  former `X`-based spelling of the polynomial algebra to the `y`-based one, so
  downstream projects can migrate incrementally:

  - `PFunctor.X` and every `X`-named companion declaration resolve, with a
    deprecation warning, to their `y`-named counterparts.
  - `A X^ B` still parses (to `PFunctor.monomial A B`), but is parse-only:
    goals always display the canonical `A y^ B` form.
  - `p ^ n` still elaborates to `PFunctor.compNth p n` through the `NatPow`
    compatibility instance; the canonical spelling is `p ◃^ n`. Typeclass
    synthesis cannot surface a deprecation warning, so this instance is
    silent.

  Each alias lives beside its canonical declaration so ordinary direct imports
  preserve the old API. This module re-exports the complete compatibility
  surface and is slated for removal once dependent projects reference the
  `y`-spelling directly; nothing inside PolyFun may import it.
-/
