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

  Deprecated aliases and parse-only notation bridging the former `X`-based
  spelling of the polynomial algebra to the `y`-based one, so downstream
  projects can migrate incrementally:

  - `PFunctor.X` and every `X`-named companion declaration resolve, with a
    deprecation warning, to their `y`-named counterparts.
  - `A X^ B` still parses (to `PFunctor.monomial A B`), but is parse-only:
    goals always display the canonical `A y^ B` form.
  - `p ^ n` still elaborates to `PFunctor.compNth p n` through the `NatPow`
    instance kept here; the canonical spelling is `p ◃^ n`. Typeclass
    synthesis cannot surface a deprecation warning, so this instance is
    silent.

  Everything in this file is slated for removal once dependent projects
  reference the `y`-spelling directly; nothing inside PolyFun may use it.
-/

public section

universe uA uB

namespace PFunctor

/-- Parse-only compatibility spelling of the monomial `A y^ B`. -/
scoped syntax:82 term:83 " X^ " term:82 : term

scoped macro_rules
  | `($A X^ $B) => `(PFunctor.monomial $A $B)

/-- Compatibility `NatPow` instance sending `p ^ n` to the composition power
`p ◃^ n`. Note that this reading conflicts with the semiring intuition for the
product instance (`p ^ 2` is `p ◃ p`, not `p * p`), which is why the marked
notation `◃^` is the canonical spelling. -/
instance instNatPowPFunctor : NatPow PFunctor.{max uA uB, uB} where
  pow := compNth

@[deprecated (since := "2026-08-17")] alias X := y
@[deprecated (since := "2026-08-17")] alias X_A := y_A
@[deprecated (since := "2026-08-17")] alias X_B := y_B
@[deprecated (since := "2026-08-17")] alias X_eq_linear_pUnit := y_eq_linear_pUnit
@[deprecated (since := "2026-08-17")] alias X_eq_purePower_pUnit := y_eq_purePower_pUnit
@[deprecated (since := "2026-08-17")] alias homFromX := homFromY
@[deprecated (since := "2026-08-17")] alias ihomX := ihomY
@[deprecated (since := "2026-08-17")] alias ihom_X_A := ihom_y_A

namespace Equiv

@[deprecated (since := "2026-08-17")] alias tensorX := tensorY
@[deprecated (since := "2026-08-17")] alias xTensor := yTensor
@[deprecated (since := "2026-08-17")] alias compX := compY
@[deprecated (since := "2026-08-17")] alias XComp := yComp

end Equiv

namespace Lens

@[deprecated (since := "2026-08-17")] alias fromX := fromY
@[deprecated (since := "2026-08-17")] alias fromX_toFunA := fromY_toFunA
@[deprecated (since := "2026-08-17")] alias fromX_toFunB := fromY_toFunB
@[deprecated (since := "2026-08-17")] alias xTensor_natural := yTensor_natural
@[deprecated (since := "2026-08-17")] alias tensorX_natural := tensorY_natural

namespace Equiv

@[deprecated (since := "2026-08-17")] alias compX := compY
@[deprecated (since := "2026-08-17")] alias XComp := yComp
@[deprecated (since := "2026-08-17")] alias tensorX := tensorY
@[deprecated (since := "2026-08-17")] alias xTensor := yTensor

end Equiv

end Lens

namespace Chart.Equiv

@[deprecated (since := "2026-08-17")] alias tensorX := tensorY
@[deprecated (since := "2026-08-17")] alias xTensor := yTensor

end Chart.Equiv

namespace CofreeP

@[deprecated (since := "2026-08-17")] alias projectionN_one_comp_compX := projectionN_one_comp_compY
@[deprecated (since := "2026-08-17")] alias projectionN_two_comp_compX := projectionN_two_comp_compY

end CofreeP

end PFunctor
