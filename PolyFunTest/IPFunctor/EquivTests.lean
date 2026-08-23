/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.IPFunctor.Equiv.Basic

/-!
# Regression Tests for Indexed Polynomial Equivalence Bridges

These producer canaries exercise the canonical conversions from
`IPFunctor.Equiv` to indexed lens and chart equivalences. The concrete fixture
uses a non-involutive three-cycle on both positions and responses, and its
source index depends on whether those values agree. This distinguishes forward
and inverse maps as well as lens pullback from chart pushforward.
-/

@[expose] public section

universe uI uJ uA₁ uA₂ uB₁ uB₂

namespace IPFunctorEquivTests

inductive Three where
  | zero
  | one
  | two
deriving DecidableEq

def cycle : Three → Three
  | .zero => .one
  | .one => .two
  | .two => .zero

def uncycle : Three → Three
  | .zero => .two
  | .one => .zero
  | .two => .one

def cycleEquiv : Three ≃ Three where
  toFun := cycle
  invFun := uncycle
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- Source polynomial for the concrete bridge canaries. Its child index is
`true` exactly when the position and response select the same branch. -/
def P : IPFunctor Bool Unit where
  A _ := Three
  B _ _ := Three
  src _ a b := decide (a = b)

/-- Target polynomial for the concrete bridge canaries. It has a separate
declaration so the tests exercise an actual cross-polynomial conversion. -/
def Q : IPFunctor Bool Unit where
  A _ := Three
  B _ _ := Three
  src _ a b := decide (a = b)

/-- A nonidentity structural equivalence preserving the response-dependent
source index by cycling positions and responses together. -/
def equiv : IPFunctor.Equiv P Q where
  equivA _ := cycleEquiv
  equivB _ _ := cycleEquiv
  src_eq _ a b := by cases a <;> cases b <;> rfl

/-! ## Lens conversion -/

example : equiv.toLensEquiv.toLens.toFunA () Three.zero = Three.one := rfl

-- Lens responses pull back, so the forward lens applies the inverse cycle.
example :
    equiv.toLensEquiv.toLens.toFunB () Three.zero Three.two = Three.one := rfl

example : equiv.toLensEquiv.invLens.toFunA () Three.zero = Three.two := rfl

-- The inverse lens pulls back through the inverse equivalence, hence cycles.
example :
    equiv.toLensEquiv.invLens.toFunB () Three.zero Three.zero = Three.one := rfl

-- The converted `src_eq` observes the response-dependent child index.
example :
    P.src () Three.zero
        (equiv.toLensEquiv.toLens.toFunB () Three.zero Three.two) =
      Q.src () (equiv.toLensEquiv.toLens.toFunA () Three.zero) Three.two :=
  equiv.toLensEquiv.toLens.src_eq () Three.zero Three.two

example :
    P.src () Three.zero
      (equiv.toLensEquiv.toLens.toFunB () Three.zero Three.two) = false := rfl

example :
    P.src () Three.zero
      (equiv.toLensEquiv.toLens.toFunB () Three.zero Three.one) = true := rfl

example : IPFunctor.Lens.comp equiv.symm.toLens equiv.toLens = IPFunctor.Lens.id P := by simp

example : IPFunctor.Lens.comp equiv.toLens equiv.symm.toLens = IPFunctor.Lens.id Q := by simp

example : (IPFunctor.Equiv.refl P).toLens = IPFunctor.Lens.id P := by simp

example :
    (equiv.trans equiv.symm).toLens = IPFunctor.Lens.comp equiv.symm.toLens equiv.toLens :=
  IPFunctor.Equiv.toLens_trans equiv equiv.symm

/-! ## Chart conversion -/

example : equiv.toChartEquiv.toChart.toFunA () Three.zero = Three.one := rfl

-- Chart responses move forward through the same nontrivial cycle as positions.
example :
    equiv.toChartEquiv.toChart.toFunB () Three.zero Three.zero = Three.one := rfl

example : equiv.toChartEquiv.invChart.toFunA () Three.zero = Three.two := rfl

example :
    equiv.toChartEquiv.invChart.toFunB () Three.zero Three.zero = Three.two := rfl

-- The chart conversion preserves the same dependent source behavior covariantly.
example :
    Q.src () (equiv.toChartEquiv.toChart.toFunA () Three.zero)
        (equiv.toChartEquiv.toChart.toFunB () Three.zero Three.two) =
      P.src () Three.zero Three.two :=
  equiv.toChartEquiv.toChart.src_eq () Three.zero Three.two

example : Q.src () (equiv.toChartEquiv.toChart.toFunA () Three.zero)
    (equiv.toChartEquiv.toChart.toFunB () Three.zero Three.two) = false := rfl

example : Q.src () (equiv.toChartEquiv.toChart.toFunA () Three.zero)
    (equiv.toChartEquiv.toChart.toFunB () Three.zero Three.zero) = true := rfl

example : IPFunctor.Chart.comp equiv.symm.toChart equiv.toChart = IPFunctor.Chart.id P := by simp

example : IPFunctor.Chart.comp equiv.toChart equiv.symm.toChart = IPFunctor.Chart.id Q := by simp

example : (IPFunctor.Equiv.refl P).toChart = IPFunctor.Chart.id P := by simp

example :
    (equiv.trans equiv.symm).toChart = IPFunctor.Chart.comp equiv.symm.toChart equiv.toChart :=
  IPFunctor.Equiv.toChart_trans equiv equiv.symm

/-! ## Independent universes -/

section MixedUniverses

variable {I : Type uI} {J : Type uJ}
  {P₁ : IPFunctor.{uI, uJ, uA₁, uB₁} I J}
  {Q₁ : IPFunctor.{uI, uJ, uA₂, uB₂} I J}

example (e : IPFunctor.Equiv P₁ Q₁) : IPFunctor.Lens.Equiv P₁ Q₁ := e.toLensEquiv

example (e : IPFunctor.Equiv P₁ Q₁) : IPFunctor.Chart.Equiv P₁ Q₁ := e.toChartEquiv

example (e : IPFunctor.Equiv P₁ Q₁) :
    IPFunctor.Lens.comp e.symm.toLens e.toLens = IPFunctor.Lens.id P₁ := by
  simp

example (e : IPFunctor.Equiv P₁ Q₁) :
    IPFunctor.Chart.comp e.symm.toChart e.toChart = IPFunctor.Chart.id P₁ := by
  simp

end MixedUniverses

end IPFunctorEquivTests
