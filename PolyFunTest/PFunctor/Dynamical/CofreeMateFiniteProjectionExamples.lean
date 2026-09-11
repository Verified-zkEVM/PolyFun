/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Dynamical.CofreeMate.FiniteProjection
public import PolyFunTest.PFunctor.Dynamical.CofreeMateExamples

/-!
# Regression tests for finite projections of cofree mates

These tests exercise the generic mate/`Run_n` theorem and a branching
three-state system whose depth-two backward map observably reaches the state
selected by the ordered path `false` then `true`.
-/

@[expose] public section

universe u

namespace PFunctor
namespace CofreeMateFiniteProjectionTest

open CofreePolynomialTest
open CofreeMateTest
open ComonoidCategoryTest

/-! ## Generic finite-run equations -/

example (P : PFunctor.{u, u}) (S : Type u)
    (system : DynSystem S P) (n : ℕ) :
    CofreeP.projectionN P n ∘ₗ system.cofreeMate.toLens =
      system.nStep n :=
  DynSystem.cofreeMate_comp_projectionN system n

example (P : PFunctor.{u, u}) (S : Type u)
    (system : DynSystem S P) :
    (Lens.id P ◃ₗ Lens.Equiv.compY.toLens) ∘ₗ
        (CofreeP.projectionN P 2 ∘ₗ system.cofreeMate.toLens) =
      system.twoStep :=
  DynSystem.cofreeMate_comp_projectionN_two system

/-! ## Observable branching behavior -/

/-- The depth-zero projection leaves the source state unchanged. -/
example : (CofreeP.projectionN binaryP 0 ∘ₗ
      branchingSystem.cofreeMate.toLens).toFunB .source PUnit.unit =
    ThreeState.source := by
  rw [DynSystem.cofreeMate_comp_projectionN]
  rfl

/-- Projecting the mate through `false` then `true` reaches the final state,
pinning both the dependent backward map and the order of the two edges. -/
example : (CofreeP.projectionN binaryP 2 ∘ₗ
      branchingSystem.cofreeMate.toLens).toFunB .source
        ⟨false, ⟨true, PUnit.unit⟩⟩ = ThreeState.final := by
  rw [DynSystem.cofreeMate_comp_projectionN]
  rfl

/-- The same concrete depth-two run agrees with the established binary
two-step system after applying the inner right unitor. -/
example : ((Lens.id binaryP ◃ₗ Lens.Equiv.compY.toLens) ∘ₗ
      (CofreeP.projectionN binaryP 2 ∘ₗ branchingSystem.cofreeMate.toLens)).toFunB
      .source ⟨false, true⟩ = ThreeState.final := by
  rw [DynSystem.cofreeMate_comp_projectionN_two]
  rfl

end CofreeMateFiniteProjectionTest
end PFunctor
