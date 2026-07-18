/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.FiniteProjection
public import PolyFun.PFunctor.Dynamical.CofreeMate
public import PolyFun.PFunctor.Dynamical.RunN

/-!
# Finite projections of dynamical-system cofree mates

The cofree mate of a dynamical system contains its entire infinite behavior
tree.  Composing that mate with `CofreeP.projectionN P n` recovers exactly the
existing finite `n`-step system `DynSystem.nStep`.
-/

@[expose] public section

universe u

namespace PFunctor
namespace DynSystem

/-- Projecting a dynamical system's cofree mate to depth `n` is its `n`-step
run.  This is the dynamical-system specialization of Spivak--Niu Proposition
8.49. -/
theorem cofreeMate_comp_projectionN
    {S : Type u} {P : PFunctor.{u, u}}
    (system : DynSystem S P) (n : ℕ) :
    system.cofreeMate.toLens ⨟ CofreeP.projectionN P n =
      system.nStep n := by
  change (CofreeP.extend (stateComonoid S) system).toLens ⨟
      CofreeP.projectionN P n = system.nStep n
  rw [CofreeP.extend_comp_projectionN, nStep_eq]
  rfl

/-- At depth two, finite projection recovers the established two-step system
after removing the innermost right composition unit. -/
theorem cofreeMate_comp_projectionN_two
    {S : Type u} {P : PFunctor.{u, u}} (system : DynSystem S P) :
    (system.cofreeMate.toLens ⨟ CofreeP.projectionN P 2) ⨟
        (Lens.id P ◃ₗ Lens.Equiv.compX.toLens) =
      system.twoStep := by
  have hprojection := congrArg
    (fun lens => (Lens.id P ◃ₗ Lens.Equiv.compX.toLens) ∘ₗ lens)
    (cofreeMate_comp_projectionN system 2)
  exact hprojection.trans (nStep_two_eq_twoStep system)

end DynSystem
end PFunctor
