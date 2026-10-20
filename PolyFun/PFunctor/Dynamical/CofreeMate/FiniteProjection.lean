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
tree. Composing that mate with `CofreeP.projectionN P n` recovers exactly the
existing finite `n`-step system `DynSystem.nStep`.
-/

@[expose] public section

universe u

namespace PFunctor
namespace DynSystem

/-- Projecting a dynamical system's cofree mate to depth `n` is its `n`-step
run. This is the dynamical-system specialization of Niu–Spivak Proposition
8.49. -/
theorem projectionN_comp_cofreeMate {S : Type u} {P : PFunctor.{u, u}}
    (system : DynSystem S P) (n : ℕ) :
    CofreeP.projectionN P n ∘ₗ system.cofreeMate.toLens =
      system.nStep n := by
  change CofreeP.projectionN P n ∘ₗ
      (CofreeP.extend (stateComonoid S) system).toLens = system.nStep n
  rw [CofreeP.projectionN_comp_extend, nStep_eq]

@[deprecated (since := "2026-10-19")] alias cofreeMate_comp_projectionN :=
  projectionN_comp_cofreeMate

/-- At depth two, finite projection recovers the two-step system `Lens.speedup`
after removing the innermost right composition unit. -/
theorem projectionN_two_comp_cofreeMate
    {S : Type u} {P : PFunctor.{u, u}} (system : DynSystem S P) :
    (Lens.id P ◃ₗ Lens.Equiv.compY.toLens) ∘ₗ
        (CofreeP.projectionN P 2 ∘ₗ system.cofreeMate.toLens) =
      Lens.speedup system :=
  (congrArg (fun lens => (Lens.id P ◃ₗ Lens.Equiv.compY.toLens) ∘ₗ lens)
    (projectionN_comp_cofreeMate system 2)).trans (nStep_two_eq_speedup system)

@[deprecated (since := "2026-10-19")] alias cofreeMate_comp_projectionN_two :=
  projectionN_two_comp_cofreeMate

end DynSystem
end PFunctor
