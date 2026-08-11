/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all PolyFun.Interaction.TwoParty.Decoration
import all PolyFun.Interaction.TwoParty.Role
public import PolyFun.Interaction.Basic.Append
public import PolyFun.Interaction.Basic.Decoration
public import PolyFun.Interaction.Basic.TypeTree
public import PolyFun.Interaction.TwoParty.Decoration
public import PolyFun.Interaction.TwoParty.Role

/-!
# Swapping roles

Involutivity of `Role.swap`, compatibility with `RoleDecoration.map`, and interaction with
appended role decorations.
-/

public section

universe u

namespace Interaction
namespace TwoParty

open TwoParty

@[simp, grind =]
theorem Role.swap_swap (r : Role) : r.swap.swap = r := by cases r <;> rfl

@[simp, grind =]
theorem RoleDecoration.swap_swap : (spec : TypeTree) → (roles : RoleDecoration spec) →
    roles.swap.swap = roles := by
  intro spec roles
  unfold RoleDecoration.swap
  rw [PFunctor.FreeM.Displayed.Decoration.map_comp]
  rw [show (fun _ => Role.swap ∘ Role.swap) = (fun _ r => r) by
    funext _ r
    exact Role.swap_swap r]
  exact PFunctor.FreeM.Displayed.Decoration.map_id spec roles

/-- Swapping commutes with appended role decorations. -/
theorem RoleDecoration.swap_append {s₁ : TypeTree.{u}} {s₂ : PFunctor.FreeM.Path s₁ → TypeTree.{u}}
    (r₁ : RoleDecoration s₁) (r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)) :
    RoleDecoration.swap (r₁.append r₂) =
      (RoleDecoration.swap r₁).append (fun tr₁ => RoleDecoration.swap (r₂ tr₁)) :=
  PFunctor.FreeM.Displayed.Decoration.map_append
    (P := TypeTree.basePFunctor) (α := PUnit.{u+1}) (β := PUnit.{u+1})
    (fun _ => Role.swap) s₁ s₂ r₁ r₂

end TwoParty
end Interaction
