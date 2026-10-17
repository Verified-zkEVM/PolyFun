/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Order.OmegaCompletePartialOrder

/-!
# Discrete value domains

An equality-ordered type is an omega-CPO: every increasing sequence is
constant. The wrapper avoids changing the ordinary arithmetic order on
numbers or the Boolean order when using them as runtime values.
-/

public section

-- upstream candidate: the discrete omega-CPO and its continuous maps.

open OmegaCompletePartialOrder

/-- A type equipped with the equality order. -/
@[ext] structure DiscreteOrder (α : Type*) where
  /-- The underlying value. -/
  value : α
  deriving DecidableEq, Repr

namespace DiscreteOrder

variable {α β : Type*}

instance : PartialOrder (DiscreteOrder α) where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

@[simp] theorem le_iff_eq (a b : DiscreteOrder α) : a ≤ b ↔ a = b := Iff.rfl

instance : OmegaCompletePartialOrder (DiscreteOrder α) where
  ωSup c := c 0
  le_ωSup c n := (c.monotone (Nat.zero_le n)).symm
  ωSup_le _ _ h := h 0

/-- Every map from a discrete domain is continuous. -/
@[expose] def continuousMap [OmegaCompletePartialOrder β] (f : α → β) : DiscreteOrder α →𝒄 β where
  toFun x := f x.value
  monotone' _ _ h := by cases h; exact le_rfl
  map_ωSup' c := by
    apply le_antisymm
    · exact le_ωSup (c.map ⟨fun x => f x.value, fun _ _ h => by cases h; exact le_rfl⟩) 0
    · apply ωSup_le
      intro n
      change f (c n).value ≤ f (c 0).value
      have h : c 0 = c n := c.monotone (Nat.zero_le n)
      rw [h]

/-- Constructing a continuous map from a discrete domain is itself continuous. -/
@[fun_prop] theorem ωScottContinuous_continuousMap [OmegaCompletePartialOrder β] :
    ωScottContinuous (continuousMap (α := α) (β := β)) := by
  apply ContinuousHom.ωScottContinuous_of_apply
  intro x
  exact ωScottContinuous.apply x.value

end DiscreteOrder
