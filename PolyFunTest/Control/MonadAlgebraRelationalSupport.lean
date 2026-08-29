/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.Control.Monad.Algebra.Relational.Support

/-!
# Exact-support relational algebra canaries

These tests distinguish the production demonic and angelic relational observations and
pin their `StrictBind` and `Anchored` witnesses on the nondeterministic `SetM` monad.
-/

@[expose] public section

namespace PolyFunTest.MonadAlgebraRelationalSupport

open MAlgRelOrdered MonadAttach

def leftChoices : SetM Nat := ({0, 1} : Set Nat)
def rightChoices : SetM Nat := ({1, 2} : Set Nat)

section Demonic

local instance instDemonicLeft : MAlgOrdered SetM Prop := mAlgOrderedPropDemonic
local instance instDemonicRel : MAlgRelOrdered SetM SetM Prop :=
  mAlgRelOrderedPropDemonic
local instance instDemonicStrict : StrictBind SetM SetM Prop := strictBindPropDemonic
local instance instDemonicAnchored : Anchored SetM SetM Prop := anchoredPropDemonic

#synth StrictBind SetM SetM Prop
#synth Anchored SetM SetM Prop

/-- Equality does not hold demoniacally: every cross-product pair would have to agree. -/
example : ¬ RelWP leftChoices rightChoices (· = ·) := by
  rw [relWP_demonic_iff_forall_support]
  intro h
  have h0 : 0 ∈ support leftChoices := by
    change 0 ∈ ({0, 1} : Set Nat)
    simp
  have h1 : 1 ∈ support rightChoices := by
    change 1 ∈ ({1, 2} : Set Nat)
    simp
  exact Nat.zero_ne_one (h 0 h0 1 h1)

/-- Ordering does hold for every pair in this particular cross product. -/
example : RelWP leftChoices rightChoices (· ≤ ·) := by
  rw [relWP_demonic_iff_forall_support]
  intro a ha b hb
  change a ∈ ({0, 1} : Set Nat) at ha
  change b ∈ ({1, 2} : Set Nat) at hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

end Demonic

section Angelic

local instance instAngelicLeft : MAlgOrdered SetM Prop := mAlgOrderedPropAngelic
local instance instAngelicRel : MAlgRelOrdered SetM SetM Prop :=
  mAlgRelOrderedPropAngelic
local instance instAngelicStrict : StrictBind SetM SetM Prop := strictBindPropAngelic
local instance instAngelicAnchored : Anchored SetM SetM Prop := anchoredPropAngelic

#synth StrictBind SetM SetM Prop
#synth Anchored SetM SetM Prop

/-- Equality does hold angelically: the shared output `1` witnesses it. -/
example : RelWP leftChoices rightChoices (· = ·) := by
  rw [relWP_angelic_iff_exists_support]
  refine ⟨1, ?_, 1, ?_, rfl⟩
  · change 1 ∈ ({0, 1} : Set Nat)
    simp
  · change 1 ∈ ({1, 2} : Set Nat)
    simp

end Angelic

end PolyFunTest.MonadAlgebraRelationalSupport
