/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.Control.Monad.Algebra.Relational
public import PolyFun.Control.Monad.Support

/-!
# Relational weakest preconditions from exact support

This file supplies two concrete `Prop`-valued relational monad algebras for monads with
exact support:

* the **demonic** algebra requires the postcondition for every pair of possible outputs;
* the **angelic** algebra requires it for some pair of possible outputs.

Both observations satisfy strict bind and are anchored to their matching unary support
algebras. The definitions are deliberately named rather than global instances because
the demonic and angelic interpretations have the same instance head, and because other
relational semantics (for example couplings) may be appropriate for the same monads.
-/

@[expose] public section

universe v₁ v₂

namespace MonadAttach

open MAlgRelOrdered

variable {m₁ : Type → Type v₁} {m₂ : Type → Type v₂}
variable [Monad m₁] [Monad m₂] [LawfulMonad m₁] [LawfulMonad m₂]
variable [MonadAttach m₁] [MonadAttach m₂] [ExactMonadAttach m₁] [ExactMonadAttach m₂]

/-- The demonic relational support algebra: every possible left output and every possible
right output must satisfy the relational postcondition. -/
@[instance_reducible]
def mAlgRelOrderedPropDemonic : MAlgRelOrdered m₁ m₂ Prop where
  rwp x y post := AllOutputs (fun a => AllOutputs (post a) y) x
  rwp_pure _ _ _ := by simp
  rwp_mono hpost := by
    intro h a ha b hb
    exact hpost a b (h a ha b hb)
  rwp_bind_le x y f g post := by
    intro h c hc d hd
    obtain ⟨a, ha, hc⟩ := mem_support_bind.mp hc
    obtain ⟨b, hb, hd⟩ := mem_support_bind.mp hd
    exact h a ha b hb c hc d hd

/-- The angelic relational support algebra: some possible left/right output pair must
satisfy the relational postcondition. -/
@[instance_reducible]
def mAlgRelOrderedPropAngelic : MAlgRelOrdered m₁ m₂ Prop where
  rwp x y post := SomeOutput (fun a => SomeOutput (post a) y) x
  rwp_pure _ _ _ := by simp
  rwp_mono hpost := by
    rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨a, ha, b, hb, hpost a b hab⟩
  rwp_bind_le x y f g post := by
    rintro ⟨a, ha, b, hb, c, hc, d, hd, hcd⟩
    exact ⟨c, mem_support_bind.mpr ⟨a, ha, hc⟩,
      d, mem_support_bind.mpr ⟨b, hb, hd⟩, hcd⟩

section Demonic

attribute [local instance] mAlgRelOrderedPropDemonic mAlgOrderedPropDemonic

/-- Support characterization of the demonic relational weakest precondition. -/
theorem relWP_demonic_iff_forall_support {α β : Type} (x : m₁ α) (y : m₂ β)
    (post : α → β → Prop) :
    RelWP x y post ↔ ∀ a ∈ support x, ∀ b ∈ support y, post a b :=
  Iff.rfl

/-- Exact support makes the demonic relational bind law an equality. -/
theorem strictBindPropDemonic : StrictBind m₁ m₂ Prop := by
  refine { rwp_bind := ?_ }
  intro α β γ δ x y f g post
  apply propext
  constructor
  · intro h c hc d hd
    obtain ⟨a, ha, hc⟩ := mem_support_bind.mp hc
    obtain ⟨b, hb, hd⟩ := mem_support_bind.mp hd
    exact h a ha b hb c hc d hd
  · intro h a ha b hb c hc d hd
    exact h c (mem_support_bind.mpr ⟨a, ha, hc⟩)
      d (mem_support_bind.mpr ⟨b, hb, hd⟩)

/-- The demonic relational support algebra is anchored to the demonic unary support
algebra on both sides. -/
theorem anchoredPropDemonic : Anchored m₁ m₂ Prop := by
  refine { rwp_pure_left := ?_, rwp_pure_right := ?_ }
  · intro α β a y post
    apply propext
    change AllOutputs (fun a' => AllOutputs (post a') y) (pure a : m₁ α) ↔
      MAlgOrdered.wp y (post a)
    rw [allOutputs_pure, wp_iff_allOutputs]
  · intro α β x b post
    apply propext
    change AllOutputs (fun a => AllOutputs (post a) (pure b : m₂ β)) x ↔
      MAlgOrdered.wp x (fun a => post a b)
    rw [wp_iff_allOutputs]
    apply allOutputs_congr
    intro a
    exact allOutputs_pure (post a) b

end Demonic

section Angelic

attribute [local instance] mAlgRelOrderedPropAngelic mAlgOrderedPropAngelic

/-- Support characterization of the angelic relational weakest precondition. -/
theorem relWP_angelic_iff_exists_support {α β : Type} (x : m₁ α) (y : m₂ β)
    (post : α → β → Prop) :
    RelWP x y post ↔ ∃ a ∈ support x, ∃ b ∈ support y, post a b :=
  Iff.rfl

/-- Exact support makes the angelic relational bind law an equality. -/
theorem strictBindPropAngelic : StrictBind m₁ m₂ Prop := by
  refine { rwp_bind := ?_ }
  intro α β γ δ x y f g post
  apply propext
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, hcd⟩
    exact ⟨c, mem_support_bind.mpr ⟨a, ha, hc⟩,
      d, mem_support_bind.mpr ⟨b, hb, hd⟩, hcd⟩
  · rintro ⟨c, hc, d, hd, hcd⟩
    obtain ⟨a, ha, hc⟩ := mem_support_bind.mp hc
    obtain ⟨b, hb, hd⟩ := mem_support_bind.mp hd
    exact ⟨a, ha, b, hb, c, hc, d, hd, hcd⟩

/-- The angelic relational support algebra is anchored to the angelic unary support
algebra on both sides. -/
theorem anchoredPropAngelic : Anchored m₁ m₂ Prop := by
  refine { rwp_pure_left := ?_, rwp_pure_right := ?_ }
  · intro α β a y post
    apply propext
    change SomeOutput (fun a' => SomeOutput (post a') y) (pure a : m₁ α) ↔
      MAlgOrdered.wp y (post a)
    rw [someOutput_pure, wp_angelic_iff_someOutput]
  · intro α β x b post
    apply propext
    change SomeOutput (fun a => SomeOutput (post a) (pure b : m₂ β)) x ↔
      MAlgOrdered.wp x (fun a => post a b)
    rw [wp_angelic_iff_someOutput]
    apply someOutput_congr
    intro a
    exact someOutput_pure (post a) b

end Angelic

end MonadAttach
