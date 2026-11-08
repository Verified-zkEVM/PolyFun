/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Embeddings and discrete instances for sums

Mathlib gives `α ⊕ β` the coproduct measurable space. Both injections are then measurable
embeddings, and a sum of discrete spaces, or of spaces with measurable singletons, is again one.
-/

@[expose] public section

-- upstream candidate

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The left injection embeds a measurable space into a sum. -/
theorem measurableEmbedding_inl : MeasurableEmbedding (@Sum.inl α β) where
  injective := Sum.inl_injective
  measurable := measurable_inl
  measurableSet_image' _ hs := hs.inl_image

/-- The right injection embeds a measurable space into a sum. -/
theorem measurableEmbedding_inr : MeasurableEmbedding (@Sum.inr α β) where
  injective := Sum.inr_injective
  measurable := measurable_inr
  measurableSet_image' _ hs := hs.inr_image

namespace Sum

/-- A sum of spaces with measurable singletons has measurable singletons. -/
instance instMeasurableSingletonClass [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton
    | .inl a => by simpa using (measurableSet_singleton a).inl_image (β := β)
    | .inr b => by simpa using (measurableSet_singleton b).inr_image (α := α)

/-- A sum of discrete measurable spaces is discrete. -/
instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] :
    DiscreteMeasurableSpace (α ⊕ β) where
  forall_measurableSet _ := measurableSet_sum_iff.2 ⟨.of_discrete, .of_discrete⟩

end Sum
