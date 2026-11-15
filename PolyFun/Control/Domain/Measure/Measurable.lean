/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Result
public import ToCslib.MeasureTheory.MeasurableSpace.Option
public import ToCslib.MeasureTheory.MeasurableSpace.Sum

/-!
# Measurable partial results

`DomainResult ε α` is `WithBot (DiscreteOrder ε ⊕ α)`: bottom, a discrete error, or a value. This
file gives it the measurable structure in which bottom and every error are atoms and the values
carry the σ-algebra of `α`.

- `DiscreteOrder ε` carries the discrete σ-algebra `⊤`, so errors need no σ-algebra on `ε`.
- `DomainResult ε α` carries the coproduct structure of `Option` over the coproduct structure of
  the sum. `DomainResult.measurableEquiv` identifies it with `Option (DiscreteOrder ε ⊕ α)`, and
  its underlying function is the identity. `DomainResult.measurableEquivSum` identifies it with
  `Option (ε ⊕ α)` when `ε` is discrete.
- A set of results is measurable exactly when its values form a measurable set
  (`measurableSet_iff`), and a function out of results is measurable exactly when its value branch
  is (`measurable_iff_comp_value`).
- `DomainResult.toOption`, which keeps a value and sends bottom and every error to `none`, is
  measurable (`measurable_toOption`). The preimage of `some '' s` is `value '' s`, and the
  preimage of `none` is the complement of the returned values.

There is deliberately no instance on `WithBot α` in general. For a linear order `ι` with the order
topology, Mathlib gives `WithTop ι` its Borel structure, and a symmetric Borel instance on
`WithBot ι` would agree with the coproduct structure of `Option` only propositionally. The instance
here is keyed on `WithBot (DiscreteOrder ε ⊕ α)`, and a sum is not a linear order, so such a Borel
instance would not apply to it.
-/

@[expose] public section

open MeasureTheory

namespace DiscreteOrder

variable {ε : Type*}

/-- Every set of a discrete domain is measurable. -/
instance instMeasurableSpace : MeasurableSpace (DiscreteOrder ε) := ⊤

instance instDiscreteMeasurableSpace : DiscreteMeasurableSpace (DiscreteOrder ε) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- A discrete domain is measurably equivalent to its carrier when the carrier is discrete. -/
def measurableEquiv [MeasurableSpace ε] [DiscreteMeasurableSpace ε] : DiscreteOrder ε ≃ᵐ ε where
  toFun := value
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := .of_discrete
  measurable_invFun := .of_discrete

@[simp]
theorem measurableEquiv_apply [MeasurableSpace ε] [DiscreteMeasurableSpace ε]
    (e : DiscreteOrder ε) : measurableEquiv e = e.value := rfl

@[simp]
theorem measurableEquiv_symm_apply [MeasurableSpace ε] [DiscreteMeasurableSpace ε] (e : ε) :
    measurableEquiv.symm e = mk e := rfl

end DiscreteOrder

namespace DomainResult

variable {ε α β : Type*}

/-! ## Preimages of optional values -/

theorem toOption_preimage_some_image (s : Set α) :
    toOption ⁻¹' (some '' s) = (value '' s : Set (DomainResult ε α)) := by
  ext d
  induction d using inductionOn <;> simp

theorem toOption_preimage_none :
    toOption ⁻¹' {none} = (Set.range (value : α → DomainResult ε α))ᶜ := by
  ext d
  induction d using inductionOn <;> simp

/-! ## The measurable structure -/

variable [MeasurableSpace α]

/-- Bottom and every error are atoms, and values carry the σ-algebra of `α`. This is the coproduct
structure of `Option (DiscreteOrder ε ⊕ α)`. -/
instance instMeasurableSpace : MeasurableSpace (DomainResult ε α) :=
  Option.instMeasurableSpace (α := DiscreteOrder ε ⊕ α)

instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (DomainResult ε α) :=
  Option.instMeasurableSingletonClass (α := DiscreteOrder ε ⊕ α)

instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (DomainResult ε α) :=
  Option.instDiscreteMeasurableSpace (α := DiscreteOrder ε ⊕ α)

/-- Results and optional sums of errors and values are the same measurable space. The underlying
function is the identity. -/
def measurableEquiv : DomainResult ε α ≃ᵐ Option (DiscreteOrder ε ⊕ α) where
  toEquiv := Equiv.refl _
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id

@[simp]
theorem measurableEquiv_bot : measurableEquiv (⊥ : DomainResult ε α) = none := rfl

@[simp]
theorem measurableEquiv_error (e : ε) :
    measurableEquiv (error e : DomainResult ε α) = some (.inl ⟨e⟩) := rfl

@[simp]
theorem measurableEquiv_value (x : α) :
    measurableEquiv (value x : DomainResult ε α) = some (.inr x) := rfl

@[simp]
theorem measurableEquiv_symm_none :
    (measurableEquiv (ε := ε) (α := α)).symm none = ⊥ := rfl

@[simp]
theorem measurableEquiv_symm_some_inl (e : DiscreteOrder ε) :
    (measurableEquiv (α := α)).symm (some (.inl e)) = error e.value := rfl

@[simp]
theorem measurableEquiv_symm_some_inr (x : α) :
    (measurableEquiv (ε := ε)).symm (some (.inr x)) = value x := rfl

/-- Results with a discrete error type are optional sums of errors and values. -/
def measurableEquivSum [MeasurableSpace ε] [DiscreteMeasurableSpace ε] :
    DomainResult ε α ≃ᵐ Option (ε ⊕ α) :=
  measurableEquiv.trans
    (DiscreteOrder.measurableEquiv.sumCongr (MeasurableEquiv.refl α)).optionCongr

@[simp]
theorem measurableEquivSum_bot [MeasurableSpace ε] [DiscreteMeasurableSpace ε] :
    measurableEquivSum (⊥ : DomainResult ε α) = none := rfl

@[simp]
theorem measurableEquivSum_error [MeasurableSpace ε] [DiscreteMeasurableSpace ε] (e : ε) :
    measurableEquivSum (error e : DomainResult ε α) = some (.inl e) := rfl

@[simp]
theorem measurableEquivSum_value [MeasurableSpace ε] [DiscreteMeasurableSpace ε] (x : α) :
    measurableEquivSum (value x : DomainResult ε α) = some (.inr x) := rfl

/-! ## Measurable sets and functions -/

/-- A set of results is measurable exactly when its values form a measurable set: bottom and the
errors are atoms. -/
theorem measurableSet_iff {s : Set (DomainResult ε α)} :
    MeasurableSet s ↔ MeasurableSet (value ⁻¹' s) := by
  change MeasurableSet (measurableEquiv.symm ⁻¹' s) ↔ _
  rw [Option.measurableSet_option_iff, measurableSet_sum_iff]
  exact and_iff_right MeasurableSet.of_discrete

/-- A function out of results is measurable exactly when its value branch is. -/
theorem measurable_iff_comp_value [MeasurableSpace β] {f : DomainResult ε α → β} :
    Measurable f ↔ Measurable (f ∘ value) := by
  refine ⟨fun hf => hf.comp ?_, fun hf s hs => measurableSet_iff.2 (hf hs)⟩
  exact fun s hs => measurableSet_iff.1 hs

/-- A function out of results is measurable when its value branch is. -/
theorem measurable_of_comp_value [MeasurableSpace β] {f : DomainResult ε α → β}
    (hf : Measurable (f ∘ value)) : Measurable f :=
  measurable_iff_comp_value.2 hf

@[fun_prop]
theorem measurable_value : Measurable (value : α → DomainResult ε α) :=
  fun _ hs => measurableSet_iff.1 hs

/-- Returning a value embeds `α` as a measurable subspace of results. -/
theorem measurableEmbedding_value : MeasurableEmbedding (value : α → DomainResult ε α) :=
  Option.measurableEmbedding_some.comp measurableEmbedding_inr

/-- The embedding of returned values, the output encoding of a decoded certificate, is
measurable. -/
@[fun_prop]
theorem measurable_valueEmbedding : Measurable ⇑(valueEmbedding : α ↪ DomainResult ε α) :=
  measurable_value

@[simp]
theorem measurableSet_value_image {s : Set α} :
    MeasurableSet (value '' s : Set (DomainResult ε α)) ↔ MeasurableSet s :=
  measurableEmbedding_value.measurableSet_image

theorem measurableSet_range_value : MeasurableSet (Set.range (value : α → DomainResult ε α)) :=
  measurableEmbedding_value.measurableSet_range

@[simp]
theorem measurableSet_bot : MeasurableSet ({⊥} : Set (DomainResult ε α)) :=
  measurableSet_iff.2 <| by simp [Set.preimage]

@[simp]
theorem measurableSet_singleton_error (e : ε) :
    MeasurableSet ({error e} : Set (DomainResult ε α)) :=
  measurableSet_iff.2 <| by simp [Set.preimage]

theorem measurableSet_range_error : MeasurableSet (Set.range (error : ε → DomainResult ε α)) := by
  have hempty : value ⁻¹' Set.range (error : ε → DomainResult ε α) = ∅ :=
    Set.eq_empty_of_forall_notMem fun x ⟨e, he⟩ => value_ne_error x e he.symm
  rw [measurableSet_iff, hempty]
  exact .empty

/-- Reporting an error is measurable from a discrete error type. -/
@[fun_prop]
theorem measurable_error [MeasurableSpace ε] [DiscreteMeasurableSpace ε] :
    Measurable (error : ε → DomainResult ε α) :=
  .of_discrete

@[fun_prop]
theorem measurable_toOption : Measurable (toOption : DomainResult ε α → Option α) :=
  measurable_of_comp_value Option.measurable_some

end DomainResult
