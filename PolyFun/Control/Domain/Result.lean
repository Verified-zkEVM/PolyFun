/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Order.OmegaCompletePartialOrder
public import ToCslib.Order.DiscreteOmegaCompletePartialOrder
public import ToCslib.Order.SumOmegaCompletePartialOrder
public import ToCslib.Order.WithBotOmegaCompletePartialOrder

/-!
# Partial results with errors and ordered values

`DomainResult ε α` distinguishes divergence, a discrete error, and a value
whose components may still be partial. Binding is strict in the outer result
and continuous in both the result and the continuation.
-/

public section

open OmegaCompletePartialOrder

/-- A fresh bottom below disjoint errors and ordered returned values. -/
abbrev DomainResult (ε α : Type*) := WithBot (DiscreteOrder ε ⊕ α)

namespace DomainResult

variable {ε α β : Type*}

/-- Return a value without demanding its components. -/
@[expose] def value (x : α) : DomainResult ε α :=
  ((Sum.inr x : DiscreteOrder ε ⊕ α) : WithBot (DiscreteOrder ε ⊕ α))

/-- Report an error, distinct from divergence and every returned value. -/
@[expose] def error (e : ε) : DomainResult ε α :=
  ((Sum.inl ⟨e⟩ : DiscreteOrder ε ⊕ α) : WithBot (DiscreteOrder ε ⊕ α))

@[simp] theorem value_inj {x y : α} : value (ε := ε) x = value y ↔ x = y := by
  simp [value]

@[simp] theorem error_inj {e e' : ε} : error (α := α) e = error e' ↔ e = e' := by
  simp [error, DiscreteOrder.mk.injEq]

@[simp] theorem value_ne_error (x : α) (e : ε) : value x ≠ error e := by
  simp [value, error]

@[simp] theorem value_ne_bot (x : α) : value (ε := ε) x ≠ ⊥ := WithBot.coe_ne_bot

@[simp] theorem error_ne_bot (e : ε) : error (α := α) e ≠ ⊥ := WithBot.coe_ne_bot

/-- Case analysis using the public bottom, error and value constructors. -/
@[elab_as_elim] theorem inductionOn {motive : DomainResult ε α → Prop}
    (d : DomainResult ε α) (bot : motive ⊥)
    (error : ∀ e, motive (DomainResult.error e))
    (value : ∀ x, motive (DomainResult.value x)) : motive d := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot
  | coe d =>
      cases d with
      | inl e => exact error e.value
      | inr x => exact value x

variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

/-- Returning a value is continuous in the information inside that value. -/
@[expose] noncomputable def valueContinuous : α →𝒄 DomainResult ε α :=
  .ofFun value (WithBot.ωScottContinuous_coe.comp Sum.ωScottContinuous_inr)

/-- Eliminate an outer suspension into any pointed domain. The error handler
may itself return a function, without introducing another suspension. -/
@[expose] noncomputable def elim [OrderBot β] (fail : ε → β) (f : α →𝒄 β) :
    DomainResult ε α →𝒄 β :=
  WithBot.extend (Sum.elimContinuous (DiscreteOrder.continuousMap fail) f)

@[simp] theorem elim_bot [OrderBot β] (fail : ε → β) (f : α →𝒄 β) :
    elim fail f ⊥ = ⊥ := rfl

@[simp] theorem elim_error [OrderBot β] (fail : ε → β) (f : α →𝒄 β) (e : ε) :
    elim fail f (error e) = fail e := rfl

@[simp] theorem elim_value [OrderBot β] (fail : ε → β) (f : α →𝒄 β) (a : α) :
    elim fail f (value a) = f a := rfl

/-- Eliminating a suspension is continuous in its value continuation. -/
@[fun_prop] theorem ωScottContinuous_elim [OrderBot β] (fail : ε → β) :
    ωScottContinuous (elim (α := α) fail) := by
  apply ContinuousHom.ωScottContinuous_of_apply
  intro x
  induction x using inductionOn with
  | bot => exact ωScottContinuous.const
  | error e => exact ωScottContinuous.const
  | value a =>
      exact ContinuousHom.ωScottContinuous_apply ωScottContinuous.id ωScottContinuous.const

/-- The continuous eliminator, including its continuation argument. -/
@[expose] noncomputable def elimContinuous [OrderBot β] (fail : ε → β) :
    (α →𝒄 β) →𝒄 (DomainResult ε α →𝒄 β) := .ofFun (elim fail) (ωScottContinuous_elim fail)

/-- Binding propagates divergence and errors and passes a value, including
its partial components, to the continuation. -/
@[expose] noncomputable def bind (f : α →𝒄 DomainResult ε β) :
    DomainResult ε α →𝒄 DomainResult ε β :=
  WithBot.extend (Sum.elimContinuous
    (DiscreteOrder.continuousMap error) f)

@[simp] theorem bind_bot (f : α →𝒄 DomainResult ε β) : bind f ⊥ = ⊥ := rfl

@[simp] theorem bind_error (f : α →𝒄 DomainResult ε β) (e : ε) :
    bind f (error e) = error e := rfl

@[simp] theorem bind_value (f : α →𝒄 DomainResult ε β) (x : α) :
    bind f (value x) = f x := rfl

/-- Binding also depends continuously on the continuation. -/
@[fun_prop] theorem ωScottContinuous_bind :
    ωScottContinuous (bind (ε := ε) (α := α) (β := β)) := by
  apply ContinuousHom.ωScottContinuous_of_apply
  intro x
  induction x using WithBot.recBotCoe with
  | bot => exact ωScottContinuous.const
  | coe x =>
      cases x with
      | inl e => exact ωScottContinuous.const
      | inr a =>
          exact ContinuousHom.ωScottContinuous_apply ωScottContinuous.id ωScottContinuous.const

/-- Binding as a continuous operation on continuations and computations. -/
@[expose] noncomputable def bindContinuous :
    (α →𝒄 DomainResult ε β) →𝒄 (DomainResult ε α →𝒄 DomainResult ε β) :=
  .ofFun bind ωScottContinuous_bind

/-- Demand only the outer constructor of the first computation, then continue. -/
@[expose] noncomputable def force :
    DomainResult ε α →𝒄 (DomainResult ε β →𝒄 DomainResult ε β) :=
  (bindContinuous.comp (ContinuousHom.curry
    (ContinuousHom.ofFun (fun p : DomainResult ε β × α => p.1)))).swapArgs

@[simp] theorem force_value (x : α) (next : DomainResult ε β) :
    force (value x) next = next := rfl

@[simp] theorem force_error (e : ε) (next : DomainResult ε β) :
    force (α := α) (error e) next = error e := rfl

@[simp] theorem force_bot (next : DomainResult ε β) :
    force (α := α) ⊥ next = ⊥ := rfl

/-- Outer forcing is strict binding with a constant continuation. -/
theorem force_eq_bind (x : DomainResult ε α) (next : DomainResult ε β) :
    force x next = bind (ContinuousHom.const next) x := rfl


variable {γ : Type*} [OmegaCompletePartialOrder γ]

/-- Strict left-to-right lifting of a continuous binary value operation. -/
@[expose] noncomputable def bind₂ (f : α →𝒄 (β →𝒄 DomainResult ε γ)) :
    DomainResult ε α →𝒄 (DomainResult ε β →𝒄 DomainResult ε γ) :=
  ((bindContinuous).comp ((bindContinuous.comp f).swapArgs)).swapArgs

/-- Applying a lifted function demands the function but passes its argument
as a suspended computation. -/
@[expose] noncomputable def applyContinuous :
    DomainResult ε (DomainResult ε α →𝒄 DomainResult ε β) →𝒄
      (DomainResult ε α →𝒄 DomainResult ε β) :=
  (bindContinuous.comp ContinuousHom.id.swapArgs).swapArgs

@[simp] theorem bind₂_value (f : α →𝒄 (β →𝒄 DomainResult ε γ)) (a : α)
    (b : DomainResult ε β) : bind₂ f (value a) b = bind (f a) b := rfl

@[simp] theorem bind₂_error (f : α →𝒄 (β →𝒄 DomainResult ε γ)) (e : ε)
    (b : DomainResult ε β) : bind₂ f (error e) b = error e := rfl

@[simp] theorem bind₂_bot (f : α →𝒄 (β →𝒄 DomainResult ε γ)) (b : DomainResult ε β) :
    bind₂ f ⊥ b = ⊥ := rfl

@[simp] theorem applyContinuous_value (f : DomainResult ε α →𝒄 DomainResult ε β)
    (x : DomainResult ε α) : applyContinuous (value f) x = f x := rfl

@[simp] theorem applyContinuous_error (e : ε) (x : DomainResult ε α) :
    applyContinuous (β := β) (error e) x = error e := rfl

@[simp] theorem applyContinuous_bot (x : DomainResult ε α) :
    applyContinuous (β := β) ⊥ x = ⊥ := rfl

@[simp] theorem value_le_value_iff (x y : α) :
    value (ε := ε) x ≤ value y ↔ x ≤ y := by
  simp [value]

@[simp] theorem error_le_error_iff (e e' : ε) :
    error (α := α) e ≤ error e' ↔ e = e' := by
  simp [error, DiscreteOrder.mk.injEq]

@[simp] theorem not_error_le_value (e : ε) (x : α) : ¬error e ≤ value x := by
  simp [error, value]

@[simp] theorem not_value_le_error (e : ε) (x : α) : ¬value x ≤ error e := by
  simp [error, value]

end DomainResult
