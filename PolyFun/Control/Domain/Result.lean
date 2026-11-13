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
public import ToCslib.Data.Fin.MOfFn

/-!
# Partial results with errors and ordered values

`DomainResult ε α` is a semantic target for languages with general recursion,
runtime errors and lazy data. It distinguishes divergence, a discrete error, and
a value whose components may still be partial. An error is not bottom, and no
later approximation can turn it into a value.

Binding is strict in the outer result and continuous in both the result and the
continuation. The other operations fix an evaluation order: `force` demands only
an outer constructor, `bind₂` demands two results from left to right, and
`applyContinuous` demands a function but suspends its argument. `elim` eliminates
into any pointed domain, so a family of meanings needs no further suspension.

`valueEmbedding` embeds returned values, and `map` changes them without any order, so a decoder
into results over native values is a `Control.Semantics.CertifiedMeaning` into
`valueEmbedding`. `toOption` keeps a returned value and forgets the difference between bottom and
an error.

`bindPlain` and `ifValue` sequence results without any order, beside `map`, so a native evaluator
can compute with them. `bindPlain` passes bottom and errors through, and `ifValue` gives bottom at
an error too. `Fin.mOfFn` in the monad of `value` and `bindPlain` (`DomainResult.monad`) collects a
`Fin`-indexed family from left to right. That monad is not an instance, so `Option`'s monad keeps
its meaning at the underlying type. On ordered values, `bind` is `bindPlain` (`bind_eq_bindPlain`).

Above a returned value lie only values above it (`value_le_iff`), and above an error only that
error (`error_le_iff`). A decoder `dec` *decodes above* an encoder `enc` (`DecodesAbove`) when the
computations that decode to `x` are exactly those above `enc x`. Then decoding is stable upward,
and a monotone map acts on every computation that decodes to `x` as it acts on `enc x`
(`DecodesAbove.dec_apply_eq_of_monotone`). So a fact proved at encodings transfers to
computations that only decode to a value. No order on the decoded type is assumed.
-/

public section

universe u

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

/-- Returned values embed faithfully into results. -/
@[expose] def valueEmbedding : α ↪ DomainResult ε α := ⟨value, fun _ _ => value_inj.mp⟩

@[simp] theorem coe_valueEmbedding : ⇑(valueEmbedding : α ↪ DomainResult ε α) = value := rfl

/-- Apply a function to a returned value, keeping bottom and every error. Neither type needs
an order, so `map` also reads a result into a type of native values. -/
@[expose] def map (f : α → β) : DomainResult ε α → DomainResult ε β :=
  WithBot.map (Sum.map id f)

@[simp] theorem map_bot (f : α → β) : map f (⊥ : DomainResult ε α) = ⊥ := rfl

@[simp] theorem map_error (f : α → β) (e : ε) : map f (error e : DomainResult ε α) = error e :=
  rfl

@[simp] theorem map_value (f : α → β) (x : α) :
    map f (value x : DomainResult ε α) = value (f x) := rfl

/-- `map f d` returns `y` exactly when `d` returns a value that `f` sends to `y`. -/
theorem map_eq_value_iff {f : α → β} {d : DomainResult ε α} {y : β} :
    map f d = value y ↔ ∃ x, d = value x ∧ f x = y := by
  induction d using inductionOn with
  | bot => exact ⟨fun h => absurd h.symm (value_ne_bot _), fun ⟨_, h, _⟩ => absurd h.symm
      (value_ne_bot _)⟩
  | error e => exact ⟨fun h => absurd h.symm (value_ne_error _ _), fun ⟨_, h, _⟩ => absurd h.symm
      (value_ne_error _ _)⟩
  | value x => simp

/-- Keep a value, and send bottom and every error to `none`. -/
@[expose] def toOption : DomainResult ε α → Option α
  | ⊥ => none
  | some (.inl _) => none
  | some (.inr x) => some x

@[simp] theorem toOption_bot : toOption (⊥ : DomainResult ε α) = none := rfl

@[simp] theorem toOption_error (e : ε) : toOption (error e : DomainResult ε α) = none := rfl

@[simp] theorem toOption_value (x : α) : toOption (value x : DomainResult ε α) = some x := rfl

@[simp]
theorem toOption_comp_value : toOption ∘ (value : α → DomainResult ε α) = some := rfl

/-- Reading a value commutes with changing it. -/
@[simp] theorem toOption_map (f : α → β) (d : DomainResult ε α) :
    toOption (map f d) = (toOption d).map f := by
  induction d using inductionOn <;> rfl

/-- `toOption` reads `y` exactly from the value `y`. -/
theorem toOption_eq_some_iff {d : DomainResult ε α} {y : α} :
    toOption d = some y ↔ d = value y := by
  induction d using inductionOn with
  | bot => exact ⟨fun h => absurd h (Option.some_ne_none y).symm, fun h => absurd h.symm
      (value_ne_bot y)⟩
  | error e => exact ⟨fun h => absurd h (Option.some_ne_none y).symm, fun h => absurd h.symm
      (value_ne_error y e)⟩
  | value x => rw [toOption_value, Option.some_inj, value_inj]

/-! ## Sequencing without an order -/

/-- Continue with a returned value; bottom and every error pass through. Unlike `bind`, it needs
no order on either type, so it sequences results over native values. -/
@[expose] def bindPlain (d : DomainResult ε α) (f : α → DomainResult ε β) : DomainResult ε β :=
  match d with
  | none => none
  | some (.inl e) => some (.inl e)
  | some (.inr x) => f x

@[simp] theorem bindPlain_bot (f : α → DomainResult ε β) : bindPlain ⊥ f = ⊥ := rfl

@[simp] theorem bindPlain_error (e : ε) (f : α → DomainResult ε β) :
    bindPlain (error e) f = error e := rfl

@[simp] theorem bindPlain_value (x : α) (f : α → DomainResult ε β) :
    bindPlain (value x) f = f x := rfl

/-- `bindPlain d f` returns `y` exactly when `d` returns a value at which `f` returns `y`. -/
theorem bindPlain_eq_value_iff {d : DomainResult ε α} {f : α → DomainResult ε β} {y : β} :
    bindPlain d f = value y ↔ ∃ x, d = value x ∧ f x = value y := by
  induction d using inductionOn with
  | bot => exact ⟨fun h => absurd h.symm (value_ne_bot _), fun ⟨_, h, _⟩ => absurd h.symm
      (value_ne_bot _)⟩
  | error e => exact ⟨fun h => absurd h.symm (value_ne_error _ _), fun ⟨_, h, _⟩ => absurd h.symm
      (value_ne_error _ _)⟩
  | value x => simp

/-- Changing a returned value is continuing with the changed value. -/
theorem map_eq_bindPlain (f : α → β) (d : DomainResult ε α) :
    map f d = bindPlain d (value ∘ f) := by
  induction d using inductionOn <;> rfl

/-- Continue with a returned value, and give bottom otherwise, also at an error. -/
@[expose] def ifValue (d : DomainResult ε α) (f : α → DomainResult ε β) : DomainResult ε β :=
  match d with
  | some (.inr x) => f x
  | _ => ⊥

@[simp] theorem ifValue_bot (f : α → DomainResult ε β) : ifValue ⊥ f = ⊥ := rfl

@[simp] theorem ifValue_error (e : ε) (f : α → DomainResult ε β) : ifValue (error e) f = ⊥ := rfl

@[simp] theorem ifValue_value (x : α) (f : α → DomainResult ε β) : ifValue (value x) f = f x :=
  rfl

/-- Results over unordered values as a monad, with `value` and `bindPlain`. It is not an
instance: through the abbreviation, a search for a monad at `DomainResult ε α` would also find
`Option`'s. `Fin.mOfFn` in this monad collects `n` results from left to right, and the first result
that is not a value is the result. -/
@[expose, reducible] def monad : Monad (DomainResult.{_, u} ε) where
  pure := value
  bind := bindPlain

theorem lawfulMonad : @LawfulMonad (DomainResult.{_, u} ε) monad := by
  let := monad (ε := ε)
  exact LawfulMonad.mk' _ (fun x => by induction x using inductionOn <;> rfl) (fun _ _ => rfl)
    (fun x _ _ => by induction x using inductionOn <;> rfl)

/-- Collecting values returns them. -/
@[simp] theorem mOfFn_value (n : ℕ) (g : Fin n → α) :
    @Fin.mOfFn (DomainResult ε) monad α n (fun i => value (g i)) = value g :=
  @Fin.mOfFn_pure _ monad α lawfulMonad n g

/-- Collecting returns `g` exactly when every result is the matching value of `g`. -/
theorem mOfFn_eq_value_iff {n : ℕ} {f : Fin n → DomainResult ε α} {g : Fin n → α} :
    @Fin.mOfFn (DomainResult ε) monad α n f = value g ↔ ∀ i, f i = value (g i) := by
  refine ⟨fun h => ?_, fun h => by rw [show f = fun i => value (g i) from funext h,
    mOfFn_value]⟩
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    change bindPlain (f 0) (fun x => bindPlain (@Fin.mOfFn _ monad α n fun i => f i.succ)
      fun rest => value (Fin.cons x rest)) = value g at h
    generalize hf0 : f 0 = r at h
    induction r using inductionOn with
    | bot => exact absurd h.symm (value_ne_bot _)
    | error e => exact absurd h.symm (value_ne_error _ _)
    | value x =>
      rw [bindPlain_value] at h
      generalize ht : @Fin.mOfFn _ monad α n (fun i => f i.succ) = t at h
      induction t using inductionOn with
      | bot => exact absurd h.symm (value_ne_bot _)
      | error e => exact absurd h.symm (value_ne_error _ _)
      | value rest =>
        rw [bindPlain_value, value_inj] at h
        subst h
        intro i
        induction i using Fin.cases with
        | zero => exact hf0
        | succ i => exact ih ht i

/-! ## What lies above a value, and decoders whose fibres are up-sets -/

section Order

variable [Preorder α]

/-- What lies above a returned value is a returned value above it. -/
theorem value_le_iff {x : α} {r : DomainResult ε α} : value x ≤ r ↔ ∃ y, r = value y ∧ x ≤ y := by
  induction r using inductionOn with
  | bot => exact ⟨fun h => absurd h (WithBot.not_coe_le_bot _), fun ⟨_, h, _⟩ => absurd h.symm
      (value_ne_bot _)⟩
  | error e => exact ⟨fun h => absurd h (by simp [error, value]), fun ⟨_, h, _⟩ => absurd h.symm
      (value_ne_error _ _)⟩
  | value y => simp [value]

/-- An error has only itself above it. -/
theorem error_le_iff {e : ε} {r : DomainResult ε α} : error e ≤ r ↔ r = error e := by
  induction r using inductionOn with
  | bot => exact ⟨fun h => absurd h (WithBot.not_coe_le_bot _), fun h => absurd h.symm
      (error_ne_bot _)⟩
  | error e' => simp [error, DiscreteOrder.mk.injEq, eq_comm]
  | value y => exact ⟨fun h => absurd h (by simp [error, value]), fun h => absurd h
      (value_ne_error _ _)⟩

end Order

/-- Over a discrete type, a returned value has only itself above it. -/
theorem value_le_iff_eq {x : DiscreteOrder β} {r : DomainResult ε (DiscreteOrder β)} :
    value x ≤ r ↔ r = value x := by
  rw [value_le_iff]
  exact ⟨fun ⟨_, h, hxy⟩ => hxy ▸ h, fun h => ⟨x, h, le_rfl⟩⟩

/-- A discrete result reads as `x` exactly when it lies above the value `⟨x⟩`. -/
theorem map_value_eq_value_iff {d : DomainResult ε (DiscreteOrder β)} {x : β} :
    map DiscreteOrder.value d = value x ↔ value ⟨x⟩ ≤ d := by
  rw [value_le_iff_eq, map_eq_value_iff]
  exact ⟨fun ⟨_, h, hx⟩ => hx ▸ h, fun h => ⟨_, h, rfl⟩⟩

/-- `dec` decodes above `enc` when the computations that decode to the value `x` are exactly those
above `enc x`. No order on the decoded type is assumed. -/
@[expose] def DecodesAbove {D N : Type*} [Preorder D] (enc : N → D)
    (dec : D → DomainResult ε N) : Prop :=
  ∀ d x, dec d = value x ↔ enc x ≤ d

namespace DecodesAbove

variable {D N : Type*} [Preorder D] {enc : N → D} {dec : D → DomainResult ε N}

/-- A computation that decodes to `x` lies above `enc x`. -/
theorem enc_le_of_dec_eq (h : DecodesAbove enc dec) {d : D} {x : N} (hd : dec d = value x) :
    enc x ≤ d :=
  (h d x).1 hd

/-- Decoding is stable upward from a computation that decodes to a value. -/
theorem dec_eq_of_le (h : DecodesAbove enc dec) {d d' : D} (hle : d ≤ d') {x : N}
    (hd : dec d = value x) : dec d' = value x :=
  (h d' x).2 ((h.enc_le_of_dec_eq hd).trans hle)

/-- The decoder reads an encoding back. -/
theorem dec_enc (h : DecodesAbove enc dec) (x : N) : dec (enc x) = value x :=
  (h _ x).2 le_rfl

/-- What a monotone map does to an encoding, it does to every computation that decodes to the
same value. -/
theorem dec_apply_eq_of_monotone {D' N' : Type*} [Preorder D'] {enc' : N' → D'}
    {dec' : D' → DomainResult ε N'} (h : DecodesAbove enc dec) (h' : DecodesAbove enc' dec')
    {F : D → D'} (hF : Monotone F) {x : N} {y : N'} (hFx : dec' (F (enc x)) = value y) {d : D}
    (hd : dec d = value x) : dec' (F d) = value y :=
  h'.dec_eq_of_le (hF (h.enc_le_of_dec_eq hd)) hFx

end DecodesAbove

/-- Over a discrete type, reading the value back decodes above `value ∘ DiscreteOrder.mk`. -/
theorem decodesAbove_map_value :
    DecodesAbove (fun x : β => (value ⟨x⟩ : DomainResult ε (DiscreteOrder β)))
      (map DiscreteOrder.value) :=
  fun _ _ => map_value_eq_value_iff

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
  elim error f

@[simp] theorem bind_bot (f : α →𝒄 DomainResult ε β) : bind f ⊥ = ⊥ := rfl

@[simp] theorem bind_error (f : α →𝒄 DomainResult ε β) (e : ε) :
    bind f (error e) = error e := rfl

@[simp] theorem bind_value (f : α →𝒄 DomainResult ε β) (x : α) :
    bind f (value x) = f x := rfl

/-- On ordered values, the continuous `bind` is `bindPlain` with the same continuation. -/
theorem bind_eq_bindPlain (f : α →𝒄 DomainResult ε β) (d : DomainResult ε α) :
    bind f d = bindPlain d f := by
  induction d using inductionOn <;> rfl

/-- Binding also depends continuously on the continuation. -/
@[fun_prop] theorem ωScottContinuous_bind :
    ωScottContinuous (bind (ε := ε) (α := α) (β := β)) :=
  ωScottContinuous_elim error

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
