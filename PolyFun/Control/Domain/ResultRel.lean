/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Result
public import ToCslib.Order.Admissible

/-!
# Relations between partial results

`DomainResult.LiftRel E R` relates two results constructor by constructor: bottom to bottom,
errors by `E` and returned values by `R`. Neither result type needs an order, so one side can be
the result of a native evaluator.

A relation that says nothing about bottom on one side is a disjunction with `d = ⊥`. For a
semantic computation `d` and the outcome of a deterministic evaluation, such a relation is closed
under suprema of chains (`admissible_bot_or_liftRel`). It can therefore be proved for a least
fixed point by fixed-point induction.
-/

public section

open OmegaCompletePartialOrder

namespace DomainResult

variable {ε ε' α β : Type*}

/-- Results related constructor by constructor: bottom to bottom, errors by `E`, and returned
values by `R`. -/
@[expose] def LiftRel (E : ε → ε' → Prop) (R : α → β → Prop) :
    DomainResult ε α → DomainResult ε' β → Prop
  | ⊥, ⊥ => True
  | some (.inl e), some (.inl e') => E e.value e'.value
  | some (.inr x), some (.inr y) => R x y
  | _, _ => False

variable {E : ε → ε' → Prop} {R : α → β → Prop}

@[simp] theorem liftRel_bot_bot : LiftRel E R (⊥ : DomainResult ε α) (⊥ : DomainResult ε' β) :=
  trivial

@[simp] theorem liftRel_error_error (e : ε) (e' : ε') :
    LiftRel E R (error e : DomainResult ε α) (error e' : DomainResult ε' β) ↔ E e e' := Iff.rfl

@[simp] theorem liftRel_value_value (x : α) (y : β) :
    LiftRel E R (value x : DomainResult ε α) (value y : DomainResult ε' β) ↔ R x y := Iff.rfl

/-- `LiftRel` is core's `Option.Rel` of `Sum.LiftRel`, read through `DomainResult ε α`, which is
`Option (DiscreteOrder ε ⊕ α)`, so lemmas about the two core relations transfer. `LiftRel` is
defined by cases instead, so that its constructor equations hold by `Iff.rfl`. -/
theorem liftRel_iff_optionRel {d : DomainResult ε α} {r : DomainResult ε' β} :
    LiftRel E R d r ↔ Option.Rel (Sum.LiftRel (fun e e' => E e.value e'.value) R) d r := by
  match d, r with
  | none, none => exact ⟨fun _ => .none, fun _ => trivial⟩
  | none, some (.inl _) | none, some (.inr _) => exact ⟨False.elim, fun h => nomatch h⟩
  | some (.inl _), none | some (.inr _), none => exact ⟨False.elim, fun h => nomatch h⟩
  | some (.inl _), some (.inl _) => exact ⟨fun h => .some (.inl h), fun | .some (.inl h) => h⟩
  | some (.inr _), some (.inr _) => exact ⟨fun h => .some (.inr h), fun | .some (.inr h) => h⟩
  | some (.inl _), some (.inr _) | some (.inr _), some (.inl _) =>
    exact ⟨False.elim, fun | .some h => nomatch h⟩

/-- Only bottom is related to bottom. -/
theorem liftRel_bot_left {r : DomainResult ε' β} :
    LiftRel E R (⊥ : DomainResult ε α) r ↔ r = ⊥ := by
  induction r using inductionOn with
  | bot => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | error e => exact ⟨False.elim, fun h => absurd h (error_ne_bot e)⟩
  | value y => exact ⟨False.elim, fun h => absurd h (value_ne_bot y)⟩

/-- An error is related only to an error. -/
theorem liftRel_error_left {e : ε} {r : DomainResult ε' β} :
    LiftRel E R (error e : DomainResult ε α) r ↔ ∃ e', r = error e' ∧ E e e' := by
  induction r using inductionOn with
  | bot => exact ⟨False.elim, fun ⟨_, h, _⟩ => absurd h.symm (error_ne_bot _)⟩
  | error e' => simp
  | value y => exact ⟨False.elim, fun ⟨_, h, _⟩ => absurd h (value_ne_error _ _)⟩

/-- A returned value is related only to a returned value. -/
theorem liftRel_value_left {x : α} {r : DomainResult ε' β} :
    LiftRel E R (value x : DomainResult ε α) r ↔ ∃ y, r = value y ∧ R x y := by
  induction r using inductionOn with
  | bot => exact ⟨False.elim, fun ⟨_, h, _⟩ => absurd h.symm (value_ne_bot _)⟩
  | error e => exact ⟨False.elim, fun ⟨_, h, _⟩ => absurd h.symm (value_ne_error _ _)⟩
  | value y => simp

/-- Lifted relations are monotone in both relations. -/
theorem LiftRel.mono {E' : ε → ε' → Prop} {R' : α → β → Prop} (hE : ∀ e e', E e e' → E' e e')
    (hR : ∀ x y, R x y → R' x y) {d : DomainResult ε α} {r : DomainResult ε' β}
    (h : LiftRel E R d r) : LiftRel E' R' d r := by
  induction d using inductionOn with
  | bot => exact liftRel_bot_left.mpr (liftRel_bot_left.mp h)
  | error e =>
    obtain ⟨e', rfl, he⟩ := liftRel_error_left.mp h
    exact hE e e' he
  | value x =>
    obtain ⟨y, rfl, hxy⟩ := liftRel_value_left.mp h
    exact hR x y hxy

/-- Swapping the results swaps the arguments of both relations. -/
theorem LiftRel.flip {d : DomainResult ε α} {r : DomainResult ε' β} (h : LiftRel E R d r) :
    LiftRel (fun e' e => E e e') (fun y x => R x y) r d := by
  induction d using inductionOn with
  | bot =>
    obtain rfl := liftRel_bot_left.mp h
    trivial
  | error e =>
    obtain ⟨e', rfl, he⟩ := liftRel_error_left.mp h
    exact he
  | value x =>
    obtain ⟨y, rfl, hxy⟩ := liftRel_value_left.mp h
    exact hxy

/-- Equality lifts to equality. -/
theorem liftRel_eq_iff {d r : DomainResult ε α} : LiftRel (· = ·) (· = ·) d r ↔ d = r := by
  constructor
  · intro h
    induction d using inductionOn with
    | bot => exact (liftRel_bot_left.mp h).symm
    | error e =>
      obtain ⟨e', rfl, rfl⟩ := liftRel_error_left.mp h
      rfl
    | value x =>
      obtain ⟨y, rfl, rfl⟩ := liftRel_value_left.mp h
      rfl
  · rintro rfl
    induction d using inductionOn with
    | bot => trivial
    | error e => exact rfl
    | value x => exact rfl

/-- Bottom, or a relation to the unique result with property `P`, is closed under suprema of
chains when `R` is closed in its first argument. Uniqueness lets one result serve the whole chain.
`P r` typically says that a deterministic evaluation terminates with outcome `r`. -/
theorem admissible_bot_or_liftRel [OmegaCompletePartialOrder α] {P : DomainResult ε' β → Prop}
    (hP : ∀ r r', P r → P r' → r = r') (hR : ∀ y, Admissible fun x : α => R x y) :
    Admissible fun d : DomainResult ε α => d = ⊥ ∨ ∃ r, P r ∧ LiftRel E R d r := by
  have hvalue : Admissible fun x : α => ∃ r, P r ∧ LiftRel E R (value x : DomainResult ε α) r := by
    intro c hc
    obtain ⟨r, hr, hcr⟩ := hc 0
    obtain ⟨y, rfl, -⟩ := liftRel_value_left.mp hcr
    refine ⟨value y, hr, (liftRel_value_value _ _).mpr (hR y c fun n => ?_)⟩
    obtain ⟨r', hr', hcr'⟩ := hc n
    rw [hP r' (value y) hr' hr] at hcr'
    exact (liftRel_value_value _ _).mp hcr'
  have h := (Admissible.sum (admissible_discrete fun e : DiscreteOrder ε =>
    ∃ r, P r ∧ LiftRel E R (error e.value : DomainResult ε α) r) hvalue).withBot
  have heq : (fun d : DomainResult ε α => d = ⊥ ∨ ∃ r, P r ∧ LiftRel E R d r) =
      WithBot.recBotCoe True (Sum.elim
        (fun e : DiscreteOrder ε => ∃ r, P r ∧ LiftRel E R (error e.value : DomainResult ε α) r)
        fun x => ∃ r, P r ∧ LiftRel E R (value x : DomainResult ε α) r) := by
    funext d
    induction d using inductionOn with
    | bot => exact propext ⟨fun _ => trivial, fun _ => Or.inl rfl⟩
    | error e => exact propext (or_iff_right (error_ne_bot e))
    | value x => exact propext (or_iff_right (value_ne_bot x))
  rw [heq]
  exact h

end DomainResult
