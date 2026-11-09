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

`DomainResult.Approx P d r` is the relation for an evaluator that may give up: bottom on the right
approximates every result, and otherwise `r` is related to `d` by `LiftRel` with equal errors
(`approx_iff`). `approx_bind` and `approx_bind₂` carry it through the continuous `bind` and
`bind₂` on the left and `bindPlain` on the right.
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

/-! ## Approximation by a result that may give up -/

/-- `r` approximates `d` through `P`: bottom approximates every result, an error only the same
error, and a returned value only a returned value related to it by `P`. Unlike `LiftRel`, it asks
nothing when `r` is bottom (`approx_iff`), so an evaluator that gives up approximates every
meaning. -/
@[expose] def Approx {X α : Type*} (P : X → α → Prop) : DomainResult ε X → DomainResult ε α → Prop
  | _, none => True
  | d, some (.inl e) => d = some (.inl e)
  | d, some (.inr w) => ∃ x, d = value x ∧ P x w

section Approx

variable {X : Type*} {P : X → α → Prop}

theorem approx_bot (P : X → α → Prop) (d : DomainResult ε X) : Approx P d ⊥ := trivial

theorem approx_error {d : DomainResult ε X} {e : ε} :
    Approx P d (error e : DomainResult ε α) ↔ d = error e := Iff.rfl

theorem approx_value {d : DomainResult ε X} {w : α} :
    Approx P d (value w) ↔ ∃ x, d = value x ∧ P x w := Iff.rfl

theorem approx_value_value {x : X} {w : α} :
    Approx P (value x : DomainResult ε X) (value w) ↔ P x w :=
  ⟨fun ⟨_, hx, h⟩ => value_inj.mp hx ▸ h, fun h => ⟨x, rfl, h⟩⟩

/-- Approximation is the lifted relation with equal errors, or bottom on the right. -/
theorem approx_iff {d : DomainResult ε X} {r : DomainResult ε α} :
    Approx P d r ↔ r = ⊥ ∨ LiftRel (· = ·) P d r := by
  induction r using inductionOn with
  | bot => exact ⟨fun _ => .inl rfl, fun _ => trivial⟩
  | error e =>
    rw [approx_error, or_iff_right (error_ne_bot e)]
    induction d using inductionOn with
    | bot => exact ⟨fun h => absurd h.symm (error_ne_bot e), False.elim⟩
    | error e' => rw [error_inj, liftRel_error_error]
    | value x => exact ⟨fun h => absurd h (value_ne_error x e), False.elim⟩
  | value w =>
    rw [or_iff_right (value_ne_bot w)]
    induction d using inductionOn with
    | bot => exact ⟨fun ⟨_, h, _⟩ => absurd h.symm (value_ne_bot _), False.elim⟩
    | error e => exact ⟨fun ⟨_, h, _⟩ => absurd h (value_ne_error _ _).symm, False.elim⟩
    | value x => rw [approx_value_value, liftRel_value_value]

/-- Demanding approximated results and continuing with approximated continuations gives
approximated results. -/
theorem approx_bind {Y β : Type*} [OmegaCompletePartialOrder X] [OmegaCompletePartialOrder Y]
    {Q : Y → β → Prop} {F : X →𝒄 DomainResult ε Y} {d : DomainResult ε X} {r : DomainResult ε α}
    {g : α → DomainResult ε β} (hd : Approx P d r) (hF : ∀ x w, P x w → Approx Q (F x) (g w)) :
    Approx Q (bind F d) (bindPlain r g) := by
  match r, hd with
  | none, _ => trivial
  | some (.inl e), hd =>
    change d = some (.inl e) at hd
    subst hd
    rfl
  | some (.inr w), ⟨x, hd, hx⟩ =>
    subst hd
    exact hF x w hx

/-- Demanding two approximated results, left first, and combining approximated values gives
approximated results. -/
theorem approx_bind₂ {Y Z β γ : Type*} [OmegaCompletePartialOrder X]
    [OmegaCompletePartialOrder Y] [OmegaCompletePartialOrder Z] {Q : Y → β → Prop}
    {S : Z → γ → Prop} {F : X →𝒄 (Y →𝒄 DomainResult ε Z)} {x : DomainResult ε X}
    {y : DomainResult ε Y} {x' : DomainResult ε α} {y' : DomainResult ε β}
    {g : α → β → DomainResult ε γ} (hx : Approx P x x') (hy : Approx Q y y')
    (hF : ∀ a b u v, P a u → Q b v → Approx S (F a b) (g u v)) :
    Approx S (bind₂ F x y) (bindPlain x' fun u => bindPlain y' fun v => g u v) := by
  match x', hx with
  | none, _ => trivial
  | some (.inl e), hx =>
    change x = some (.inl e) at hx
    subst hx
    rfl
  | some (.inr u), ⟨a, ha, hau⟩ =>
    subst ha
    match y', hy with
    | none, _ => trivial
    | some (.inl e), hy =>
      change y = some (.inl e) at hy
      subst hy
      rfl
    | some (.inr v), ⟨b, hb, hbv⟩ =>
      subst hb
      exact hF a b u v hau hbv

end Approx

end DomainResult
