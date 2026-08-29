/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin
-/
module

public import ToCslib.Computability.PolyTime

/-!
# Appending a fixed bit with a single-tape machine

This supplies the missing low-level string primitive needed to feed a fixed
encoded answer into a machine state. It is independent of PolyFun and oracle
semantics. The encoding-level API also records the additive description-size
bound for finite iteration; it makes no polynomial-time claim about an
iteration count that grows with the security parameter.
-/

@[expose] public section

namespace Cslib.Turing.SingleTapeTM

open Cslib.Turing Relation

/-- Append `c` at the right end of the input and return the head to the first symbol. -/
def snocComputer (c : Bool) : SingleTapeTM Bool where
  State := Unit ⊕ Unit
  q₀ := .inl ()
  tr q h := match q with
    | .inl () => match h with
      | some b => ⟨⟨some b, some .right⟩, some (.inl ())⟩
      | none => ⟨⟨some c, some .left⟩, some (.inr ())⟩
    | .inr () => match h with
      | some b => ⟨⟨some b, some .left⟩, some (.inr ())⟩
      | none => ⟨⟨none, some .right⟩, none⟩

private def snocPush : StackTape Bool → List Bool → StackTape Bool
  | left, [] => left
  | left, bit :: tail => snocPush (StackTape.cons (some bit) left) tail

@[simp] private lemma snocPush_nil (left : StackTape Bool) : snocPush left [] = left := rfl

@[simp] private lemma snocPush_cons (left : StackTape Bool) (bit : Bool) (tail : List Bool) :
    snocPush left (bit :: tail) = snocPush (StackTape.cons (some bit) left) tail := rfl

private lemma stackTape_ext {left right : StackTape Bool}
    (equality : left.toList = right.toList) : left = right := by
  cases left
  cases right
  cases equality
  rfl

private lemma snocPush_toList (left : StackTape Bool) (input : List Bool) :
    (snocPush left input).toList = input.reverse.map some ++ left.toList := by
  induction input generalizing left with
  | nil => simp
  | cons bit tail induction =>
    rw [snocPush_cons, induction (StackTape.cons (some bit) left),
      StackTape.cons_some_toList]
    simp

private lemma mk₁_eq (input : List Bool) :
    (BiTape.mk₁ input : BiTape Bool) =
      ⟨(StackTape.mapSome input).head, ∅, (StackTape.mapSome input).tail⟩ := by
  cases input <;> rfl

private lemma snocComputer_phaseA (c : Bool) (left : StackTape Bool) :
    ∀ input : List Bool,
      RelatesInSteps (snocComputer c).TransitionRelation
        ⟨some (.inl ()),
          ⟨(StackTape.mapSome input).head, left, (StackTape.mapSome input).tail⟩⟩
        ⟨some (.inl ()), ⟨none, snocPush left input, ∅⟩⟩ input.length := by
  intro input
  induction input generalizing left with
  | nil => exact .refl _
  | cons bit tail induction =>
    refine .head _ (t' := (⟨some (.inl ()),
      ⟨(StackTape.mapSome tail).head, StackTape.cons (some bit) left,
        (StackTape.mapSome tail).tail⟩⟩ : (snocComputer c).Cfg)) _ _ ?_ ?_
    · rfl
    · simpa using induction (StackTape.cons (some bit) left)

private lemma snocComputer_phaseB (c : Bool) :
    ∀ (input : List Bool) (right : StackTape Bool),
      RelatesInSteps (snocComputer c).TransitionRelation
        ⟨some (.inr ()),
          ⟨(StackTape.mapSome input).head, (StackTape.mapSome input).tail, right⟩⟩
        ⟨none, ⟨(snocPush right input).head, ∅, (snocPush right input).tail⟩⟩
        (input.length + 1) := by
  intro input
  induction input with
  | nil => intro right; exact .single rfl
  | cons bit tail induction =>
    intro right
    refine .head _ (t' := (⟨some (.inr ()),
      ⟨(StackTape.mapSome tail).head, (StackTape.mapSome tail).tail,
        StackTape.cons (some bit) right⟩⟩ : (snocComputer c).Cfg)) _ _ ?_ ?_
    · rfl
    · simpa using induction (StackTape.cons (some bit) right)

private lemma snocPush_empty (input : List Bool) :
    snocPush (∅ : StackTape Bool) input = StackTape.mapSome input.reverse := by
  apply stackTape_ext
  rw [snocPush_toList]
  simp [StackTape.mapSome]

private lemma snocPush_final (c : Bool) (input : List Bool) :
    snocPush (StackTape.cons (some c) ∅) input.reverse =
      StackTape.mapSome (input ++ [c]) := by
  apply stackTape_ext
  rw [snocPush_toList, StackTape.cons_some_toList]
  simp [StackTape.mapSome]

/-- `snocComputer` outputs `input ++ [c]` within `2 * input.length + 2` steps. -/
theorem snocComputer_outputsWithinTime (c : Bool) (input : List Bool) :
    (snocComputer c).OutputsWithinTime input (input ++ [c]) (2 * input.length + 2) := by
  have forward := snocComputer_phaseA c ∅ input
  have backward := snocComputer_phaseB c input.reverse (StackTape.cons (some c) ∅)
  rw [← snocPush_empty input, snocPush_final c input] at backward
  have chain :
      RelatesInSteps (snocComputer c).TransitionRelation
        ⟨some (.inl ()), (BiTape.mk₁ input : BiTape Bool)⟩
        ⟨none, (BiTape.mk₁ (input ++ [c]) : BiTape Bool)⟩
        (input.length + (1 + (input.reverse.length + 1))) := by
    rw [mk₁_eq input, mk₁_eq (input ++ [c])]
    exact forward.trans ((RelatesInSteps.single (by rfl)).trans backward)
  refine RelatesWithinSteps.of_le
    (RelatesWithinSteps.of_relatesInSteps chain) ?_
  simp only [List.length_reverse]
  omega

/-- The exact linear-time witness for appending a fixed bit. -/
def snocTimeComputable (c : Bool) : TimeComputable (fun input => input ++ [c]) where
  tm := snocComputer c
  timeBound n := 2 * n + 2
  outputsFunInTime input := snocComputer_outputsWithinTime c input

/-- Appending a fixed bit is polynomial-time computable. -/
noncomputable def snocPolyTimeComputable (c : Bool) :
    PolyTimeComputable (fun input => input ++ [c]) where
  toTimeComputable := snocTimeComputable c
  poly := 2 * Polynomial.X + Polynomial.C 2
  bounds n := by simp [snocTimeComputable, two_mul]

/-- The append machine has two states. -/
theorem size_snocPolyTimeComputable (c : Bool) :
    (snocPolyTimeComputable c).size ≤ 2 := by
  change Fintype.card (Unit ⊕ Unit) ≤ 2
  simp

end Cslib.Turing.SingleTapeTM

namespace ToCslib.Computability.EncPolyTime

open Cslib.Turing.SingleTapeTM

/-- View the identity through an output encoding with one fixed bit appended. -/
noncomputable def appendBit {σ : Type} (encoding : σ → List Bool) (c : Bool) :
    EncPolyTime encoding (fun value => encoding value ++ [c]) _root_.id where
  toFun input := input ++ [c]
  polyTime := snocPolyTimeComputable c
  map_encode _ := rfl

/-- The append witness uses at most two states. -/
theorem size_appendBit {σ : Type} (encoding : σ → List Bool) (c : Bool) :
    (appendBit encoding c).size ≤ 2 := size_snocPolyTimeComputable c

/-- A fixed finite iterate has description size at most one plus the sum of
the step-machine sizes. This is description accounting only: composing a
parameter-dependent number of polynomial-time machines is not asserted to
have a uniform polynomial running-time bound. -/
theorem exists_iterate {σ : Type} (encoding : σ → List Bool) {step : σ → σ}
    (stepCode : EncPolyTime encoding encoding step) :
    ∀ count : ℕ, ∃ code : EncPolyTime encoding encoding (step^[count]),
      code.size ≤ 1 + count * stepCode.size := by
  intro count
  induction count with
  | zero =>
    refine ⟨(EncPolyTime.id encoding).copy (step^[0]) (fun state => ?_), ?_⟩
    · simp
    · simp
  | succ count induction =>
    obtain ⟨code, sizeBound⟩ := induction
    refine ⟨(code.comp stepCode).copy (step^[count + 1]) (fun state => ?_), ?_⟩
    · exact (Function.iterate_succ_apply' step count state).symm
    · rw [size_copy, size_comp]
      have multiplication :
          (count + 1) * stepCode.size = count * stepCode.size + stepCode.size := by
        ring
      omega

end ToCslib.Computability.EncPolyTime
