/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Membership, calendar dates, and exact voting arithmetic

Dates are supplied by the environment. A quarterly interval uses calendar months,
not a fixed number of days. Abstention is represented separately from a cast vote.
-/

@[expose] public section

namespace Parliament

/-- Stable identity of a roster member, supplied by the host. -/
abbrev MemberId := Nat
/-- Stable identity allocated to a proposed question. -/
abbrev QuestionId := Nat
/-- Stable identity of a registered committee. -/
abbrev CommitteeId := Nat

/-- A civil date. `Date.Valid` is checked at the input boundary. -/
structure Date where
  /-- Gregorian calendar year. -/
  year : Nat
  /-- Calendar month, from one to twelve when valid. -/
  month : Nat
  /-- Day of the month, starting at one. -/
  day : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Date

/-- The Gregorian leap-year rule, including century exceptions. -/
def leapYear (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

/-- Length of the selected Gregorian month. -/
def daysInMonth (date : Date) : Nat :=
  if date.month == 2 then if leapYear date.year then 29 else 28
  else if [4, 6, 9, 11].contains date.month then 30 else 31

/-- The month and day are within their Gregorian ranges. -/
def Valid (date : Date) : Prop :=
  1 ≤ date.month ∧ date.month ≤ 12 ∧ 1 ≤ date.day ∧ date.day ≤ date.daysInMonth

instance (date : Date) : Decidable date.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-- Absolute month index used for calendar-quarter comparisons. -/
def monthIndex (date : Date) : Nat := date.year * 12 + (date.month - 1)

/-- Order-preserving date key; differences are not elapsed days. -/
def ordinal (date : Date) : Nat := date.monthIndex * 32 + date.day

/-- The later date is no later than the end of the third following month. -/
def withinQuarter (earlier later : Date) : Bool :=
  earlier.ordinal ≤ later.ordinal && later.monthIndex ≤ earlier.monthIndex + 3

theorem withinQuarter_month_bound (earlier later : Date)
    (h : withinQuarter earlier later = true) :
    later.monthIndex ≤ earlier.monthIndex + 3 := by
  have h' : earlier.ordinal ≤ later.ordinal ∧
      later.monthIndex ≤ earlier.monthIndex + 3 := by simpa [withinQuarter] using h
  exact h'.2

end Date

/-- An individual choice; abstention contributes to neither side of a tally. -/
inductive Vote where
  | yes | no | abstain
  deriving DecidableEq, Repr, Inhabited

/-- Supported decision thresholds, including the appeal's tie-sustains rule. -/
inductive Threshold where
  | majority | twoThirds | sustainChair
  deriving DecidableEq, Repr, Inhabited

/-- The population against which a voting threshold is measured. -/
inductive Denominator where
  | cast | present | membership
  deriving DecidableEq, Repr, Inhabited

/-- A tally of valid, nonsecret votes. -/
structure Tally where
  /-- Number of affirmative votes. -/
  yes : Nat := 0
  /-- Number of negative votes. -/
  no : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace Tally

/-- Total affirmative and negative votes, excluding abstentions. -/
def cast (t : Tally) : Nat := t.yes + t.no

/-- Select cast votes, present voters, or the full voting membership. -/
def denominator (t : Tally) (basis : Denominator) (present membership : Nat) : Nat :=
  match basis with
  | .cast => t.cast
  | .present => present
  | .membership => membership

/-- A tie sustains an appealed ruling. Zero affirmative votes cannot adopt a motion. -/
def passes (t : Tally) (threshold : Threshold) (denom : Nat) : Bool :=
  match threshold with
  | .majority => 2 * t.yes > denom
  | .twoThirds => t.yes > 0 && 3 * t.yes ≥ 2 * denom
  | .sustainChair => t.yes ≥ t.no

theorem majority_iff (t : Tally) :
    t.passes .majority t.cast = true ↔ t.no < t.yes := by
  simp [passes, cast]
  omega

theorem twoThirds_iff (t : Tally) :
    t.passes .twoThirds t.cast = true ↔ 0 < t.yes ∧ 2 * t.no ≤ t.yes := by
  simp [passes, cast]
  omega

theorem abstentions_irrelevant (t : Tally) (threshold : Threshold) (p n p' n' : Nat) :
    t.passes threshold (t.denominator .cast p n) =
      t.passes threshold (t.denominator .cast p' n') := rfl

theorem tie_sustains (n : Nat) : (Tally.mk n n).passes .sustainChair (2 * n) = true := by
  simp [passes]

end Tally

/-- Overrides are explicit configuration, fixed during a session. -/
structure Rules where
  /-- Positive quorum size supplied by the governing rules. -/
  quorum : Nat
  /-- Denominator override for main motions; procedural thresholds stay fixed. -/
  ordinaryBasis : Denominator := .cast
  /-- Ordinary speech limit per person, question, and calendar day. -/
  speechesPerQuestion : Nat := 2
  /-- Maximum duration of an uninterrupted speech. -/
  speechSeconds : Nat := 600
  /-- Human-readable source of this assembly's configured rules. -/
  provenance : String := "RONR 12th edition; quorum supplied by governing rules"
  deriving DecidableEq, Repr

/-- Roster entries distinguish the right to vote from counting toward a quorum. -/
structure Member where
  /-- Stable roster identity. -/
  id : MemberId
  /-- Whether this member has the right to vote. -/
  votes : Bool := true
  /-- Whether this member's presence contributes to quorum. -/
  countsForQuorum : Bool := true
  deriving DecidableEq, Repr

/-- The session calendar is an explicit environment input. -/
structure Calendar where
  /-- Current civil date supplied by the host clock. -/
  today : Date
  /-- Monotone identifier of the current parliamentary session. -/
  session : Nat := 0
  /-- Monotone identifier of the current meeting. -/
  meeting : Nat := 0
  /-- Scheduled date of the next regular session. -/
  nextRegular : Date
  /-- Whether continuing membership permits ordinary carryover. -/
  termsContinue : Bool := true
  deriving DecidableEq, Repr

/-- Both dates are valid and the next regular date is not in the past. -/
def Calendar.Valid (c : Calendar) : Prop :=
  c.today.Valid ∧ c.nextRegular.Valid ∧ c.today.ordinal ≤ c.nextRegular.ordinal

instance (c : Calendar) : Decidable c.Valid := inferInstanceAs (Decidable (_ ∧ _))

end Parliament
