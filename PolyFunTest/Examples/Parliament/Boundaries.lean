/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Examples.Parliament

/-! # Exact arithmetic, calendar, content, and public-interface boundaries -/

open Parliament

example : !(Tally.mk 0 0).passes .majority 0 := by decide
example : !(Tally.mk 0 0).passes .twoThirds 0 := by decide
example : !(Tally.mk 8 8).passes .majority 16 := by decide
example : (Tally.mk 9 8).passes .majority 17 := by decide
example : !(Tally.mk 67 34).passes .twoThirds 101 := by decide
example : (Tally.mk 68 33).passes .twoThirds 101 := by decide
example : (Tally.mk 1 0).passes .twoThirds 1 := by decide
example : (Tally.mk 0 0).passes .sustainChair 0 := by decide
example : (Tally.mk 3 3).passes .sustainChair 6 := by decide
example : !(Tally.mk 3 4).passes .sustainChair 7 := by decide

example : (Date.mk 2026 1 1).withinQuarter ⟨2026, 4, 30⟩ := by decide
example : !(Date.mk 2026 1 31).withinQuarter ⟨2026, 5, 1⟩ := by decide
example : (Date.mk 2025 11 30).withinQuarter ⟨2026, 2, 28⟩ := by decide
example : !(Date.mk 2026 1 1).withinQuarter ⟨2025, 12, 31⟩ := by decide
example : (Date.mk 2024 2 29).Valid := by decide
example : ¬(Date.mk 2026 2 29).Valid := by decide
example : ¬(Date.mk 2026 4 31).Valid := by decide
example : ¬(Date.mk 2026 0 1).Valid := by decide

example : WordEdit.apply ["a", "b"] ⟨1, 1, ["c"]⟩ = some ["a", "c"] := by decide
example : WordEdit.apply ["a", "b"] ⟨2, 0, ["c"]⟩ = some ["a", "b", "c"] := by decide
example : WordEdit.apply ["a", "b"] ⟨1, 2, []⟩ = none := by decide
example : applyWordSecondary ["a", "b"] ⟨0, 2, []⟩ (.narrow 1 1) = some ⟨1, 1, []⟩ := by decide

#check MeetingP
#check JudgmentSig
#check Script
#check boundedScript
#check meetingSystem
#check step_iff
#check replay_iff
#check LegalStep.substantiveDecision_quorum
#check MeetingPath.replays

example (rules : Rules) (s : AssemblyState wordDomain) (input : EnabledInput rules s) :
    (meetingSystem wordDomain rules).update s input = input.next := rfl

example (rules : Rules) (s : AssemblyState wordDomain) :
    boundedScript rules 0 s = IPFunctor.IFreeM.pure () := rfl
