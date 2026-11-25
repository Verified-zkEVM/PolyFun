/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Hint

/-!
# Replaying incomparable partial handlers

Each hidden state answers only its own request. Together their answers settle an adaptive
program that neither state settles alone. A shared decoder must reproduce these settled
answers, whereas an exact decoder would also have to reproduce each failure.
-/

public section

namespace PolyFunTest.HandlerHint

open PFunctor Handler

/-- A Boolean request expects a Boolean answer. -/
abbrev Key : PFunctor := ⟨Bool, fun _ => Bool⟩

/-- Each state answers its own key with the other Boolean. -/
def partialAnswer (state : Bool) : Handler Option Key where
  toFun key :=
    if key = state then some (!state) else none

/-- Query the first answer. -/
def adaptive : FreeM Key Bool := do
  let next ← FreeM.lift (P := Key) false
  FreeM.lift (P := Key) next

example (state : Bool) : adaptive.liftM (partialAnswer state) = none := by
  cases state <;> rfl

/-- Pairwise consistency supplies one decoder for the two incomparable histories. -/
theorem exists_one_label : ∃ d : Unit → Handler Option Key,
    Hint.PreservesSettled partialAnswer (fun _ => ()) d := by
  apply (Hint.exists_preservesSettled_iff _ _).2
  intro t t' _ key b b' hb hb'
  cases t <;> cases t' <;> cases key <;> simp_all [partialAnswer]

/-- Every common decoder answers both requests, settling an additional adaptive execution. -/
theorem adaptive_settled_by_decoder {d : Unit → Handler Option Key}
    (hd : Hint.PreservesSettled partialAnswer (fun _ => ()) d) :
    adaptive.liftM (d ()) = some false := by
  have answers : d () = fun key => some (!key) := by
    funext key
    cases key
    · exact hd false false true rfl
    · exact hd true true false rfl
  rw [answers]
  rfl

/-- One request distinguishes the histories when a decoder must replay misses as well. -/
theorem no_exact_decoder : ¬ ∃ d : Unit → Handler Option Key,
    Hint.Valid (fun t a c => partialAnswer t a = c) (fun _ => ()) fun h => d h := by
  rintro ⟨d, hd⟩
  have runs := (Hint.exact_iff_liftM (P := Key) _ _ _).1 hd
  have collision := (runs false (FreeM.lift (P := Key) false)).trans
    (runs true (FreeM.lift (P := Key) false)).symm
  exact Option.some_ne_none true collision

/-- Two different settled answers to the same request prevent every shared decoder. -/
theorem conflicting_answers : ¬ ∃ d : Unit → Handler Option Key,
    Hint.PreservesSettled (fun t => ⟨fun _ => some t⟩) (fun _ => ()) d := by
  intro hd
  have consistent := (Hint.exists_preservesSettled_iff (P := Key) _ _).1 hd
  exact Bool.false_ne_true (consistent false true rfl false false true rfl rfl)

end PolyFunTest.HandlerHint
