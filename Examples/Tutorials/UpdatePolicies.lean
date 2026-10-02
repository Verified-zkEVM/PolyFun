/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.WP

/-! # Update policies: all responses versus a particular interpreter

A proposed bounded update separates syntactic safety, an assumption on allowed answers, and
execution under one chosen handler. A demonic policy quantifies over every permitted answer;
one successful run does not prove that policy. Empty policies make partial-correctness claims
vacuous and do not establish progress. This tutorial uses the public logic API, not Std.Do.
-/

@[expose] public section

namespace PolyFunExamples.UpdatePolicies

open PFunctor

/-- Ask for a proposed value, supplying the maximum acceptable value as the request. -/
abbrev Proposal : PFunctor := ⟨Nat, fun _ => Nat⟩

/-- A policy on the environment's answers, not a runtime validator. -/
def allowed (maximum answer : Nat) : Prop := answer ≤ maximum

/-- A total validator clamps an arbitrary proposal before returning the update. -/
def checked (maximum : Nat) : FreeM Proposal Nat :=
  FreeM.liftBind maximum fun answer => pure (min answer maximum)

/-- The validator is safe against every typed response, with no honesty assumption. -/
theorem checked_safe (maximum : Nat) :
    (checked maximum).wpFold (OpSpec.demonic Proposal) (· ≤ maximum) := by
  simp only [checked, FreeM.wpFold_liftBind, OpSpec.demonic, FreeM.wpFold_pure]
  exact fun answer => Nat.min_le_right answer maximum

/-- Without a validator the same guarantee needs an explicit response policy. -/
theorem proposed_safe_under_policy (maximum : Nat) :
    (FreeM.lift (P := Proposal) maximum).wpFold (OpSpec.demonicUnder allowed)
      (· ≤ maximum) := by
  rw [FreeM.wpFold_lift]
  exact fun _ h => h

/-- Reachability states precisely what the policy admits. -/
theorem proposal_reachable (maximum value : Nat) :
    value ∈ (FreeM.lift (P := Proposal) maximum).reachableUnder allowed ↔ value ≤ maximum := by
  rw [FreeM.reachableUnder_lift]
  rfl

/-- Every chosen pure handler is safe for the checked program, regardless of its policy. -/
theorem checked_run_safe (handler : Handler Id Proposal) (maximum : Nat) :
    ((checked maximum).liftM handler).run ≤ maximum :=
  Nat.min_le_right (handler maximum) maximum

/-- The raw program's guarantee is relative to its handler satisfying the response policy. -/
theorem proposed_run_safe (handler : Handler Id Proposal)
    (compliant : ∀ maximum, allowed maximum (handler maximum)) (maximum : Nat) :
    ((FreeM.lift (P := Proposal) maximum).liftM handler).run ≤ maximum := compliant maximum

/-- One deliberately noncompliant handler; checking still protects the result. -/
def oversized : Handler Id Proposal := fun maximum => maximum + 7

example : (checked 10).liftM oversized = 10 := rfl
example : (FreeM.lift (P := Proposal) 10).liftM oversized = 17 := rfl

/-- No admitted answer means vacuous safety, not an executable progress guarantee. -/
theorem empty_policy :
    (FreeM.lift (P := Proposal) 10).wpFold (OpSpec.demonicUnder (fun _ _ => False))
      (fun _ => False) := by
  rw [FreeM.wpFold_lift]
  exact fun _ impossible => impossible.elim

end PolyFunExamples.UpdatePolicies
