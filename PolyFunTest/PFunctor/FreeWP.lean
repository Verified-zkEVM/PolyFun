/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.WP

/-!
# Free-monad weakest-precondition canaries

These examples distinguish demonic and angelic operation specifications, pin
answer-dependent continuations, and exercise syntactic-to-semantic transport
through a nontrivial handler.
-/

@[expose] public section

namespace PolyFunTest.FreeWP

open PFunctor
open PFunctor.FreeM
open MonadAttach

/-- A single query with two observably different responses. -/
abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

/-- Two responses are combined, so the second continuation depends on the
first response. -/
def flipTwo : FreeM coinP Bool := do
  let a ← FreeM.lift (P := coinP) PUnit.unit
  let b ← FreeM.lift (P := coinP) PUnit.unit
  pure (a && b)

/-- Demonic semantics rejects a postcondition falsified by one response path. -/
example : ¬ wpFold (OpSpec.demonic coinP) flipTwo (fun out => out = true) := by
  change ¬ ∀ a b : Bool, (a && b) = true
  intro h
  exact Bool.noConfusion (h false false)

/-- Angelic semantics accepts the same postcondition by choosing `true` twice. -/
example : wpFold (OpSpec.angelic coinP) flipTwo (fun out => out = true) := by
  change ∃ a b : Bool, (a && b) = true
  exact ⟨true, true, rfl⟩

/-- A deterministic operation spec that always answers `true`. -/
def chooseTrueSpec : OpSpec coinP Prop :=
  fun _ continuation => continuation true

theorem chooseTrueSpec_mono : chooseTrueSpec.Mono :=
  fun _ _ _ h => h true

/-- `wpFold` preserves the answer-dependent continuation of both queries. -/
example : wpFold chooseTrueSpec flipTwo (fun out => out = true) := by
  change true && true = true
  rfl

/-- The induced ordered algebra computes the same nontrivial fold. -/
example :
    letI := chooseTrueSpec.toMAlgOrdered chooseTrueSpec_mono
    MAlgOrdered.wp flipTwo (fun out => out = true) := by
  rw [wp_toMAlgOrdered]
  change true && true = true
  rfl

/-! ## Handler semantics -/

/-- Interpret every query as the concrete answer `true`. -/
def chooseTrueHandler : Handler Id coinP :=
  fun _ => true

noncomputable local instance instIdOrdered : MAlgOrdered Id Prop where
  μ x := x
  μ_pure _ := rfl
  μ_bind_mono _ _ h x := h x

/-- The semantic WP observes the handler rather than quantifying over every
syntactic response. -/
example : wpVia chooseTrueHandler flipTwo (fun out => out = true) := by
  change true && true = true
  rfl

/-- The deterministic operation spec agrees exactly with the handler WP. -/
example : wpFold chooseTrueSpec flipTwo (fun out => out = true) =
    wpVia chooseTrueHandler flipTwo (fun out => out = true) := by
  apply wpFold_eq_wpVia
  intro _ continuation
  rfl

/-- Demonic syntax safely under-approximates the deterministic handler even
when the postcondition is not tautological. -/
example : wpFold (OpSpec.demonic coinP) flipTwo (fun out => out = true) ≤
    wpVia chooseTrueHandler flipTwo (fun out => out = true) := by
  apply wpFold_le_wpVia
  intro _ continuation hall
  exact hall true

/-! ## Coherence with support -/

/-- The demonic fold exposes a genuine negative support fact. -/
example : ¬ AllOutputs (fun out => out = true) flipTwo := by
  rw [← wpFold_demonic_iff_allOutputs]
  exact show ¬ (∀ a b : Bool, (a && b) = true) by
    intro h
    exact Bool.noConfusion (h false false)

/-- The angelic fold exposes a concrete reachable output. -/
example : SomeOutput (fun out => out = true) flipTwo := by
  rw [← wpFold_angelic_iff_someOutput]
  exact ⟨true, true, rfl⟩

end PolyFunTest.FreeWP
