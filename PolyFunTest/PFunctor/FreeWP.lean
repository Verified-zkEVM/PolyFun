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

universe uA uB uX uY

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

/-! ## Admitted-response contracts -/

/-! The map and bind laws retain independent source and target result
universes, matching the underlying `FreeM` operations. -/

example {P : PFunctor.{uA, uB}} {X : Type uX} {Y : Type uY}
    (allows : (position : P.A) → P.B position → Prop)
    (accept : Y → Prop) (function : X → Y) (program : FreeM P X) :
    (FreeM.map function program).LeavesSatisfyUnder allows accept ↔
      program.LeavesSatisfyUnder allows (accept ∘ function) :=
  leavesSatisfyUnder_map_iff allows accept function program

example {P : PFunctor.{uA, uB}} {X : Type uX} {Y : Type uY}
    (allows : (position : P.A) → P.B position → Prop)
    (accept : Y → Prop) (program : FreeM P X) (next : X → FreeM P Y) :
    (FreeM.bind program next).LeavesSatisfyUnder allows accept ↔
      program.LeavesSatisfyUnder allows
        (fun result => (next result).LeavesSatisfyUnder allows accept) :=
  leavesSatisfyUnder_bind_iff allows accept program next

/-- Restricting the admitted answer set ignores a branch that would falsify
the postcondition. -/
example :
    (FreeM.lift (P := coinP) PUnit.unit).LeavesSatisfyUnder
      (fun _ answer => answer = true) (fun answer => answer = true) := by
  change ∀ answer : Bool, answer = true → answer = true
  exact fun _ h => h

/-- Admitting that same branch exposes the failing leaf. -/
example : ¬
    (FreeM.lift (P := coinP) PUnit.unit).LeavesSatisfyUnder
      (fun _ _ => True) (fun answer => answer = true) := by
  change ¬ ∀ answer : Bool, True → answer = true
  intro h
  exact Bool.noConfusion (h false trivial)

/-- Leaf conformance deliberately carries no progress assertion. -/
example :
    (FreeM.lift (P := coinP) PUnit.unit).LeavesSatisfyUnder
      (fun _ _ => False) (fun _ => False) := by
  change ∀ answer : Bool, False → False
  simp

/-- The unrestricted contract agrees with the canonical support judgment. -/
example (post : Bool → Prop) :
    flipTwo.LeavesSatisfyUnder (fun _ _ => True) post ↔ AllOutputs post flipTwo :=
  leavesSatisfyUnder_all_iff_allOutputs flipTwo post

/-! A dependent response canary for free-handler closure. -/

inductive MixedOp where
  | bit
  | trit

abbrev mixedP : PFunctor.{0, 0} where
  A := MixedOp
  B
    | .bit => Bool
    | .trit => Fin 3

def mixedAllows : (position : mixedP.A) → mixedP.B position → Prop
  | .bit, _ => True
  | .trit, answer => answer.val ≤ 1

def mixedHandler : (position : mixedP.A) → FreeM coinP (mixedP.B position)
  | .bit => FreeM.lift PUnit.unit
  | .trit => FreeM.liftBind PUnit.unit fun answer =>
      pure (if answer then (1 : Fin 3) else 0)

def mixedProgram : FreeM mixedP Nat :=
  FreeM.liftBind .trit fun answer => pure answer.val

theorem mixedHandler_conforms (position : mixedP.A) :
    (mixedHandler position).LeavesSatisfyUnder (fun _ _ => True)
      (mixedAllows position) := by
  cases position with
  | bit =>
      unfold mixedHandler
      change ∀ answer : Bool, True → True
      simp
  | trit =>
      unfold mixedHandler
      change ∀ answer : Bool, True → (if answer then (1 : Fin 3) else 0).val ≤ 1
      intro answer _
      cases answer <;> decide

/-- Free-handler interpretation preserves a genuinely dependent answer
contract through a nontrivial inner query. -/
example :
    (mixedProgram.liftM mixedHandler).LeavesSatisfyUnder
      (fun _ _ => True) (fun result => result ≤ 1) := by
  apply leavesSatisfyUnder_liftM mixedHandler mixedAllows (fun _ _ => True)
    (fun result => result ≤ 1) mixedHandler_conforms mixedProgram
  change ∀ answer : Fin 3, answer.val ≤ 1 → answer.val ≤ 1
  exact fun _ h => h

end PolyFunTest.FreeWP
