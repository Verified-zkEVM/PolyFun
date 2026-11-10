/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.WP
public import PolyFun.PFunctor.Free.WP.Upstream
public import PolyFun.PFunctor.Free.WP.Charge

/-!
# Free-monad weakest-precondition canaries

These examples distinguish demonic and angelic operation specifications, pin
answer-dependent continuations, and exercise syntactic-to-semantic transport
through a nontrivial handler. They also compare specs, compute a charge through
its induced algebra, and lift a `Prop` reading past universe 0.
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

theorem chooseTrueSpec_mono : chooseTrueSpec.Monotone :=
  fun _ _ _ h => h true

/-- `wpFold` preserves the answer-dependent continuation of both queries. -/
example : wpFold chooseTrueSpec flipTwo (fun out => out = true) := by
  change true && true = true
  rfl

/-- The induced core interpretation computes the same nontrivial fold. -/
example :
    ((chooseTrueSpec.toWPMonad chooseTrueSpec_mono).toWP Bool).wp flipTwo
      (fun out => out = true) estack⟨⟩ := by
  rw [OpSpec.toWPMonad_wp]
  change true && true = true
  rfl

/-! ## Comparing specs and their algebras -/

/-- The demonic spec is below the deterministic one, which is below the angelic one, so their
folds are ordered for every postcondition. -/
example (post : Bool → Prop) :
    wpFold (OpSpec.demonic coinP) flipTwo post → wpFold chooseTrueSpec flipTwo post :=
  wpFold_le_wpFold_of_le chooseTrueSpec_mono (fun _ _ h => h true) flipTwo post

example (post : Bool → Prop) :
    wpFold chooseTrueSpec flipTwo post → wpFold (OpSpec.angelic coinP) flipTwo post :=
  wpFold_le_wpFold_of_le' chooseTrueSpec_mono (fun _ _ h => ⟨true, h⟩) flipTwo post

/-- The comparison is strict on this program: the deterministic fold holds where the demonic
one fails. -/
example : wpFold chooseTrueSpec flipTwo (fun out => out = true) ∧
    ¬ wpFold (OpSpec.demonic coinP) flipTwo (fun out => out = true) :=
  ⟨rfl, fun h => Bool.noConfusion (h false false)⟩

/-- The unit charge, read through its induced algebra, counts the two calls of `flipTwo`. -/
example :
    letI := (OpSpec.charge fun _ : coinP.A => (1 : ℕ∞)).toMAlgOrdered (OpSpec.charge_mono _)
    MAlgOrdered.μ (flipTwo >>= fun _ => pure (0 : ℕ∞)) = 2 := by
  rw [toMAlgOrdered_μ_bind_pure]
  simp [flipTwo, wpFold_bind]
  rfl

/-- A pointwise larger charge folds to a larger cost. -/
example : wpFold (OpSpec.charge fun _ : coinP.A => (1 : ℕ∞)) flipTwo (fun _ => 0) ≤
    wpFold (OpSpec.charge fun _ : coinP.A => (2 : ℕ∞)) flipTwo (fun _ => 0) :=
  wpFold_le_wpFold_of_le (OpSpec.charge_mono _)
    (fun _ _ => add_le_add one_le_two le_rfl) flipTwo _

/-- `wpFold` is CSLib's fold. -/
example (post : Bool → Prop) :
    wpFold (OpSpec.demonic coinP) flipTwo post =
      FreeM.foldFreeM post (OpSpec.demonic coinP) flipTwo :=
  wpFold_eq_foldFreeM _ _ _

/-! ## Lifting the carrier -/

/-- The demonic reading over `ULift.{1} Prop`. -/
abbrev demonicULift : OpSpec coinP (ULift.{1} Prop) :=
  (OpSpec.demonic coinP).ulift

/-- The lifted demonic reading induces an algebra on programs with results in `Type 1`, which
`toMAlgOrdered` cannot build from the `Prop` reading itself. Its value is the demonic fold. -/
example :
    letI := demonicULift.toMAlgOrdered OpSpec.demonic_mono.ulift
    (MAlgOrdered.μ (FreeM.map ULift.up.{1} flipTwo >>= fun a =>
      pure (ULift.up (a.down = true)))).down ↔ ∀ a b : Bool, (a && b) = true := by
  rw [toMAlgOrdered_μ_bind_pure, wpFold_ulift]
  exact Iff.rfl

/-- Lifting a postcondition and folding the lifted spec lifts the fold. -/
example (Φ : OpSpec coinP Prop) (x : FreeM coinP Bool) (post : Bool → Prop) :
    wpFold Φ.ulift x (fun a => ULift.up.{2} (post a)) = ⟨wpFold Φ x post⟩ :=
  wpFold_ulift Φ x _

/-- Reading a lifted fold back is the original fold. -/
example (Φ : OpSpec coinP Prop) (x : FreeM coinP Bool) (post : Bool → ULift.{2} Prop) :
    (wpFold Φ.ulift x post).down = wpFold Φ x fun a => (post a).down := by
  simp

/-! ## Handler semantics -/

/-- Interpret every query as the concrete answer `true`. -/
def chooseTrueHandler : Handler Id coinP :=
  fun _ => true

/-- The semantic WP, core's `wp` of the interpreted program, observes the handler rather than
quantifying over every syntactic response. -/
example : Std.WP.wp (flipTwo.liftM chooseTrueHandler) (fun out => out = true)
    estack⟨⟩ := by
  change true && true = true
  rfl

/-- The deterministic operation spec agrees exactly with the handler WP. -/
example : wpFold chooseTrueSpec flipTwo (fun out => out = true) =
    Std.WP.wp (flipTwo.liftM chooseTrueHandler) (fun out => out = true)
      estack⟨⟩ := by
  apply wpFold_eq_wp_liftM
  intro _ continuation
  rfl

/-- Demonic syntax safely under-approximates the deterministic handler even
when the postcondition is not tautological. -/
example : wpFold (OpSpec.demonic coinP) flipTwo (fun out => out = true) ≤
    Std.WP.wp (flipTwo.liftM chooseTrueHandler) (fun out => out = true)
      estack⟨⟩ := by
  apply wpFold_le_wp_liftM
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
