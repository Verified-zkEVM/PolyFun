/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.Instances
public import PolyFun.Interaction.Execution.ReactiveNetwork.Budget

/-!
# Global budgets and productive unbounded feedback

A countdown consumes its certified number of actual token activations. Two finite-state
receive/send actors each have a two-operation local reaction, but their closed feedback
network keeps exchanging packets forever. A failing effect interpreter separately tests the
certificate's progress requirement.
-/

public section

namespace Interaction.Execution.ReactiveNetwork.BudgetTests

open PFunctor ReactiveProcess DynSystem MonadAttach

@[expose] def noEffect : PFunctor.{0, 0} := ⟨Empty, Empty.elim⟩

@[expose] def countdownStep : ℕ → Outcome Unit ⊕ (signature noEffect PortBoundary.empty).Obj ℕ
  | 0 => .inl (.returned ())
  | n + 1 => .inr ⟨.tick, fun _ => n⟩

@[expose] def countdown (n : ℕ) : Network Unit PortBoundary.empty Unit where
  effect _ := noEffect
  ports _ := PortBoundary.empty
  component _ := DynComputation.ofStep countdownStep (fun _ => n)
  route _ packet := packet.1.elim
  ingress packet := packet.1.elim
  environment := ()

def countdownImpl (n : ℕ) :
    (node : Unit) → Handler (StateT Unit Id) ((countdown n).effect node) :=
  fun _ operation => operation.elim

attribute [local implicit_reducible] countdown countdownStep noEffect signature Response

/-- The local counter is a global rank because there is only one active countdown. -/
def countdownBudget (n : ℕ) : TokenBudgetCertificate (countdownImpl n) (fun _ => True) where
  rank state := state.localState ()
  zero state _ hz := by
    refine ⟨.returned (), ?_⟩
    simp [outcome, countdown, DynComputation.view_ofStep, hz, countdownStep]
  preserves _ _ _ _ := trivial
  decreases state next _ hout hstep := by
    have heq := Id.canReturn_iff.mp hstep
    cases state.focus
    cases hs : state.localState () with
    | zero => simp [outcome, countdown, DynComputation.view_ofStep, hs, countdownStep] at hout
    | succ n =>
      rw [← heq]
      simp [activate, countdown, DynComputation.view_ofStep, hs, countdownStep]
  progress state _ := ⟨_, Id.canReturn_iff.mpr rfl⟩

/-- The certificate proves actual completion at every initial countdown size. -/
example (n : ℕ) :
    ∃ value, outcome () (runToken (m := Id) (countdownImpl n) n
      (initial (countdown n) ())).run = some value :=
  (countdownBudget n).runToken_terminal n _ _ trivial (Nat.le_refl _) (Id.canReturn_iff.mpr rfl)

/-- Completion retains the exact consumed activation count. -/
example (n : ℕ) :
    (runToken (m := Id) (countdownImpl n) n (initial (countdown n) ())).run.elapsed = n := by
  simpa [initial] using elapsed_runToken (countdownImpl n) n
    (initial (countdown n) ()) _ (Id.canReturn_iff.mpr rfl)

@[expose] def unitPort : Interface := ⟨Unit, fun _ => Unit⟩
@[expose] def loopPorts : PortBoundary := ⟨unitPort, unitPort⟩

@[expose] def loopStep : Bool → Outcome Unit ⊕ (signature noEffect loopPorts).Obj Bool
  | false => .inr ⟨.receive, fun _ => true⟩
  | true => .inr ⟨.send ⟨(), ()⟩, fun _ => false⟩

@[expose] def feedback : Network Bool PortBoundary.empty Unit where
  effect _ := noEffect
  ports _ := loopPorts
  component node := DynComputation.ofStep loopStep (fun _ => !node)
  route node packet := .inl ⟨!node, packet⟩
  ingress packet := packet.1.elim
  environment := false

def feedbackImpl : (node : Bool) → Handler (StateT Unit Id) (feedback.effect node) :=
  fun _ operation => operation.elim

attribute [local implicit_reducible] feedback loopStep loopPorts unitPort

/-- A local receive/send reaction has exactly two polynomial operations. -/
example : loopStep false = .inr ⟨.receive, fun _ => true⟩ ∧
    loopStep true = .inr ⟨.send ⟨(), ()⟩, fun _ => false⟩ := ⟨rfl, rfl⟩

/-- Every local control state in the feedback network is unfinished. -/
theorem feedback_unfinished (state : State feedback Unit) : outcome false state = none := by
  cases hs : state.localState false <;>
    simp [outcome, feedback, DynComputation.view_ofStep, hs, loopStep]

/-- Four productive token activations exchange two packets and restore the private control state. -/
theorem feedback_round (elapsed : ℕ) :
    runToken feedbackImpl 4 { initial feedback () with elapsed } =
      (pure { initial feedback () with elapsed := elapsed + 4 } : Id (State feedback Unit)) := by
  have hstate : Function.update (Function.update
      (Function.update (fun id : Bool => !id) false false) true false) false true =
      (fun id : Bool => !id) := by
    funext node
    cases node <;> rfl
  simp [runToken, activate, feedback, initial, DynComputation.view_ofStep, loopStep,
    dispatch, Function.update, Nat.add_assoc, hstate]

/-- There are arbitrarily many complete packet-exchange rounds, with all their cost retained. -/
theorem feedback_rounds (rounds : ℕ) :
    runToken feedbackImpl (4 * rounds) (initial feedback ()) =
      (pure { initial feedback () with elapsed := 4 * rounds } : Id (State feedback Unit)) := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    rw [Nat.mul_succ, runToken_add, ih]
    simp only [pure_bind]
    exact feedback_round _

/-- Constant-size local reactions do not supply any global termination budget. -/
theorem feedback_has_no_budget :
    ¬ Nonempty (TokenBudgetCertificate feedbackImpl (fun _ => True)) := by
  rintro ⟨certificate⟩
  obtain ⟨value, hvalue⟩ := certificate.runToken_terminal
    (certificate.rank (initial feedback ())) (initial feedback ()) _ trivial
    (Nat.le_refl _) (Id.canReturn_iff.mpr rfl)
  change outcome false _ = some value at hvalue
  rw [feedback_unfinished] at hvalue
  cases hvalue

@[expose] def failingNetwork : Network Unit PortBoundary.empty Unit where
  effect _ := ⟨Unit, fun _ => Unit⟩
  ports _ := PortBoundary.empty
  component _ := DynComputation.ofFreeM fun _ =>
    .liftBind (.effect ()) fun _ => .pure (.returned ())
  route _ packet := packet.1.elim
  ingress packet := packet.1.elim
  environment := ()

def failingImpl :
    (node : Unit) → Handler (StateT Unit Option) (failingNetwork.effect node) :=
  fun _ _ _ => none

/-- An interpreter with no possible next state cannot inhabit the progress-bearing certificate. -/
example : ¬ Nonempty (TokenBudgetCertificate failingImpl (fun _ => True)) := by
  rintro ⟨certificate⟩
  obtain ⟨next, hnext⟩ := certificate.progress (initial failingNetwork ()) trivial
  change CanReturn (none : Option (State failingNetwork Unit)) next at hnext
  simp at hnext

end Interaction.Execution.ReactiveNetwork.BudgetTests
