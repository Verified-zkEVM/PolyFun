/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Dynamical.DynComputation.Termination

/-!
# Qualitative returning-computation termination examples

The main canary has one infinitely branching query. Answer `n` selects a
countdown of depth `n`, so every branch terminates but no natural-number fuel
bound covers every branch.
-/

@[expose] public section

open PFunctor

namespace PFunctor.DynSystem.DynComputation

universe uState uA uB uInput uOutput

def terminationUniverseCanary {p : PFunctor.{uA, uB}}
    {α : Type uInput} {β : Type uOutput}
    (M : DynComputation.{uState} p α β) (state : M.State)
    (termination : M.TerminatesFrom state) : FreeM p β :=
  M.toFreeMFrom state termination

theorem terminationSemanticsUniverseCanary {p : PFunctor.{uA, uB}}
    {α : Type uInput} {β : Type uOutput}
    (M : DynComputation.{uState} p α β) (state : M.State)
    (termination : M.TerminatesFrom state) :
    M.toDynSystem.behavior state =
      FreeM.toResumption (terminationUniverseCanary M state termination) :=
  M.behavior_eq_toResumption_toFreeMFrom state termination

abbrev natQuery : PFunctor.{0, 0} := purePower Nat

/-- A root query selects a countdown length. Countdown queries ignore their
answers and decrease the counter; zero returns. -/
def unboundedDepth : DynComputation natQuery Unit Unit where
  State := Option Nat
  toDynSystem :=
    (fun
      | none => Sum.inr PUnit.unit
      | some 0 => Sum.inl ()
      | some (_ + 1) => Sum.inr PUnit.unit) ⇆
    fun
      | none => fun answer => some answer
      | some 0 => PEmpty.elim
      | some (n + 1) => fun _ => some n
  init := fun _ => none

theorem unboundedDepth_view_root :
    unboundedDepth.view none =
      Sum.inr (⟨PUnit.unit, fun answer => some answer⟩ :
        natQuery.Obj (Option Nat)) := rfl

theorem unboundedDepth_view_zero :
    unboundedDepth.view (some 0) = Sum.inl () := rfl

theorem unboundedDepth_view_succ (n : Nat) :
    unboundedDepth.view (some (n + 1)) =
      Sum.inr (⟨PUnit.unit, fun _ => some n⟩ :
        natQuery.Obj (Option Nat)) := rfl

theorem unboundedDepth_countdown_terminates (n : Nat) :
    unboundedDepth.TerminatesFrom (some n) := by
  induction n with
  | zero =>
      exact unboundedDepth.terminatesFrom_return _ ()
        unboundedDepth_view_zero
  | succ n ih =>
      apply (unboundedDepth.terminatesFrom_query_iff _ PUnit.unit
        (fun _ => some n) (unboundedDepth_view_succ n)).mpr
      exact fun _ => ih

theorem unboundedDepth_terminates : unboundedDepth.TerminatesFrom none := by
  apply (unboundedDepth.terminatesFrom_query_iff _ PUnit.unit
    (fun answer => some answer) unboundedDepth_view_root).mpr
  exact unboundedDepth_countdown_terminates

theorem unboundedDepth_countdown_not_resolves (k : Nat) :
    ¬unboundedDepth.ResolvesIn k (some (k + 1)) := by
  induction k with
  | zero =>
      exact unboundedDepth.not_resolvesIn_query_zero _ PUnit.unit _
        (unboundedDepth_view_succ 0)
  | succ k ih =>
      intro h
      have hbranches :=
        (unboundedDepth.resolvesIn_query_succ_iff k _ PUnit.unit
          (fun _ => some (k + 1)) (unboundedDepth_view_succ (k + 1))).mp h
      change ∀ _ : Nat, unboundedDepth.ResolvesIn k (some (k + 1)) at hbranches
      exact ih (hbranches 0)

theorem unboundedDepth_has_no_uniform_bound (k : Nat) :
    ¬unboundedDepth.ResolvesIn k none := by
  cases k with
  | zero =>
      exact unboundedDepth.not_resolvesIn_query_zero _ PUnit.unit _
        unboundedDepth_view_root
  | succ k =>
      intro h
      have hbranches :=
        (unboundedDepth.resolvesIn_query_succ_iff k _ PUnit.unit
          (fun answer => some answer) unboundedDepth_view_root).mp h
      exact unboundedDepth_countdown_not_resolves k (hbranches (k + 1))

def countdownProgram : Nat → FreeM natQuery Unit
  | 0 => FreeM.pure ()
  | n + 1 => FreeM.liftBind PUnit.unit fun _ => countdownProgram n

def unboundedDepthProgram : FreeM natQuery Unit :=
  FreeM.liftBind PUnit.unit countdownProgram

theorem unboundedDepth_extract_countdown (n : Nat) :
    unboundedDepth.toFreeMFrom (some n)
      (unboundedDepth_countdown_terminates n) = countdownProgram n := by
  induction n with
  | zero =>
      rw [unboundedDepth.toFreeMFrom_return _ _ ()
        unboundedDepth_view_zero]
      rfl
  | succ n ih =>
      rw [unboundedDepth.toFreeMFrom_query _ _ PUnit.unit
        (fun _ => some n) (unboundedDepth_view_succ n)]
      change FreeM.liftBind (P := natQuery) (α := Unit) PUnit.unit _ =
        FreeM.liftBind (P := natQuery) (α := Unit) PUnit.unit _
      congr 1
      funext direction
      calc
        unboundedDepth.toFreeMFrom (some n) _ =
            unboundedDepth.toFreeMFrom (some n)
              (unboundedDepth_countdown_terminates n) :=
          unboundedDepth.toFreeMFrom_proof_irrel _ _ _
        _ = countdownProgram n := ih

theorem unboundedDepth_extract_root :
    unboundedDepth.toFreeMFrom none unboundedDepth_terminates =
      unboundedDepthProgram := by
  rw [unboundedDepth.toFreeMFrom_query _ _ PUnit.unit
    (fun answer => some answer) unboundedDepth_view_root]
  change FreeM.liftBind (P := natQuery) (α := Unit) PUnit.unit _ =
    FreeM.liftBind (P := natQuery) (α := Unit) PUnit.unit _
  congr 1
  funext answer
  exact (unboundedDepth.toFreeMFrom_proof_irrel _ _ _).trans
    (unboundedDepth_extract_countdown answer)

theorem unboundedDepth_program_semantics :
    unboundedDepth.toDynSystem.behavior none =
      FreeM.toResumption unboundedDepthProgram := by
  rw [unboundedDepth.behavior_eq_toResumption_toFreeMFrom none
    unboundedDepth_terminates, unboundedDepth_extract_root]

theorem unboundedDepth_terminates_from_program :
    unboundedDepth.TerminatesFrom none :=
  (unboundedDepth.terminatesFrom_iff_exists_behavior_eq_toResumption none).mpr
    ⟨unboundedDepthProgram, unboundedDepth_program_semantics⟩

theorem unboundedDepth_extract_has_no_uniform_bound (k : Nat) :
    ¬(unboundedDepth.toFreeMFrom none
      unboundedDepth_terminates).IsTotalRollBound k := by
  rw [← unboundedDepth.resolvesIn_iff_isTotalRollBound_toFreeMFrom k none
    unboundedDepth_terminates]
  exact unboundedDepth_has_no_uniform_bound k

/-! ## Qualitative sequencing -/

def terminalSecond : DynComputation natQuery Unit Nat :=
  ofFn fun _ => 7

theorem terminalSecond_terminates (input : Unit) :
    terminalSecond.TerminatesFrom (terminalSecond.init input) := by
  apply terminalSecond.terminatesFrom_return _ 7
  rfl

theorem unboundedThenTerminal_terminates :
    (unboundedDepth.seqComp terminalSecond).TerminatesFrom
      ((unboundedDepth.seqComp terminalSecond).init ()) :=
  unboundedDepth_terminates.seqComp_inl terminalSecond_terminates

example :
    (unboundedDepth.seqComp terminalSecond).toFreeMFrom
        (Sum.inl none)
        (unboundedDepth_terminates.seqComp_inl terminalSecond_terminates) =
      FreeM.bind unboundedDepthProgram fun _ => FreeM.pure 7 := by
  rw [toFreeMFrom_seqComp_inl unboundedDepth terminalSecond none
    unboundedDepth_terminates terminalSecond_terminates,
    unboundedDepth_extract_root]
  apply congrArg (FreeM.bind unboundedDepthProgram)
  funext value
  exact terminalSecond.toFreeMFrom_return _ _ 7 rfl

/-! Both phases below query. The first answer becomes an intermediate value
that changes the second phase's returned results, so exact extraction must
preserve both answer-dependent continuations and their handoff order. -/

def phaseOneProgram (_ : Unit) : FreeM natQuery Nat :=
  FreeM.liftBind PUnit.unit fun answer => FreeM.pure answer

def phaseTwoProgram (first : Nat) : FreeM natQuery Nat :=
  FreeM.liftBind PUnit.unit fun answer : Nat => FreeM.pure (first + answer)

def phaseOne : DynComputation natQuery Unit Nat :=
  ofFreeM phaseOneProgram

def phaseTwo : DynComputation natQuery Nat Nat :=
  ofFreeM phaseTwoProgram

theorem phaseOne_terminates (input : Unit) :
    phaseOne.TerminatesFrom (phaseOne.init input) :=
  phaseOne.terminatesFrom_of_behavior_eq_toResumption
    (phaseOneProgram input) (phaseOne.init input)
    (denote_ofFreeM phaseOneProgram input)

theorem phaseTwo_terminates (first : Nat) :
    phaseTwo.TerminatesFrom (phaseTwo.init first) :=
  phaseTwo.terminatesFrom_of_behavior_eq_toResumption
    (phaseTwoProgram first) (phaseTwo.init first)
    (denote_ofFreeM phaseTwoProgram first)

theorem phaseOne_extract (input : Unit) :
    phaseOne.toFreeMFrom (phaseOne.init input) (phaseOne_terminates input) =
      phaseOneProgram input := by
  apply FreeM.toResumption_injective
  exact (phaseOne.behavior_eq_toResumption_toFreeMFrom
    (phaseOne.init input) (phaseOne_terminates input)).symm.trans
      (denote_ofFreeM phaseOneProgram input)

theorem phaseTwo_extract (first : Nat) :
    phaseTwo.toFreeMFrom (phaseTwo.init first) (phaseTwo_terminates first) =
      phaseTwoProgram first := by
  apply FreeM.toResumption_injective
  exact (phaseTwo.behavior_eq_toResumption_toFreeMFrom
    (phaseTwo.init first) (phaseTwo_terminates first)).symm.trans
      (denote_ofFreeM phaseTwoProgram first)

theorem queriedPhases_terminate :
    (phaseOne.seqComp phaseTwo).TerminatesFrom
      ((phaseOne.seqComp phaseTwo).init ()) :=
  TerminatesFrom.seqComp_init phaseOne_terminates phaseTwo_terminates ()

example (first : Nat) :
    (phaseOne.seqComp phaseTwo).TerminatesFrom
      (Sum.inr (phaseTwo.init first)) :=
  (phaseTwo_terminates first).seqComp_inr

example (first : Nat) :
    (phaseOne.seqComp phaseTwo).toFreeMFrom
        (Sum.inr (phaseTwo.init first))
        (phaseTwo_terminates first).seqComp_inr =
      phaseTwoProgram first := by
  rw [toFreeMFrom_seqComp_inr phaseOne phaseTwo (phaseTwo.init first)
    (phaseTwo_terminates first), phaseTwo_extract]

example :
    (phaseOne.seqComp phaseTwo).toFreeMFrom
        ((phaseOne.seqComp phaseTwo).init ()) queriedPhases_terminate =
      FreeM.bind (phaseOneProgram ()) phaseTwoProgram := by
  change (phaseOne.seqComp phaseTwo).toFreeMFrom
      (Sum.inl (phaseOne.init ())) _ = _
  rw [toFreeMFrom_seqComp_inl phaseOne phaseTwo (phaseOne.init ())
    (phaseOne_terminates ()) phaseTwo_terminates, phaseOne_extract]
  apply congrArg (FreeM.bind (phaseOneProgram ()))
  funext first
  exact phaseTwo_extract first

example :
    (phaseOne.seqComp phaseTwo).toFreeM
        (fun input => TerminatesFrom.seqComp_init
          phaseOne_terminates phaseTwo_terminates input) =
      fun input => FreeM.bind (phaseOneProgram input) phaseTwoProgram := by
  have hOne : phaseOne.toFreeM phaseOne_terminates = phaseOneProgram := by
    funext input
    exact phaseOne_extract input
  have hTwo : phaseTwo.toFreeM phaseTwo_terminates = phaseTwoProgram := by
    funext first
    exact phaseTwo_extract first
  rw [toFreeM_seqComp phaseOne phaseTwo phaseOne_terminates
    phaseTwo_terminates, hOne, hTwo]

end PFunctor.DynSystem.DynComputation
