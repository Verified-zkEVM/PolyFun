/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.PatternRunsOnMatter.Display

/-!
# A bounded guessing program running on an input responder

This worked example presents a small program and its operating environment
independently. The program repeatedly performs `read` until it sees a target
value or exhausts its budget. The responder supplies a stream of input values
and records how much of the stream was consumed.

`Responder.runAgainstResult` executes the free program through the evaluated
Pattern-Runs-on-Matter construction. The examples below observe both the
program result and the responder state, and instantiate the general theorem
identifying that construction with ordinary state-handler execution.
-/

@[expose] public section

namespace PFunctor.PatternRunsOnMatterGuessing

inductive InputOperation where
  | read
  deriving DecidableEq

/-- An input operation is answered by one decimal digit. -/
abbrev Input : PFunctor :=
  ⟨InputOperation, fun _ => Fin 10⟩

/-- Read inputs until `target` appears, for at most `fuel` reads. -/
def guessUntil (target : Fin 10) : Nat → FreeM Input Bool
  | 0 => .pure false
  | fuel + 1 =>
      .liftBind .read fun input =>
        if input = target then .pure true else guessUntil target fuel

/-- The next stream value, with zero after the finite input is exhausted. -/
def currentInput : List (Fin 10) → Fin 10
  | [] => 0
  | input :: _ => input

/-- Consume one stream value, leaving an exhausted stream unchanged. -/
def consumeInput : List (Fin 10) → List (Fin 10)
  | [] => []
  | _ :: rest => rest

/-- A deterministic input stream presented as a stateful responder. -/
def inputResponder : Responder (List (Fin 10)) Input :=
  Responder.mk'
    (fun inputs _ => currentInput inputs)
    (fun inputs _ => consumeInput inputs)

/-- The evaluated Pattern-Runs-on-Matter action agrees with direct responder
execution for this concrete program and environment. -/
example (target : Fin 10) (fuel : Nat) (inputs : List (Fin 10)) :
    Responder.runAgainstResult inputResponder (guessUntil target fuel) inputs =
      inputResponder.runFree (guessUntil target fuel) inputs :=
  Responder.runAgainstResult_eq_runFree
    inputResponder (guessUntil target fuel) inputs

/-- A successful run stops as soon as it reads the target, leaving the
unconsumed suffix in the responder state. -/
example :
    Responder.runAgainstResult inputResponder
        (guessUntil 7 4) [2, 4, 7, 9] =
      (true, [9]) := by
  rw [Responder.runAgainstResult_eq_runFree]
  rfl

/-- An unsuccessful run consumes exactly its budget rather than the entire
available stream. -/
example :
    Responder.runAgainstResult inputResponder
        (guessUntil 7 3) [2, 4, 5, 9] =
      (false, [9]) := by
  rw [Responder.runAgainstResult_eq_runFree]
  rfl

/-- A zero-read program terminates without advancing its matter. -/
example :
    Responder.runAgainstResult inputResponder
        (guessUntil 7 0) [7, 9] =
      (false, [7, 9]) := by
  rw [Responder.runAgainstResult_eq_runFree]
  rfl

end PFunctor.PatternRunsOnMatterGuessing
