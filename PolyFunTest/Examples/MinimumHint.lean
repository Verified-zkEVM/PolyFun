/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.FerryCrossing

/-!
# Independent exhaustive checks for minimum hints

Each side has a baseline move that pays zero and a second move with an arbitrary binary
observation at each of two states. The oracle tries every labeled signal and every labeled
decoder, including unused labels. It tests their behavior directly on the observations.
-/

namespace PolyFunTest.MinimumHint

open PolyFunExamples.Bargaining.Replay

private def bits : List Bool := [false, true]

private def rows : List (Bool × Bool) := bits.flatMap fun x => bits.map fun y => (x, y)

private def readRow (row : Bool × Bool) (x : Bool) : Bool :=
  if x then row.2 else row.1

private def table (s t : Bool × Bool) : Board Bool Bool Bool Bool where
  opening _ := false
  source state move := move && readRow s state
  target state move := move && readRow t state
  defaultMove := false

local instance : FinEnum Bool := FinEnum.ofNodupList [false, true]
  (by intro x; cases x <;> decide) (by decide)

/-- Reward each of the two observations in turn. These tests cover either direction of strict
preference. Exact mode simply compares the two actual observations. -/
private def preserves (mode : Mode) (opening source target : Bool) : Bool :=
  match mode with
  | .exact => source == target
  | .gain => bits.all fun prize => !(opening != prize && source == prize) || target == prize

private def signals (k : Nat) : List (Bool → Fin k) :=
  (List.finRange k).flatMap fun x => (List.finRange k).map fun y state => if state then y else x

/-- Each new hint label adds an independent two-bit decoder row. -/
private def decoders : (k : Nat) → List (Fin k → Bool → Bool)
  | 0 => [fun x => x.elim0]
  | k + 1 => (decoders k).flatMap fun tail => rows.map fun row => Fin.cases (readRow row) tail

/-- Execute the selected target move at each state and compare its actual observation. -/
private def replayDecoder {T B C H : Type} (mode : Mode) (board : Board T B C Bool)
    (states : List T) (moves : List B) (h : T → H) (d : H → B → C) : Bool :=
  states.all fun t => moves.all fun b =>
    preserves mode (board.opening t) (board.source t b) (board.target t (d (h t) b))

private def feasible (mode : Mode) (board : Board Bool Bool Bool Bool) (k : Nat) : Bool :=
  (signals k).any fun h => (decoders k).any (replayDecoder mode board bits bits h)

/-- Compare the solver and all its certificates with the exhaustive binary-board oracle. -/
public def agrees (mode : Mode) : Bool := rows.all fun s => rows.all fun t =>
  let board := table s t
  let result := minimumHint mode board
  let size := result.size?
  let replayed := match result with
    | .optimal _ h d .. => replayDecoder mode board bits bits h d
    | .impossible state move _ => bits.all fun target =>
      !preserves mode (board.opening state) (board.source state move) (board.target state target)
  let sizes := [0, 1, 2]
  replayed && (size == sizes.find? (feasible mode board)) && sizes.all fun k =>
    feasible mode board k == size.any (fun n => n ≤ k)

example : rows.length = 4 ∧ [0, 1, 2].map (fun k => (signals k).length) = [0, 1, 4] ∧
    [0, 1, 2].map (fun k => (decoders k).length) = [1, 4, 16] := by decide

example : agrees .gain = true := by decide
example : agrees .exact = true := by decide

private def noStates : Board (Fin 0) Bool Bool Bool :=
  ⟨Fin.elim0, Fin.elim0, Fin.elim0, false⟩

private def noMoves : Board (Fin 1) (Fin 0) Bool Bool :=
  ⟨fun _ => false, fun _ => Fin.elim0, fun _ c => c, false⟩

/-- With no states the alphabet can be empty. With one state it needs one label even when the
source has no moves. -/
example (mode : Mode) : (minimumHint mode noStates).size? = some 0 ∧
    (minimumHint mode noMoves).size? = some 1 := by cases mode <;> decide

/-- Changing the opening in two different ways can help different payoff functions. -/
private def threeObservations : Board Unit Unit Unit (Fin 3) :=
  ⟨fun _ => 0, fun _ _ => 1, fun _ _ => 2, ()⟩

example (mode : Mode) : (minimumHint mode threeObservations).size? = none := by
  cases mode <;> decide

/-- At state zero the only target move misses the source outcome. The other states
admit a translation. Returning the offending state and move needs no partition enumeration. -/
private def blockedAtZero : Board (Fin 12) (Fin 1) (Fin 1) Bool :=
  ⟨fun _ => false, fun t _ => t == 0, fun _ _ => false, 0⟩

private def identifiesBlockedState (mode : Mode) : Bool :=
  match minimumHint mode blockedAtZero with
  | .optimal .. => false
  | .impossible t b _ =>
    t == 0 && b == 0 && !(preserves mode (blockedAtZero.opening t)
      (blockedAtZero.source t b) (blockedAtZero.target t 0))

example (mode : Mode) : identifiesBlockedState mode = true := by cases mode <;> decide

open PolyFunExamples.Bargaining.Ferry (twoTides)

/-- The explicit-list search accepts repeated entries and public names in an infinite type.
Replay the result at the two names that the ferryman can actually send. -/
private def replaysSparseHints (mode : Mode) : Bool :=
  let h (t : Fin 2) : Nat := if t = 0 then 10 else 20
  match search mode twoTides h [1, 0, 1] [1, 1, 0] [2, 2, 0, 1]
      (by decide +revert) (by decide +revert) (by decide +revert) with
  | .success d _ => replayDecoder mode twoTides (List.finRange 2) (List.finRange 2) h d
  | .failure _ => false

example (mode : Mode) : replaysSparseHints mode = true := by cases mode <;> decide

private def replaysMinimum (mode : Mode) : Bool :=
  match minimumHint mode twoTides with
  | .optimal k h d .. =>
    k == 2 && replayDecoder mode twoTides (List.finRange 2) (List.finRange 2) h d
  | .impossible .. => false

private def replaysRevealedTide (mode : Mode) : Bool :=
  match MinimumHint.searchHints mode twoTides (id : Fin 2 → Fin 2) with
  | .success d _ => replayDecoder mode twoTides (List.finRange 2) (List.finRange 2) id d
  | .failure _ => false

/-- Every candidate channel, including waiting, must fail at the tide actually returned for it. -/
private def replaysHiddenTide (mode : Mode) : Bool :=
  let h (_ : Fin 2) := false
  match MinimumHint.searchHints mode twoTides h with
  | .success .. => false
  | .failure o =>
    o.move == 1 && (o.refute 1 != o.refute 2) && (List.finRange 3).all fun c =>
      let t := o.refute c
      h t == h o.hintState &&
        !preserves mode (twoTides.opening t) (twoTides.source t o.move) (twoTides.target t c)

example (mode : Mode) : replaysMinimum mode = true ∧
    replaysRevealedTide mode = true ∧ replaysHiddenTide mode = true := by
  cases mode <;> decide

end PolyFunTest.MinimumHint
