/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.LighthouseCounting

/-! # Two sightings, five signals, and recovery on all legal clues -/

namespace PolyFunTest.Lighthouse

open PolyFunExamples.Bargaining.Replay.Lighthouse
open PolyFunExamples.Bargaining.Replay (minimumHint)

/-- Generate the endpoints directly from the navigator's clues, including the wraparound edge.
The decoder must recover all four ordered sightings for each of the 25 clue pairs. -/
private def decodedSightings : List Bool := do
  let i ← List.finRange 5
  let j ← List.finRange 5
  let x ← [i, i + 1]
  let y ← [j, j + 1]
  return jointDecoder (jointHint (x, y)) (i, j) == (x, y)

example : decodedSightings.length = 100 ∧ decodedSightings.all id = true := by decide

example : (do
    let joint ← (minimumHint .gain jointBoard).size?
    let single ← (minimumHint .gain singleBoard).size?
    return decide (joint < single * single)) = some true := by
  rw [minimum_joint, minimum_single]
  rfl

/-- The executable three-message code supplies a Mathlib coloring with the same labels. -/
public theorem singleHint_coloring : ∃ c : (confusabilityGraph AdjacentClue).Coloring (Fin 3),
    (c : Fin 5 → Fin 3) = singleHint :=
  (exists_valid_iff_coloring 0 AdjacentClue singleHint).1 ⟨singleDecoder, single_valid⟩

end PolyFunTest.Lighthouse
