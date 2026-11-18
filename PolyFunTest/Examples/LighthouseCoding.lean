/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.Lighthouse.Coding

/-! # Decoding and optimal alphabet sizes with only the lighthouse coding import -/

namespace PolyFunTest.LighthouseCoding

open PolyFunExamples.Lighthouse

example : IsLeast {k : ℕ | ∃ (encode : Fin 5 → Fin k) (decode : Fin k → Fin 5 → Fin 5),
    Recovers AdjacentClue encode decode} 3 := single_optimal

example : IsLeast {k : ℕ | ∃ (encode : Fin 5 × Fin 5 → Fin k)
    (decode : Fin k → Fin 5 × Fin 5 → Fin 5 × Fin 5), Recovers JointClue encode decode} 5 :=
  joint_optimal

/-- Label one selects the unique legal sighting at clues starting at four and zero. -/
public theorem decode_worked_pair : jointHint (4, 1) = 1 ∧ jointDecoder 1 (4, 0) = (4, 1) := by
  decide

/-- Generate the endpoints directly from the navigator's clues, including the wraparound edge.
The decoder must recover all four ordered sightings for each of the 25 clue pairs. -/
private def decodedSightings : List Bool := do
  let i ← List.finRange 5
  let j ← List.finRange 5
  let x ← [i, i + 1]
  let y ← [j, j + 1]
  return jointDecoder (jointHint (x, y)) (i, j) == (x, y)

example : decodedSightings.length = 100 ∧ decodedSightings.all id = true := by decide

end PolyFunTest.LighthouseCoding
