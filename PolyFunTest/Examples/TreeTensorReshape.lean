/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.TreeTensorReshape
meta import Examples.Tutorials.TreeTensorReshape
meta import Mathlib.Algebra.Group.Int.Defs

/-!
# TensorType's five-entry tree

The left subtree has root 7 and leaves −42 and 46. The full tree has root 60 and right leaf 2.
Selecting 46 twice and 2 once sends the first two output weights back to the same leaf.
-/

public section

namespace Examples.TreeTensor.Test

example {α : Type*} (s : Shape) (x : Pos s → α) :
    (fun p => (flatten s x).get ((indexEquiv s).symm p)) = x := by
  simpa only [flattenEquiv_apply, flattenEquiv_symm_apply] using
    (flattenEquiv s α).symm_apply_apply x

example {α : Type*} (s : Shape) (y : Vector α (size s)) :
    flatten s (fun p => y.get ((indexEquiv s).symm p)) = y := by
  simpa only [flattenEquiv_apply, flattenEquiv_symm_apply] using
    (flattenEquiv s α).apply_symm_apply y

private def sampleShape : Shape := .node (.node .leaf .leaf) .leaf

private def sampleValues : Pos sampleShape → Int
  | .left (.left .atLeaf) => -42
  | .left .atNode => 7
  | .left (.right .atLeaf) => 46
  | .atNode => 60
  | .right .atLeaf => 2

private def sampleSelection : Fin 3 → Fin (size sampleShape) :=
  (#v[2, 2, 4] : Vector (Fin 5) 3).get

/-- In-order values, selected values, returned weights, and weights for the empty selection. -/
def fiveEntryReshapes : Array (Array Int) :=
  let values := flatten sampleShape sampleValues
  let weights := returnWeights sampleShape sampleSelection #v[2, 3, 7]
  let emptyWeights := returnWeights sampleShape Fin.elim0 (#v[] : Vector Int 0)
  #[values.toArray, (gather sampleSelection values).toArray,
    (flatten sampleShape weights.get).toArray, (flatten sampleShape emptyWeights.get).toArray]

/-- info: #[#[-42, 7, 46, 60, 2], #[46, 46, 2], #[0, 0, 5, 0, 7], #[0, 0, 0, 0, 0]] -/
#guard_msgs in
#eval fiveEntryReshapes

private def mirrorShape : Shape := .node .leaf (.node .leaf .leaf)

private def mirrorValues : Pos mirrorShape → Int
  | .left .atLeaf => 8
  | .atNode => -1
  | .right (.left .atLeaf) => 4
  | .right .atNode => 9
  | .right (.right .atLeaf) => -5

/-- A repeated internal node receives cancelling weights. The selector also reorders entries. -/
def mirrorReshape : Array (Array Int) :=
  let r := (#v[3, 0, 3, 4] : Vector (Fin 5) 4).get
  let weights := returnWeights mirrorShape r (#v[13, 6, -13, 7] : Vector Int 4)
  #[(gather r (flatten mirrorShape mirrorValues)).toArray,
    (flatten mirrorShape weights.get).toArray]

/-- info: #[#[9, 8, 9, -5], #[6, 0, 0, 0, 7]] -/
#guard_msgs in
#eval mirrorReshape

end Examples.TreeTensor.Test
