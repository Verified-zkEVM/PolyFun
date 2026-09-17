/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cursor.ReplayTree
public import PolyFunTest.PFunctor.FreeCursorOccurrenceExamples

/-! # Replay boundaries: empty branches, repeated answers, and restored prefixes -/

public section

namespace PFunctor.FreeM.Cursor

/-- A branch need not have a completed execution. -/
def emptyReplay : ReplayTree rootProgram :=
  .branch (.here _) 0 Fin.elim0 (fun i => Fin.elim0 i)

example (leaf : ReplayTree.Leaf emptyReplay) : False := by
  cases leaf with
  | branch i _ => exact Fin.elim0 i

/-- Different addresses can prescribe the same answers after a nonempty prefix. -/
def repeatedReplay : ReplayTree nestedProgram :=
  .branch nestedOccurrence 2 (fun _ => true) fun _ =>
    .branch (.here _) 1 (fun _ => false) fun _ => .leaf ⟨⟩

def firstLeaf : ReplayTree.Leaf repeatedReplay := .branch 0 (.branch 0 .leaf)

def secondLeaf : ReplayTree.Leaf repeatedReplay := .branch 1 (.branch 0 .leaf)

example : firstLeaf ≠ secondLeaf := by
  intro h
  have := ReplayTree.Leaf.branch.inj h
  simp at this

example : firstLeaf.path = secondLeaf.path := rfl

example : output nestedProgram firstLeaf.path = 210 := rfl

example : Path.trace nestedProgram firstLeaf.path =
    [⟨ExampleOp.noise, noiseOne⟩, ⟨ExampleOp.target, true⟩, ⟨ExampleOp.target, false⟩] := rfl

example : output nestedProgram firstLeaf.path = firstLeaf.result := firstLeaf.output_path

end PFunctor.FreeM.Cursor
