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

/-! ## Heterogeneous answers and continuation-dependent branch counts

A fixed setup response is restored before each replay. The next response selects
a subtree with either two or three leaves, with a different answer type at that node.
-/

namespace PFunctor.FreeM.Cursor.HeterogeneousReplay
open PFunctor PFunctor.FreeM PFunctor.FreeM.Cursor

inductive Operation where
  | setup | first | second

@[expose]
def interface : PFunctor.{0, 0} := ⟨Operation, fun
  | .setup => Bool
  | .first => Bool
  | .second => Fin 3⟩

@[expose]
def finish (setup first : Bool) (second : Fin 3) : FreeM interface (Bool × Bool × Fin 3) :=
  pure (setup, first, second)

@[expose]
def suffix (setup first : Bool) : FreeM interface (Bool × Bool × Fin 3) :=
  .liftBind .second (finish setup first)

@[expose]
def afterSetup (setup : Bool) : FreeM interface (Bool × Bool × Fin 3) :=
  .liftBind .first (suffix setup)

@[expose]
def program : FreeM interface (Bool × Bool × Fin 3) :=
  .liftBind .setup afterSetup

@[expose]
def firstOccurrence (setup : Bool) : Occurrence Operation.first program 0 := by
  change Occurrence Operation.first (FreeM.liftBind (P := interface) Operation.setup afterSetup) 0
  refine .stepOther (by intro h; cases h) setup ?_
  change Occurrence Operation.first
    (FreeM.liftBind (P := interface) Operation.first (suffix setup)) 0
  exact Occurrence.here (P := interface) (target := Operation.first) (suffix setup)

@[expose]
def childArity (first : Bool) : Nat := if first then 3 else 2

@[expose]
def secondAnswer (first : Bool) (i : Fin (childArity first)) : Fin 3 :=
  ⟨i.val, by cases first <;> simp_all [childArity] <;> omega⟩

@[expose]
def childTree (setup first : Bool) : ReplayTree (suffix setup first) := by
  change ReplayTree (FreeM.liftBind (P := interface) Operation.second (finish setup first))
  refine .branch (target := Operation.second)
    (Occurrence.here (P := interface) (target := Operation.second) (finish setup first))
    (childArity first) (secondAnswer first) (fun i => ?_)
  change ReplayTree (pure (setup, first, secondAnswer first i))
  exact .leaf ⟨⟩

@[expose]
def firstAnswer (i : Fin 2) : Bool := i.val == 1

/-- The setup is held fixed; the first challenge fans out into two or three second challenges. -/
@[expose]
def exampleTree (setup : Bool) : ReplayTree program :=
  .branch (firstOccurrence setup) 2 firstAnswer
    (fun i => by
      change ReplayTree (suffix setup (firstAnswer i))
      exact childTree setup (firstAnswer i))

@[expose]
def exampleLeaf (setup : Bool) (i : Fin 2)
    (j : Fin (childArity (firstAnswer i))) : ReplayTree.Leaf (exampleTree setup) := by
  unfold exampleTree
  refine .branch i ?_
  change ReplayTree.Leaf (childTree setup (firstAnswer i))
  unfold childTree
  exact .branch j .leaf

theorem example_output (setup : Bool) (i : Fin 2)
    (j : Fin (childArity (firstAnswer i))) :
    output program (exampleLeaf setup i j).path =
      (setup, firstAnswer i, secondAnswer (firstAnswer i) j) := rfl

theorem example_trace (setup : Bool) (i : Fin 2)
    (j : Fin (childArity (firstAnswer i))) :
    Path.trace program (exampleLeaf setup i j).path =
      [⟨Operation.setup, setup⟩, ⟨Operation.first, firstAnswer i⟩,
       ⟨Operation.second, secondAnswer (firstAnswer i) j⟩] := rfl

theorem different_branch_counts :
    childArity (firstAnswer 0) = 2 ∧ childArity (firstAnswer 1) = 3 := by
  decide

end PFunctor.FreeM.Cursor.HeterogeneousReplay
