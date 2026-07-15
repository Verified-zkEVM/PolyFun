/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Cursor

/-! # Cursor examples for dependent free polynomial programs -/

@[expose] public section

universe uA uB v

namespace PFunctor.FreeM.CursorExamples

/-- Cursor construction keeps all three relevant universes independent. -/
example {P : PFunctor.{uA, uB}} {α : Type v} (program : FreeM P α) :
    Cursor program :=
  Cursor.root program

inductive Command
  | choose
  | select (wide : Bool)
  deriving DecidableEq, Repr

/-- The answer type genuinely depends on the command. -/
def Answer : Command → Type
  | .choose => Bool
  | .select true => Fin 2
  | .select false => PUnit

def Interface : PFunctor where
  A := Command
  B := Answer

def afterIndex (index : Fin 2) : FreeM Interface Nat :=
  .liftBind (.select false) fun _ => .pure (10 + index.val)

def afterChoice : Bool → FreeM Interface Nat
  | false => .pure 7
  | true => .liftBind (.select true) afterIndex

def program : FreeM Interface Nat :=
  .liftBind .choose afterChoice

def selectedIndex : Fin 2 := ⟨1, by omega⟩

/-- An internal cursor stops after choosing the nontrivial dependent branch. -/
def internal : Cursor program :=
  Cursor.down true (Cursor.root (afterChoice true))

example : internal.residual = afterChoice true := rfl

example : internal.length = 1 := rfl

example : internal.trace = [⟨Command.choose, true⟩] := rfl

/-- A second edge selects an answer within the `Fin 2` branch. -/
def indexEdge : Cursor.Edge internal.residual :=
  Cursor.Edge.down selectedIndex

def afterIndexCursor : Cursor program :=
  internal.comp indexEdge.toCursor

/-- The final edge has the distinct answer type `PUnit`. -/
def unitEdge : Cursor.Edge afterIndexCursor.residual :=
  Cursor.Edge.down PUnit.unit

def trueLeaf : Cursor program :=
  afterIndexCursor.comp unitEdge.toCursor

example : trueLeaf.residual = FreeM.pure 11 := rfl

example : trueLeaf.length = 3 := rfl

example : trueLeaf.trace =
    [⟨Command.choose, true⟩, ⟨Command.select true, selectedIndex⟩,
      ⟨Command.select false, PUnit.unit⟩] := rfl

def truePath : Path program :=
  ⟨true, selectedIndex, PUnit.unit, ⟨⟩⟩

def falsePath : Path program :=
  ⟨false, ⟨⟩⟩

example : internal.plug (⟨selectedIndex, PUnit.unit, ⟨⟩⟩ : Path internal.residual) =
    truePath := rfl

example : Path.trace program truePath = trueLeaf.trace := by
  change Path.trace program
      (trueLeaf.plug (⟨⟩ : Path trueLeaf.residual)) = trueLeaf.trace
  rw [Cursor.trace_plug]
  rfl

example : FreeM.map (output program) (withPath program) = program := by
  exact map_output_withPath program

example : Cursor.ofPath program truePath = trueLeaf := rfl

def trueTerminal : Cursor.Terminal program :=
  Cursor.terminalOfPath program truePath

def falseTerminal : Cursor.Terminal program :=
  Cursor.terminalOfPath program falsePath

example : trueTerminal.output = 11 := rfl

example : falseTerminal.output = 7 := rfl

example : trueTerminal.output ≠ falseTerminal.output := by decide

example : Cursor.pathOfTerminal trueTerminal = truePath := by simp [trueTerminal]

example : Cursor.pathOfTerminal falseTerminal = falsePath := by simp [falseTerminal]

example : Cursor.terminalOfPath program (Cursor.pathOfTerminal trueTerminal) =
    trueTerminal := by simp

example : Cursor.terminalEquivPath program trueTerminal = truePath := by
  simp [Cursor.terminalEquivPath, trueTerminal]

/-! The producer tests below name the public algebraic laws explicitly, so
their availability and simp orientation remain part of the regression surface. -/

example : (Cursor.root program).comp internal = internal := by
  exact Cursor.root_comp internal

example : internal.comp (Cursor.root internal.residual) = internal := by
  exact Cursor.comp_root internal

example : (internal.comp indexEdge.toCursor).comp unitEdge.toCursor =
    internal.comp (indexEdge.toCursor.comp unitEdge.toCursor) := by
  exact Cursor.comp_assoc internal indexEdge.toCursor unitEdge.toCursor

example : trueLeaf.length = internal.length + indexEdge.toCursor.length +
    unitEdge.toCursor.length := by
  simp only [trueLeaf, afterIndexCursor, Cursor.length_comp]

example : trueLeaf.trace =
    List.append (List.append internal.trace indexEdge.toCursor.trace)
      unitEdge.toCursor.trace := by
  simp only [trueLeaf, afterIndexCursor, Cursor.trace_comp]

example (path : Path unitEdge.residual) :
    (afterIndexCursor.comp unitEdge.toCursor).plug path =
      afterIndexCursor.plug (unitEdge.toCursor.plug path) := by
  exact Cursor.plug_comp afterIndexCursor unitEdge.toCursor path

example : trueLeaf.length = FreeMonoid.length trueLeaf.trace := by
  exact Cursor.length_eq_trace_length trueLeaf

/-- The witness retains the continuation, rather than merely comparing lengths. -/
def extendsInternal : Cursor.Extends internal trueLeaf where
  continuation := indexEdge.toCursor.comp unitEdge.toCursor
  comp_eq := rfl

/-- A separate witness records that the extension is exactly one edge. -/
def extendsInternalByOne : Cursor.ExtendsByOne internal afterIndexCursor where
  edge := indexEdge
  comp_eq := rfl

end PFunctor.FreeM.CursorExamples
