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

def afterChoice : Bool → FreeM Interface Nat
  | false => .pure 7
  | true => .liftBind (.select true) fun index => .pure (10 + index.val)

def program : FreeM Interface Nat :=
  .liftBind .choose afterChoice

def selectedIndex : Fin 2 := ⟨1, by omega⟩

/-- An internal cursor stops after choosing the nontrivial dependent branch. -/
def internal : Cursor program :=
  Cursor.down true (Cursor.root (afterChoice true))

example : internal.residual = afterChoice true := rfl

example : internal.length = 1 := rfl

example : internal.trace = [⟨Command.choose, true⟩] := rfl

/-- One more edge selects a leaf within the `Fin 2` branch. -/
def leafEdge : Cursor.Edge internal.residual :=
  Cursor.Edge.down selectedIndex

def trueLeaf : Cursor program :=
  internal.comp leafEdge.toCursor

example : trueLeaf.residual = FreeM.pure 11 := rfl

example : trueLeaf.length = 2 := rfl

example : trueLeaf.trace =
    [⟨Command.choose, true⟩, ⟨Command.select true, selectedIndex⟩] := rfl

def truePath : Path program :=
  ⟨true, selectedIndex, ⟨⟩⟩

def falsePath : Path program :=
  ⟨false, ⟨⟩⟩

example : internal.plug (⟨selectedIndex, ⟨⟩⟩ : Path internal.residual) = truePath := rfl

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

/-- The witness retains the continuation, rather than merely comparing lengths. -/
def extendsInternal : Cursor.Extends internal trueLeaf where
  continuation := leafEdge.toCursor
  comp_eq := rfl

/-- A separate witness records that the extension is exactly one edge. -/
def extendsInternalByOne : Cursor.ExtendsByOne internal trueLeaf where
  edge := leafEdge
  comp_eq := rfl

end PFunctor.FreeM.CursorExamples
