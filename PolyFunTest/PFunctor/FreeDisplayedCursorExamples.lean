/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Displayed.Cursor

/-! # Cursor restriction examples for displayed free programs -/

@[expose] public section

universe uA uB v

namespace PFunctor.FreeM.DisplayedCursorExamples

open Displayed

inductive Command
  | choose
  | index
  | finish
  deriving DecidableEq

def Answer : Command → Type
  | .choose => Bool
  | .index => Fin 2
  | .finish => PUnit

abbrev Interface : PFunctor where
  A := Command
  B := Answer

def afterIndex (index : Fin 2) : FreeM Interface Nat :=
  FreeM.liftBind .finish fun _ => pure (20 + index)

def afterChoice : Bool → FreeM Interface Nat
  | false => pure 7
  | true => FreeM.liftBind .index afterIndex

def program : FreeM Interface Nat :=
  FreeM.liftBind .choose afterChoice

def internal : Cursor program :=
  Cursor.down true (Cursor.root (afterChoice true))

def selectedIndex : Fin 2 := 1

def leaf : Cursor program :=
  internal.comp (Cursor.down selectedIndex
    (Cursor.down PUnit.unit (Cursor.root (pure 21))))

abbrev Labels (_ : Command) : Type := Nat

def labels : Decoration (P := Interface) Labels program :=
  ⟨10, fun choice => match choice with
    | false => ⟨⟩
    | true => ⟨20, fun index : Fin 2 => ⟨30 + index.val, fun _ => ⟨⟩⟩⟩⟩

example : Decoration.restrict internal labels = labels.2 true := rfl

example : Decoration.restrict leaf labels =
    (⟨⟩ : Decoration (P := Interface) Labels (pure 21)) := rfl

example : Decoration.restrict leaf labels =
    Decoration.restrict
      (Cursor.down selectedIndex
        (Cursor.down PUnit.unit (Cursor.root (pure 21))))
      (Decoration.restrict internal labels) :=
  Decoration.restrict_comp internal _ labels

abbrev Fibers (_ : Command) (label : Nat) : Type := Fin (label + 1)

def fibers : Decoration.Over (P := Interface) Labels Fibers program labels :=
  ⟨0, fun choice => match choice with
    | false => ⟨⟩
    | true => ⟨1, fun _index : Fin 2 => ⟨2, fun _ => ⟨⟩⟩⟩⟩

example : Decoration.Over.restrict internal labels fibers = fibers.2 true := rfl

example : Decoration.Over.restrict leaf labels fibers =
    (⟨⟩ : Decoration.Over (P := Interface) Labels Fibers (pure 21) ⟨⟩) := rfl

example : Decoration.restrict internal (Decoration.ofOver program labels fibers) =
    Decoration.ofOver internal.residual
      (Decoration.restrict internal labels)
      (Decoration.Over.restrict internal labels fibers) :=
  Decoration.restrict_ofOver internal labels fibers

example : Decoration.restrict internal (Decoration.map (fun _ n => n + 1) program labels) =
    Decoration.map (fun _ n => n + 1) internal.residual
      (Decoration.restrict internal labels) :=
  Decoration.restrict_map (fun _ n => n + 1) internal labels

end PFunctor.FreeM.DisplayedCursorExamples
