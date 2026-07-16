/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Cursor.Append
public import PolyFunTest.PFunctor.FreeDisplayedCursorExamples

/-! # Cursor decomposition examples for dependent append -/

@[expose] public section

namespace PFunctor.FreeM.CursorAppendExamples

open DisplayedCursorExamples
open Displayed

def suffix (path : Path program) : FreeM Interface Nat :=
  FreeM.liftBind .finish fun _ => pure (100 + output program path)

def leftJoined : Cursor (FreeM.append program suffix) :=
  internal.liftAppend suffix

def truePath : Path program :=
  ⟨true, selectedIndex, PUnit.unit, ⟨⟩⟩

def rightRoot : Cursor (suffix truePath) :=
  Cursor.root (suffix truePath)

def rightJoined : Cursor (FreeM.append program suffix) :=
  Cursor.joinRight program suffix truePath rightRoot

theorem internalIsNode : Cursor.IsNode internal.residual := by
  change Cursor.IsNode
    (FreeM.liftBind (P := Interface) Command.index afterIndex)
  exact Cursor.IsNode.liftBind (P := Interface) (α := Nat)
    Command.index afterIndex

example : leftJoined.residual =
    FreeM.append internal.residual (fun path => suffix (internal.plug path)) := rfl

example : rightJoined.residual = suffix truePath := rfl

example : Cursor.split program suffix leftJoined =
    .left internal internalIsNode := by
  exact Cursor.split_liftAppend_of_isNode suffix internal internalIsNode

example : Cursor.split program suffix rightJoined = .right truePath rightRoot := by
  exact Cursor.split_joinRight program suffix truePath rightRoot

example : (Cursor.split program suffix leftJoined).join = leftJoined :=
  Cursor.join_split program suffix leftJoined

example : (Cursor.split program suffix rightJoined).join = rightJoined :=
  Cursor.join_split program suffix rightJoined

example (continuation : Cursor internal.residual) :
    (internal.comp continuation).liftAppend suffix =
      leftJoined.comp
        (continuation.liftAppend (fun path => suffix (internal.plug path))) :=
  Cursor.liftAppend_comp internal continuation suffix

example (view : Cursor.AppendView program suffix) :
    Cursor.split program suffix view.join = view :=
  Cursor.split_join view

def suffixPath : Path (suffix truePath) := ⟨PUnit.unit, ⟨⟩⟩

example : Cursor.joinRight program suffix truePath
      (Cursor.ofPath (suffix truePath) suffixPath) =
    Cursor.ofPath (FreeM.append program suffix)
      (Path.append program suffix truePath suffixPath) :=
  Cursor.joinRight_ofPath program suffix truePath suffixPath

example : Cursor.split program suffix
      (Cursor.ofPath (FreeM.append program suffix)
        (Path.append program suffix truePath suffixPath)) =
    .right truePath (Cursor.ofPath (suffix truePath) suffixPath) :=
  Cursor.split_ofPath_append suffix truePath suffixPath

def suffixLabels (path : Path program) : Decoration Labels (suffix path) :=
  ⟨40 + output program path, fun _ => ⟨⟩⟩

def appendedLabels : Decoration Labels (FreeM.append program suffix) :=
  Decoration.append labels suffixLabels

example : Decoration.restrict leftJoined appendedLabels =
    Decoration.append (Decoration.restrict internal labels)
      (fun path => suffixLabels (internal.plug path)) :=
  Cursor.Decoration.restrict_liftAppend suffix internal labels suffixLabels

example : Decoration.restrict rightJoined appendedLabels =
    Decoration.restrict rightRoot (suffixLabels truePath) :=
  Cursor.Decoration.restrict_joinRight program suffix truePath rightRoot labels suffixLabels

def suffixFibers (path : Path program) :
    Decoration.Over Labels Fibers (suffix path) (suffixLabels path) :=
  ⟨0, fun _ => ⟨⟩⟩

def appendedFibers : Decoration.Over Labels Fibers
    (FreeM.append program suffix) appendedLabels :=
  Decoration.Over.append fibers suffixFibers

example : HEq
    (Decoration.Over.restrict leftJoined appendedLabels appendedFibers)
    (Decoration.Over.append
      (Decoration.Over.restrict internal labels fibers)
      (fun path => suffixFibers (internal.plug path))) :=
  Cursor.Decoration.Over.restrict_liftAppend suffix internal labels suffixLabels
    fibers suffixFibers

example : HEq
    (Decoration.Over.restrict rightJoined appendedLabels appendedFibers)
    (Decoration.Over.restrict rightRoot (suffixLabels truePath) (suffixFibers truePath)) :=
  Cursor.Decoration.Over.restrict_joinRight program suffix truePath rightRoot
    labels suffixLabels fibers suffixFibers

end PFunctor.FreeM.CursorAppendExamples
