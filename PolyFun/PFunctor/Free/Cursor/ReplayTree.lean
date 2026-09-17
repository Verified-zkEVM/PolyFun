/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cursor.Occurrence

/-!
# Finite replay trees with source execution paths

A replay tree retains a typed occurrence at every branch. Each selected leaf
therefore reconstructs a path of the original program. The structural interface
is independent of sampling, acceptance predicates, and the number of siblings.
Branches may have arity zero, and different leaf addresses may reconstruct the
same source path when their prescribed answers coincide.
-/

public section

universe uA uB v

namespace PFunctor.FreeM.Cursor

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- A finite family of source executions sharing typed occurrence prefixes. -/
inductive ReplayTree : (program : FreeM P α) → Type (max uA uB v) where
  | leaf {program} (path : Path program) : ReplayTree program
  | branch {program} {target : P.A} {ordinal : Nat}
      (occurrence : Occurrence target program ordinal) (arity : Nat)
      (answers : Fin arity → P.B target)
      (children : (i : Fin arity) → ReplayTree (occurrence.resume (answers i))) :
      ReplayTree program

namespace ReplayTree

/-- An address selecting one realized leaf of a replay tree. -/
inductive Leaf : {program : FreeM P α} → ReplayTree program → Type (max uA uB v) where
  | leaf {program} {path : Path program} : Leaf (.leaf path)
  | branch {program} {target : P.A} {ordinal : Nat}
      {occurrence : Occurrence target program ordinal} {arity : Nat}
      {answers : Fin arity → P.B target}
      {children : (i : Fin arity) → ReplayTree (occurrence.resume (answers i))}
      (i : Fin arity) (tail : Leaf (children i)) :
      Leaf (.branch occurrence arity answers children)

/-- Reconstruct the source path of a selected replay leaf. -/
@[expose]
def Leaf.path : {program : FreeM P α} → {tree : ReplayTree program} →
    Leaf tree → Path program
  | _, .leaf path, .leaf => path
  | _, .branch occurrence _ answers _, .branch i tail =>
      occurrence.plug (answers i) tail.path

/-- The result stored at a leaf, before reconstructing its surrounding prefixes. -/
@[expose]
def Leaf.result : {program : FreeM P α} → {tree : ReplayTree program} → Leaf tree → α
  | program, .leaf path, .leaf => output program path
  | _, .branch _ _ _ _, .branch _ tail => tail.result

/-- Reconstructing prefixes preserves the selected leaf's output. -/
@[simp]
theorem Leaf.output_path {program : FreeM P α} {tree : ReplayTree program}
    (leaf : Leaf tree) : output program leaf.path = leaf.result := by
  induction leaf with
  | leaf => rfl
  | branch i tail ih => simpa only [Leaf.path, Occurrence.output_plug, Leaf.result] using ih

/-- Every branch keeps precisely the prefix preceding its selected occurrence. -/
theorem branch_trace {program : FreeM P α} {target : P.A} {ordinal : Nat}
    (occurrence : Occurrence target program ordinal) (arity : Nat)
    (answers : Fin arity → P.B target)
    (children : (i : Fin arity) → ReplayTree (occurrence.resume (answers i)))
    (i : Fin arity) (tail : Leaf (children i)) :
    Path.trace program (Leaf.path (tree := .branch occurrence arity answers children)
      (.branch i tail)) = List.append occurrence.before
        (⟨target, answers i⟩ :: Path.trace _ tail.path) :=
  occurrence.trace_plug (answers i) tail.path


end ReplayTree
end PFunctor.FreeM.Cursor
