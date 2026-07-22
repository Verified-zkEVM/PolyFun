/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.TypeTree
import Mathlib.Data.Fintype.Basic

/-!
# Branching ornaments on interaction type trees

`Interaction.TypeTree.Fintype tree` and `Interaction.TypeTree.Nonempty tree`
are recursive typeclass-level ornaments asserting, respectively, that every
move space in `tree` is finite or nonempty.

Keeping the properties separate follows `PFunctor.Fintype` and
`OracleSpec.Fintype`: finiteness does not imply that a move is available.
`TypeTree` has many layers of positions, so each ornament recurses into every
subtree.

Together, `TypeTree.Fintype tree` and `TypeTree.Nonempty tree` provide the
assumptions needed by downstream uniform samplers. PolyFun itself remains
independent of any probability monad.
-/

universe u

namespace Interaction

/-- Recursive finite-branching ornament on an interaction type tree.

The `.done` case holds vacuously. At a `.node X rest`, the ornament
stores a `Fintype X` witness together with a per-branch ornament on every
continuation `rest x`. Typeclass synthesis builds these structurally from
concrete trees via the companion instances below, the same way
`OracleSpec.Fintype` synthesizes from `PFunctor.Fintype`. -/
protected class inductive TypeTree.Fintype : TypeTree.{u} → Type (u + 1) where
  | done : TypeTree.Fintype TypeTree.done
  | node {X : Type u} (hFin : Fintype X)
      {rest : X → TypeTree.{u}} (hRec : ∀ x, TypeTree.Fintype (rest x)) :
      TypeTree.Fintype (TypeTree.node X rest)

namespace TypeTree.Fintype

/-- Canonical `TypeTree.Fintype` instance for the terminal tree. -/
instance instDone : TypeTree.Fintype TypeTree.done := .done

/-- Canonical `TypeTree.Fintype` instance for a node: synthesizes from
`Fintype X` and a per-branch ornament. -/
instance instNode {X : Type u} [hFin : Fintype X]
    {rest : X → TypeTree.{u}} [hRec : ∀ x, TypeTree.Fintype (rest x)] :
    TypeTree.Fintype (TypeTree.node X rest) :=
  .node hFin hRec

/-- Extract the `Fintype` instance for the move space of the root node. -/
@[reducible]
def rootFintype {X : Type u} {rest : X → TypeTree.{u}}
    (h : TypeTree.Fintype (TypeTree.node X rest)) : Fintype X :=
  match h with
  | .node hFin _ => hFin

/-- Extract the ornament for every continuation of the root node. -/
@[reducible]
def rest {X : Type u} {rest : X → TypeTree.{u}}
    (h : TypeTree.Fintype (TypeTree.node X rest)) : ∀ x, TypeTree.Fintype (rest x) :=
  match h with
  | .node _ hRec => hRec

end TypeTree.Fintype

/-- Recursive nonempty-branching ornament on an interaction type tree.

The `.done` case holds vacuously. At a `.node X rest`, the ornament stores a
`Nonempty X` witness and recursively requires every continuation to be
nonempty-branching. This is separate from `TypeTree.Fintype`: a finite move
space may be empty. -/
protected class inductive TypeTree.Nonempty : TypeTree.{u} → Prop where
  | done : TypeTree.Nonempty TypeTree.done
  | node {X : Type u} (hNonempty : Nonempty X)
      {rest : X → TypeTree.{u}} (hRec : ∀ x, TypeTree.Nonempty (rest x)) :
      TypeTree.Nonempty (TypeTree.node X rest)

namespace TypeTree.Nonempty

/-- Canonical `TypeTree.Nonempty` instance for the terminal tree. -/
instance instDone : TypeTree.Nonempty TypeTree.done := .done

/-- Canonical `TypeTree.Nonempty` instance for a node: synthesizes from
`Nonempty X` and a per-branch ornament. -/
instance instNode {X : Type u} [hNonempty : Nonempty X]
    {rest : X → TypeTree.{u}} [hRec : ∀ x, TypeTree.Nonempty (rest x)] :
    TypeTree.Nonempty (TypeTree.node X rest) :=
  .node hNonempty hRec

/-- Extract the `Nonempty` instance for the move space of the root node. -/
theorem rootNonempty {X : Type u} {rest : X → TypeTree.{u}}
    (h : TypeTree.Nonempty (TypeTree.node X rest)) : Nonempty X :=
  match h with
  | .node hNonempty _ => hNonempty

/-- Extract the ornament for every continuation of the root node. -/
theorem rest {X : Type u} {rest : X → TypeTree.{u}}
    (h : TypeTree.Nonempty (TypeTree.node X rest)) : ∀ x, TypeTree.Nonempty (rest x) :=
  match h with
  | .node _ hRec => hRec

end TypeTree.Nonempty

end Interaction
