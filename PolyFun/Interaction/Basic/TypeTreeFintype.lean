/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.TypeTree
import Mathlib.Data.Fintype.Basic

/-!
# Finite-branching ornament on interaction type trees

`Interaction.TypeTree.Fintype spec` is the recursive typeclass-level ornament
asserting that every move space appearing in `spec : TypeTree.{0}` carries
`Fintype` and `Nonempty` instances.

This is the tree-shaped analog of `OracleSpec.Fintype extends PFunctor.Fintype`:
`OracleSpec` has one layer of positions (a single polynomial functor), so a
single `PFunctor.Fintype` witness suffices. `TypeTree` is a tree of nodes, so the
ornament recurses into every subtree.

A `TypeTree.Fintype spec` instance is the data needed to derive a canonical
uniform sampler `TypeTree.Sampler.uniform : Sampler ProbComp spec` built by
uniform selection at each node (see `PolyFun.Interaction.UC.Runtime`).
-/

namespace Interaction

/-- Recursive finite-branching ornament on an interaction type tree.

The `.done` case holds vacuously. At a `.node X rest` the ornament
bundles `Fintype` and `Nonempty` witnesses for the move space `X`
together with a per-branch ornament on every continuation `rest x`.
Typeclass synthesis builds these up structurally from concrete `spec`
trees via the companion instances below, the same way
`OracleSpec.Fintype` synthesizes from `PFunctor.Fintype`. -/
protected class inductive TypeTree.Fintype : TypeTree.{0} → Type 1 where
  | done : TypeTree.Fintype TypeTree.done
  | node {X : Type} (hFin : Fintype X) (hNon : Nonempty X)
      {rest : X → TypeTree.{0}} (hRec : ∀ x, TypeTree.Fintype (rest x)) :
      TypeTree.Fintype (TypeTree.node X rest)

namespace TypeTree.Fintype

/-- Canonical `TypeTree.Fintype` instance for the terminal tree. -/
instance instDone : TypeTree.Fintype TypeTree.done := .done

/-- Canonical `TypeTree.Fintype` instance for a node: synthesizes from
`Fintype X`, `Nonempty X`, and a per-branch ornament. -/
instance instNode {X : Type} [hFin : Fintype X] [hNon : Nonempty X]
    {rest : X → TypeTree.{0}} [hRec : ∀ x, TypeTree.Fintype (rest x)] :
    TypeTree.Fintype (TypeTree.node X rest) :=
  .node hFin hNon hRec

/-- Extract the `Fintype` instance for the move space of the root node. -/
@[reducible]
def rootFintype {X : Type} {rest : X → TypeTree.{0}}
    (h : TypeTree.Fintype (TypeTree.node X rest)) : Fintype X :=
  match h with
  | .node hFin _ _ => hFin

/-- Extract the `Nonempty` instance for the move space of the root node. -/
theorem rootNonempty {X : Type} {rest : X → TypeTree.{0}}
    (h : TypeTree.Fintype (TypeTree.node X rest)) : Nonempty X :=
  match h with
  | .node _ hNon _ => hNon

/-- Extract the ornament for every continuation of the root node. -/
@[reducible]
def tail {X : Type} {rest : X → TypeTree.{0}}
    (h : TypeTree.Fintype (TypeTree.node X rest)) : ∀ x, TypeTree.Fintype (rest x) :=
  match h with
  | .node _ _ hRec => hRec

end TypeTree.Fintype

end Interaction
