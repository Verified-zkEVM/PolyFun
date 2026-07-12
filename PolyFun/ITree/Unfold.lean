/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Basic
public import PolyFun.PFunctor.Dynamical.Trajectory

/-!
# Unfolding dynamical systems into interaction trees

A `p`-dynamical system queries its interface forever: at each state it exposes
a position (a visible event) and transitions along the answer. Unfolding this
into the ITree over event signature `p` gives a tree with no `pure` leaves and
no silent steps — every node is a `query` at the exposed position.

* `PFunctor.M.toITree` — embed a behavior tree `M p` as an all-query ITree.
* `PFunctor.DynSystem.toITree` — the ITree unfolding of a dynamical system,
  which is the query-embedding of its behavior tree
  (`DynSystem.toITree_eq_toITree_behavior`).
-/

@[expose] public section

universe u v

namespace PFunctor

/-- Embed a `p`-behavior tree as an interaction tree over event signature `p`:
every node becomes a visible `query` at its position, with the same children.
The result never returns (`PEmpty` leaves) and takes no silent steps. -/
def M.toITree {p : PFunctor.{u, u}} : M p → ITree p PEmpty.{u + 1} :=
  M.corec fun t => ⟨.query (M.dest t).1, (M.dest t).2⟩

namespace DynSystem

/-- The ITree unfolding of a dynamical system from a state: query the exposed
position forever, transitioning along each answer. -/
def toITree {S : Type v} {p : PFunctor.{u, u}} (s : DynSystem S p) :
    S → ITree p PEmpty.{u + 1} :=
  M.corec fun st => ⟨.query (s.expose st), fun d => s.update st d⟩

@[simp] theorem dest_toITree {S : Type v} {p : PFunctor.{u, u}} (s : DynSystem S p) (st : S) :
    M.dest (s.toITree st)
      = ⟨.query (s.expose st), fun d => s.toITree (s.update st d)⟩ := by
  simp only [toITree, M.dest_corec_apply]

/-- Unfolding a system into an ITree is the query-embedding of its behavior
tree: the two coinductive semantics agree. -/
theorem toITree_eq_toITree_behavior {S : Type v} {p : PFunctor.{u, u}} (s : DynSystem S p)
    (st : S) : s.toITree st = M.toITree (s.behavior st) := by
  refine congrFun (Eq.symm (M.corec_unique _ (fun st => M.toITree (s.behavior st)) ?_)) st
  intro st
  simp only [M.toITree, M.dest_corec_apply]
  rfl

end DynSystem

end PFunctor
