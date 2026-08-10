/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

import all PolyFun.ITree.Basic
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

universe uA uB uR uS

namespace PFunctor

/-- Embed a `p`-behavior tree as an interaction tree over event signature `p`:
every node becomes a visible `query` at its position, with the same children.
The result never returns (`PEmpty` leaves) and takes no silent steps. The empty
return type may live in a universe independent of both universes of `p`. -/
def M.toITree {p : PFunctor.{uA, uB}} : M p → ITree p PEmpty.{uR + 1} :=
  M.corec fun t => ⟨.query (M.dest t).1, (M.dest t).2⟩

namespace DynSystem

/-- The ITree unfolding of a dynamical system from a state: query the exposed
position forever, transitioning along each answer. -/
def toITree {S : Type uS} {p : PFunctor.{uA, uB}} (s : DynSystem S p) :
    S → ITree p PEmpty.{uR + 1} :=
  M.corec fun st => ⟨.query (s.expose st), fun d => s.update st d⟩

@[simp] theorem dest_toITree {S : Type uS} {p : PFunctor.{uA, uB}}
    (s : DynSystem S p) (st : S) :
    M.dest (s.toITree st)
      = ⟨.query (s.expose st), fun d => s.toITree (s.update st d)⟩ := by
  let g : S → (ITree.Poly p PEmpty) S :=
    fun st => ⟨.query (s.expose st), fun d => s.update st d⟩
  change M.dest (M.corec g st) =
    ⟨.query (s.expose st), fun d => M.corec g (s.update st d)⟩
  rw [M.dest_corec_apply]

/-- Unfolding a system into an ITree is the query-embedding of its behavior
tree: the two coinductive semantics agree. -/
theorem toITree_eq_toITree_behavior {S : Type uS} {p : PFunctor.{uA, uB}}
    (s : DynSystem S p) (st : S) :
    s.toITree st = M.toITree (s.behavior st) := by
  refine congrFun (M.corec_unique _ (fun st => M.toITree (s.behavior st)) ?_).symm st
  intro st
  let g : M p → (ITree.Poly p PEmpty) (M p) :=
    fun t => ⟨.query (M.dest t).1, (M.dest t).2⟩
  change M.dest (M.corec g (s.behavior st)) = _
  have hg : g (s.behavior st) =
      ⟨.query (s.expose st), fun d => s.behavior (s.update st d)⟩ := by
    dsimp only [g]
    rw [DynSystem.dest_behavior]
  rw [M.dest_corec_eq g _ hg]
  rfl

end DynSystem

end PFunctor
