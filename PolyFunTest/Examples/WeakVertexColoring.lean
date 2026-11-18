/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.FerryCrossing
public import Examples.Tutorials.HintColoring
import Examples.Tutorials.MatroidColoring
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Data.Fintype.Powerset

/-! # Weak coloring on empty, singleton, nested, and three-tide conflicts -/

namespace PolyFunTest.WeakVertexColoring

open PolyFunExamples.Bargaining.Replay
open PolyFunExamples.Bargaining.Ferry
open PolyFunExamples.MatroidColoring

/-- All three tides together form the only minimal conflict. Every proper subset can share
a signal, in either replay mode. -/
public theorem closedOnce_edge_iff (mode : Mode) (s : Finset (Fin 3)) :
    (s : Set (Fin 3)) ∈ (obstructionHypergraph mode closedOnce).edgeSet ↔ s = Finset.univ := by
  rw [coe_mem_obstructionHypergraph_iff]
  unfold Minimal Feasible
  cases mode <;> decide +revert

/-- At the stranded harbor the lone tide is already an infeasible group. -/
theorem stranded_singleton_edge (mode : Mode) :
    (({0} : Finset (Fin 1)) : Set (Fin 1)) ∈ (obstructionHypergraph mode stranded).edgeSet := by
  rw [coe_mem_obstructionHypergraph_iff]
  unfold Minimal Feasible
  cases mode <;> decide

private def noStates : Board (Fin 0) Bool Bool Bool :=
  ⟨Fin.elim0, Fin.elim0, Fin.elim0, false⟩

private def noMoves : Board (Fin 1) (Fin 0) Bool Bool :=
  ⟨fun _ => false, fun _ => Fin.elim0, fun _ c => c, false⟩

example (mode : Mode) :
    WeakColoring (obstructionHypergraph mode noStates) (Fin.elim0 : Fin 0 → Fin 0) :=
  (exists_valid_iff_weakColoring _ _ _).mp ⟨Fin.elim0, fun t => t.elim0⟩

example (mode : Mode) :
    WeakColoring (obstructionHypergraph mode noMoves) (fun _ => (0 : Fin 1)) :=
  (exists_valid_iff_weakColoring _ _ _).mp ⟨fun _ => Fin.elim0, fun _ b => b.elim0⟩

/-- No signal assignment, even one revealing the entire tide, can split a singleton edge. -/
example {H : Type} (h : Fin 1 → H) (mode : Mode) :
    ¬ WeakColoring (obstructionHypergraph mode PolyFunExamples.Bargaining.Ferry.stranded) h := by
  intro color
  obtain ⟨x, _, y, _, different⟩ :=
    color _ (stranded_singleton_edge mode)
  exact different (congrArg h (Subsingleton.elim x y))

private def nestedEdges (i : Fin 2) : Finset (Fin 3) :=
  if i = 0 then {0, 1} else Finset.univ

/-- A redundant forbidden superset never appears as a minimal obstruction. -/
example (mode : Mode) (s : Finset (Fin 3)) :
    (s : Set (Fin 3)) ∈ (obstructionHypergraph mode (realizationBoard nestedEdges)).edgeSet ↔
      s = {0, 1} := by
  rw [coe_mem_realization_iff nestedEdges (by decide)]
  simp only [Minimal, Set.mem_range]
  decide +revert

/-- An empty edge cannot contain two colors. With no color labels, the statement
that every color class avoids every edge holds vacuously. -/
example :
    let G := Hypergraph.completeOn (Set.univ : Set (Fin 0))
    let c : G.vertexSet → Fin 0 := Subtype.val
    (∀ i : Fin 0, ∀ e ∈ G.edgeSet, ¬ e ⊆ Subtype.val '' {v | c v = i}) ∧
      ¬ G.IsWeakColoring c := by
  refine ⟨fun i => i.elim0, fun color => ?_⟩
  obtain ⟨x, _⟩ := color ∅ (Set.empty_subset _)
  exact x.elim0

/-- The ambient type has two elements, but an empty ground set can use zero colors. -/
example : ∃ c : (Matroid.emptyOn Bool).E → Fin 0,
    (circuitHypergraph (Matroid.emptyOn Bool)).IsWeakColoring c := by
  refine ⟨fun x => False.elim x.property, ?_⟩
  apply (isWeakColoring_iff_indep ..).2
  intro i
  exact i.elim0

/-- A loop is a singleton circuit. Its own color class is dependent. -/
example {V K : Type*} (M : Matroid V) (e : V) (loop : M.IsLoop e) (c : M.E → K) :
    ¬ (circuitHypergraph M).IsWeakColoring c := by
  intro coloring
  have hi := (isWeakColoring_iff_indep M c).1 coloring (c ⟨e, loop.mem_ground⟩)
  exact loop.isCircuit.dep.not_indep <| hi.subset (Set.singleton_subset_iff.mpr
    ⟨⟨e, loop.mem_ground⟩, rfl, rfl⟩)

end PolyFunTest.WeakVertexColoring
