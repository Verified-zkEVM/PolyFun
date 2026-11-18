/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Combinatorics.Hypergraph.WeakColoring
public import Mathlib.Combinatorics.Matroid.Circuit

/-!
# Independent color classes in a matroid

Use the ground set of the matroid as vertices and its circuits as edges. A coloring splits
every circuit exactly when the elements of each color form an independent set.
-/

public section

namespace PolyFunExamples.MatroidColoring

variable {V K : Type*} (M : Matroid V)

/-- The circuits already contain exactly the minimal dependencies of a matroid. -/
@[expose] def circuitHypergraph : Hypergraph V where
  vertexSet := M.E
  edgeSet := {s | M.IsCircuit s}
  subset_vertexSet_of_mem_edgeSet' := fun _ h => h.subset_ground

/-- The ambient set of each color class is independent iff the coloring splits every circuit. -/
theorem isWeakColoring_iff_indep (c : M.E → K) :
    (circuitHypergraph M).IsWeakColoring c ↔ ∀ i, M.Indep (Subtype.val '' {v | c v = i}) := by
  refine ((circuitHypergraph M).isWeakColoring_iff_forall_not_subset
    (fun _ h => Matroid.IsCircuit.nonempty h) c).trans ?_
  apply forall_congr'
  intro i
  have ground : Subtype.val '' {v | c v = i} ⊆ M.E := by
    rintro _ ⟨v, _, rfl⟩
    exact v.property
  rw [M.indep_iff_forall_subset_not_isCircuit ground]
  constructor
  · intro avoids C sub circuit
    exact avoids C circuit sub
  · intro independent C circuit sub
    exact independent C sub circuit

end PolyFunExamples.MatroidColoring
