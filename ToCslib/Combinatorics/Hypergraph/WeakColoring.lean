/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Combinatorics.Hypergraph.Basic

/-!
# Weak vertex colorings

A weak coloring gives two vertices in every edge different colors. A color is assigned only
to a vertex of the hypergraph, so an empty ground set can use an empty color type.
-/

public section

namespace Hypergraph

variable {V K : Type*} (G : Hypergraph V)

/-- Every edge contains two vertices with different colors. -/
@[expose] def IsWeakColoring (c : G.vertexSet → K) : Prop :=
  ∀ (e : Set V) (he : e ∈ G.edgeSet), ∃ (x : V) (hx : x ∈ e) (y : V) (hy : y ∈ e),
    c ⟨x, G.subset_vertexSet_of_mem_edgeSet he hx⟩ ≠
      c ⟨y, G.subset_vertexSet_of_mem_edgeSet he hy⟩

/-- For a hypergraph with nonempty edges, weak coloring is equivalent to forbidding
each whole edge from lying in one color class. -/
theorem isWeakColoring_iff_forall_not_subset (nonempty : ∀ e ∈ G.edgeSet, Set.Nonempty e)
    (c : G.vertexSet → K) :
    G.IsWeakColoring c ↔ ∀ i : K, ∀ e ∈ G.edgeSet, ¬ e ⊆ Subtype.val '' {v | c v = i} := by
  constructor
  · intro split i e he sub
    obtain ⟨x, hx, y, hy, ne⟩ := split e he
    obtain ⟨⟨_, _⟩, hxi, rfl⟩ := sub hx
    obtain ⟨⟨_, _⟩, hyi, rfl⟩ := sub hy
    exact ne (hxi.trans hyi.symm)
  · intro avoids e he
    obtain ⟨x, hx⟩ := nonempty e he
    let vertex (y : V) (hy : y ∈ e) : G.vertexSet :=
      ⟨y, G.subset_vertexSet_of_mem_edgeSet he hy⟩
    refine ⟨x, hx, ?_⟩
    by_contra! same
    apply avoids (c (vertex x hx)) e he
    intro y hy
    exact ⟨vertex y hy, (same y hy).symm, rfl⟩

end Hypergraph
