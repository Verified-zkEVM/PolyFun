/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.MoveTranslation
public import ToCslib.Combinatorics.Hypergraph.WeakColoring
public import Mathlib.Order.Antichain
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# When a hint colors the hidden states

One hint can group states if every source move admits a target move shared by those states.
The inclusion-minimal groups that fail this test form the edges of a hypergraph. A decoder
exists exactly when the hint assigns at least two values to every edge.
-/

public section

namespace PolyFunExamples.Bargaining.Replay

variable {T B C O H I : Type}

/-- Each source move can be translated uniformly on the finite set of states `s`. -/
@[expose] def Feasible (mode : Mode) (board : Board T B C O) (s : Finset T) : Prop :=
  ∀ b, ∃ c, ∀ t ∈ s, Compatible mode board t b c

/-- The fallback target suffices when no state needs a translation. -/
theorem feasible_empty (mode : Mode) (board : Board T B C O) :
    Feasible mode board ∅ :=
  fun _ => ⟨board.defaultMove, by simp⟩

/-- A uniform translation on a set of states also works on each subset. -/
theorem Feasible.mono {mode : Mode} {board : Board T B C O} {s u : Finset T}
    (hs : Feasible mode board s) (hu : u ⊆ s) : Feasible mode board u :=
  fun b => (hs b).imp (fun _ hc t ht => hc t (hu ht))

/-- All states are vertices. An edge is an inclusion-minimal finite group of states that
cannot share one hint. -/
@[expose] def obstructionHypergraph (mode : Mode) (board : Board T B C O) : Hypergraph T where
  vertexSet := Set.univ
  edgeSet := { e | ∃ s : Finset T, Minimal (fun u => ¬ Feasible mode board u) s ∧ (s : Set T) = e }
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _

/-- The finite edge membership test is inclusion-minimal failure of feasibility. -/
theorem coe_mem_obstructionHypergraph_iff (mode : Mode) (board : Board T B C O) (s : Finset T) :
    (s : Set T) ∈ (obstructionHypergraph mode board).edgeSet ↔
      Minimal (fun u => ¬ Feasible mode board u) s := by
  refine ⟨?_, fun hs => ⟨s, hs, rfl⟩⟩
  rintro ⟨u, hu, eq⟩
  exact Finset.coe_injective eq ▸ hu

/-- A weak coloring gives two distinct colors somewhere in each edge. -/
@[expose] def WeakColoring (graph : Hypergraph T) (h : T → H) : Prop :=
  graph.IsWeakColoring (fun x => h x.val)

/-- A hint supports a decoder exactly when it splits each minimal infeasible group. -/
theorem exists_valid_iff_weakColoring [Finite T] (mode : Mode) (board : Board T B C O)
    (h : T → H) :
    (∃ d, Valid mode board h d) ↔ WeakColoring (obstructionHypergraph mode board) h := by
  classical
  let := Fintype.ofFinite T
  constructor
  · rintro ⟨d, hd⟩ _ ⟨s, hm, rfl⟩
    obtain ⟨x, hx⟩ : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      rintro rfl
      exact hm.prop (feasible_empty mode board))
    by_contra! same
    apply hm.prop
    intro b
    exact ⟨d (h x) b, fun t ht => by simpa [same t ht x hx] using hd t b⟩
  · intro color
    have ok (i : H) : Feasible mode board (Finset.univ.filter fun t => h t = i) := by
      by_contra bad
      obtain ⟨s, hs, hm⟩ :=
        exists_minimal_le_of_wellFoundedLT (fun s => ¬ Feasible mode board s) _ bad
      obtain ⟨x, hx, y, hy, hxy⟩ := color _ ⟨s, hm, rfl⟩
      exact hxy (((Finset.mem_filter.mp (hs hx)).2).trans ((Finset.mem_filter.mp (hs hy)).2).symm)
    choose d hd using fun i b => ok i b
    exact ⟨d, fun t b => hd (h t) b t (by simp)⟩

/-- A finite-edge family on all states. Equal indexed edges define the same hyperedge. -/
@[expose] def edgeHypergraph (edges : I → Finset T) : Hypergraph T where
  vertexSet := Set.univ
  edgeSet := Set.range fun i => (edges i : Set T)
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _

/-- Source move `i` announces edge `i`. The target alternative `(i,v)` announces that edge
exactly outside state `v`. The fallback gives the opening observation everywhere. -/
@[expose] def realizationBoard [DecidableEq T] (edges : I → Finset T) :
    Board T I (Unit ⊕ ((i : I) × ↥(edges i))) (Option I) where
  opening _ := none
  source _ i := some i
  target
    | _, .inl _ => none
    | t, .inr ⟨i, v⟩ => if t = v.val then none else some i
  defaultMove := .inl ()

private theorem compatible_realization [DecidableEq T] (edges : I → Finset T) (mode : Mode)
    (t : T) (i : I) (c : Unit ⊕ ((j : I) × ↥(edges j))) :
    Compatible mode (realizationBoard edges) t i c ↔
      match c with
      | .inl _ => False
      | .inr ⟨j, v⟩ => i = j ∧ t ≠ v.val := by
  cases c with
  | inl => cases mode <;> simp [Compatible, realizationBoard]
  | inr p =>
    obtain ⟨j, v⟩ := p
    by_cases ht : t = v.val <;> cases mode <;> simp [Compatible, realizationBoard, ht]

/-- Each nonempty edge must have a vertex outside the proposed hint block. Choosing that
vertex translates the edge's source move on the entire block. -/
theorem feasible_realization_iff [DecidableEq T] (edges : I → Finset T)
    (hne : ∀ i, (edges i).Nonempty) (mode : Mode) (s : Finset T) :
    Feasible mode (realizationBoard edges) s ↔ ∀ i, ¬ edges i ⊆ s := by
  constructor
  · intro ok i sub
    obtain ⟨x, hx⟩ := hne i
    obtain ⟨c, hc⟩ := ok i
    cases c with
    | inl => exact (compatible_realization edges mode x i _).1 (hc x (sub hx))
    | inr p =>
      obtain ⟨j, v⟩ := p
      have eq := ((compatible_realization edges mode x i _).1 (hc x (sub hx))).1
      subst j
      exact ((compatible_realization edges mode v.val i _).1 (hc v.val (sub v.property))).2 rfl
  · intro good i
    obtain ⟨v, hv, hvout⟩ := Finset.not_subset.mp (good i)
    exact ⟨.inr ⟨i, ⟨v, hv⟩⟩, fun t ht => (compatible_realization edges mode t i _).2
      ⟨rfl, fun (eq : t = v) => hvout (eq ▸ ht)⟩⟩

/-- Every family of nonempty finite edges is realized by a board whose translatable hints are
exactly its weak colorings. Both modes induce the same condition. -/
theorem exists_valid_realization_iff [DecidableEq T] (edges : I → Finset T)
    (hne : ∀ i, (edges i).Nonempty) (mode : Mode) (h : T → H) :
    (∃ d, Valid mode (realizationBoard edges) h d) ↔ WeakColoring (edgeHypergraph edges) h := by
  classical
  constructor
  · rintro ⟨d, hd⟩ _ ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hne i
    by_contra! same
    have ok : Feasible mode (realizationBoard edges) (edges i) :=
      fun b => ⟨d (h x) b, fun t ht => by simpa [same t ht x hx] using hd t b⟩
    exact ((feasible_realization_iff edges hne mode _).1 ok i) Finset.Subset.rfl
  · intro color
    have missed (z : H) (i : I) : ∃ v ∈ edges i, h v ≠ z := by
      obtain ⟨x, hx, y, hy, hxy⟩ := color _ ⟨i, rfl⟩
      by_cases he : h x = z
      · exact ⟨y, hy, fun hyz => hxy (he.trans hyz.symm)⟩
      · exact ⟨x, hx, he⟩
    choose v hv hmiss using missed
    refine ⟨fun z i => .inr ⟨i, ⟨v z i, hv z i⟩⟩, fun t i => ?_⟩
    exact (compatible_realization edges mode t i _).2 ⟨rfl, fun eq =>
      hmiss (h t) i (congrArg h eq).symm⟩

/-- The obstruction edges of the constructed board are the inclusion-minimal input edges. -/
theorem coe_mem_realization_iff [DecidableEq T] (edges : I → Finset T)
    (hne : ∀ i, (edges i).Nonempty) (mode : Mode) (s : Finset T) :
    (s : Set T) ∈ (obstructionHypergraph mode (realizationBoard edges)).edgeSet ↔
      Minimal (· ∈ Set.range edges) s := by
  classical
  have bad (q : Finset T) : ¬ Feasible mode (realizationBoard edges) q ↔ ∃ i, edges i ⊆ q := by
    simp [feasible_realization_iff edges hne]
  rw [coe_mem_obstructionHypergraph_iff]
  constructor
  · intro hm
    obtain ⟨i, hi⟩ := (bad s).1 hm.prop
    have eq := hm.eq_of_ge ((bad _).2 ⟨i, Finset.Subset.rfl⟩) hi
    refine ⟨⟨i, eq.symm⟩, ?_⟩
    rintro q ⟨j, rfl⟩ hqs
    exact hm.le_of_le ((bad _).2 ⟨j, Finset.Subset.rfl⟩) hqs
  · intro hm
    obtain ⟨i, hi⟩ := hm.prop
    refine ⟨(bad _).2 ⟨i, hi.le⟩, fun q hq hqs => ?_⟩
    obtain ⟨j, hj⟩ := (bad q).1 hq
    exact (hm.le_of_le ⟨j, rfl⟩ (hj.trans hqs)).trans hj

/-- A family of incomparable nonempty edges is recovered as the board's obstruction hypergraph. -/
theorem obstructionHypergraph_realization [DecidableEq T] (edges : I → Finset T)
    (hne : ∀ i, (edges i).Nonempty) (anti : IsAntichain (· ≤ ·) (Set.range edges))
    (mode : Mode) : obstructionHypergraph mode (realizationBoard edges) = edgeHypergraph edges := by
  refine Hypergraph.ext ?_ ?_
  · rfl
  ext e
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨i, rfl⟩ := anti.minimal_mem_iff.mp ((coe_mem_realization_iff edges hne mode s).1
      ((coe_mem_obstructionHypergraph_iff ..).2 hs))
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact (coe_mem_realization_iff edges hne mode _).2 (anti.minimal_mem_iff.mpr ⟨i, rfl⟩)

end PolyFunExamples.Bargaining.Replay
