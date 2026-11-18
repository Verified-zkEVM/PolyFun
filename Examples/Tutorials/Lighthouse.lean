/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.MinimumHint
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Two sightings from five lighthouses

A lookout sees a lighthouse and sends a signal. A navigator already knows an edge of the
pentagon containing the lighthouse. A decoder must recover the sighting from the signal and
that edge. Two sightings can share a single signal with five possible values.
-/

public section

namespace PolyFunExamples.Bargaining.Replay.Lighthouse

/-- The clue names an edge by its clockwise starting point. -/
@[expose] def AdjacentClue (e x : Fin 5) : Prop := x = e ∨ x = e + 1

instance instDecidableAdjacentClue (e x : Fin 5) : Decidable (AdjacentClue e x) :=
  inferInstanceAs (Decidable (x = e ∨ x = e + 1))

/-- A legal clue requests the hidden state. An illegal clue gives the opening observation. -/
@[expose] def recoveryBoard {T E : Type} (witness : T) (legal : E → T → Prop)
    [∀ e x, Decidable (legal e x)] : Board T E T (Option T) where
  opening _ := none
  source x e := if legal e x then some x else none
  target _ guess := some guess
  defaultMove := witness

/-- Gain preservation requires recovery at every legal clue. -/
theorem valid_recoveryBoard_iff {T E H : Type} (witness : T) (legal : E → T → Prop)
    [∀ e x, Decidable (legal e x)] (h : T → H) (d : H → E → T) :
    Valid .gain (recoveryBoard witness legal) h d ↔ ∀ x e, legal e x → d (h x) e = x := by
  constructor
  · intro hd x e hx
    simpa [recoveryBoard, Compatible, hx, eq_comm] using hd x e
  · intro hd x e
    by_cases hx : legal e x
    · simp [recoveryBoard, Compatible, hx, hd x e hx]
    · simp [recoveryBoard, Compatible, hx]

/-- A decoder exists exactly when the signal distinguishes every pair of distinct states
admitting a common clue. On an unused signal and clue the decoder may return the default. -/
theorem exists_valid_iff_separates {T E H : Type} (witness : T) (legal : E → T → Prop)
    [∀ e x, Decidable (legal e x)] (h : T → H) :
    (∃ d, Valid .gain (recoveryBoard witness legal) h d) ↔
      ∀ x y, (∃ e, legal e x ∧ legal e y) → h x = h y → x = y := by
  constructor
  · rintro ⟨d, hd⟩ x y ⟨e, hx, hy⟩ same
    have recover := (valid_recoveryBoard_iff witness legal h d).1 hd
    have left := recover x e hx
    rw [same] at left
    exact left.symm.trans (recover y e hy)
  · classical
    intro separates
    let d (s : H) (e : E) := if found : ∃ x, h x = s ∧ legal e x then found.choose else witness
    refine ⟨d, (valid_recoveryBoard_iff witness legal h d).2 ?_⟩
    intro x e hx
    have found : ∃ y, h y = h x ∧ legal e y := ⟨x, rfl, hx⟩
    simpa only [d, dite_eq_left found] using
      separates found.choose x ⟨e, found.choose_spec.2, hx⟩ found.choose_spec.1

/-- Distinct states are confusable if the receiver can get the same clue for both. -/
@[expose] def confusabilityGraph {T E : Type*} (legal : E → T → Prop) : SimpleGraph T where
  Adj x y := x ≠ y ∧ ∃ e, legal e x ∧ legal e y
  symm := ⟨fun _ _ ⟨ne, e, hx, hy⟩ => ⟨ne.symm, e, hy, hx⟩⟩
  loopless := ⟨fun _ adj => adj.1 rfl⟩

/-- A fixed message assignment supports recovery precisely when it underlies a proper coloring
of the confusability graph. -/
theorem exists_valid_iff_coloring {T E H : Type} (witness : T) (legal : E → T → Prop)
    [∀ e x, Decidable (legal e x)] (h : T → H) :
    (∃ d, Valid .gain (recoveryBoard witness legal) h d) ↔
      ∃ c : (confusabilityGraph legal).Coloring H, (c : T → H) = h := by
  rw [exists_valid_iff_separates]
  constructor
  · intro sep
    exact ⟨SimpleGraph.Coloring.mk h (fun {x y} adj eq => adj.1 (sep x y adj.2 eq)), rfl⟩
  · rintro ⟨c, rfl⟩ x y clue eq
    by_contra ne
    exact c.valid (show (confusabilityGraph legal).Adj x y from ⟨ne, clue⟩) eq

/-- One hidden vertex of the pentagon, with an incident edge supplied to the decoder. -/
@[expose] def singleBoard : Board (Fin 5) (Fin 5) (Fin 5) (Option (Fin 5)) :=
  recoveryBoard 0 AdjacentClue

/-- Colors 0 and 1 alternate along four vertices. The fifth vertex has color 2. -/
@[expose] def singleHint (x : Fin 5) : Fin 3 :=
  if x = 4 then 2 else if x.val % 2 = 0 then 0 else 1

/-- Return the endpoint of the edge bearing the received color. -/
@[expose] def singleDecoder (s : Fin 3) (e : Fin 5) : Fin 5 :=
  if singleHint e = s then e else e + 1

/-- Three colors allow recovery on every legal clue, including the wraparound edge. -/
theorem single_valid : Valid .gain singleBoard singleHint singleDecoder := by
  apply (valid_recoveryBoard_iff _ _ _ _).2
  decide

/-- The confusable pairs for a single sighting are the edges of Mathlib's five-cycle. -/
theorem confusabilityGraph_adjacentClue :
    confusabilityGraph AdjacentClue = SimpleGraph.cycleGraph 5 := by
  ext x y
  change (x ≠ y ∧ ∃ e, AdjacentClue e x ∧ AdjacentClue e y) ↔ _
  decide +revert

/-- The odd cycle needs at least three colors, hence three signal values. -/
theorem single_lower_bound (j : Nat) (h : Fin 5 → Fin j) (d : Fin j → Fin 5 → Fin 5)
    (hd : Valid .gain singleBoard h d) : 3 ≤ j := by
  obtain ⟨c, _⟩ := (exists_valid_iff_coloring 0 AdjacentClue h).1 ⟨d, hd⟩
  have lower := c.colorable.chromaticNumber_le
  rw [confusabilityGraph_adjacentClue,
    SimpleGraph.chromaticNumber_cycleGraph_of_odd 5 (by decide) (by decide)] at lower
  simpa using lower

/-- The smallest alphabet for one sighting has three signals. -/
theorem minimum_single : (minimumHint .gain singleBoard).size? = some 3 :=
  HintResult.size?_of_bounds _ single_valid single_lower_bound

/-- The navigator receives the two incident edges separately. -/
@[expose] def jointBoard :
    Board (Fin 5 × Fin 5) (Fin 5 × Fin 5) (Fin 5 × Fin 5) (Option (Fin 5 × Fin 5)) :=
  recoveryBoard (0, 0) fun e p => AdjacentClue e.1 p.1 ∧ AdjacentClue e.2 p.2

/-- One of five signals conveys both sightings, using arithmetic modulo five. -/
@[expose] def jointHint (p : Fin 5 × Fin 5) : Fin 5 := p.1 + 2 * p.2

/-- Starting at the first endpoints, advancing around the first edge adds one to the signal.
Advancing around the second adds two. The four legal offsets are zero, one, two and three. -/
@[expose] def jointDecoder (s : Fin 5) (e : Fin 5 × Fin 5) : Fin 5 × Fin 5 :=
  match (s - jointHint e).val with
  | 0 => e
  | 1 => (e.1 + 1, e.2)
  | 2 => (e.1, e.2 + 1)
  | _ => (e.1 + 1, e.2 + 1)

/-- Every pair of legal clues recovers both sightings from the joint signal. -/
theorem joint_valid : Valid .gain jointBoard jointHint jointDecoder := by
  apply (valid_recoveryBoard_iff _ _ _ _).2
  decide

/-- If two states share a possible pair of clues, a valid decoder can identify them only when
their signals differ or the states coincide. -/
theorem joint_separates {H : Type} {h : Fin 5 × Fin 5 → H}
    {d : H → Fin 5 × Fin 5 → Fin 5 × Fin 5} (hd : Valid .gain jointBoard h d)
    (p q : Fin 5 × Fin 5)
    (overlap : ∃ e : Fin 5 × Fin 5,
      (AdjacentClue e.1 p.1 ∧ AdjacentClue e.2 p.2) ∧
      (AdjacentClue e.1 q.1 ∧ AdjacentClue e.2 q.2)) (same : h p = h q) : p = q :=
  (exists_valid_iff_separates _ _ h).1 ⟨d, hd⟩ p q overlap same

end PolyFunExamples.Bargaining.Replay.Lighthouse
