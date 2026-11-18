/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.Lighthouse.Coding
public import Examples.Tutorials.MinimumHint

/-!
# Lighthouse recovery as a ferry board

A legal clue asks the decoder to reproduce a sighting. On this board, preserving gains is
equivalent to recovering the sighting on every legal clue. The optimal lighthouse codes
therefore give certificates for the minimum-hint solver.
-/

public section

namespace PolyFunExamples.Bargaining.Replay.Lighthouse

export PolyFunExamples.Lighthouse (AdjacentClue instDecidableAdjacentClue confusabilityGraph
  confusabilityGraph_adjacentClue singleHint singleDecoder jointHint jointDecoder)

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
    Valid .gain (recoveryBoard witness legal) h d ↔
      PolyFunExamples.Lighthouse.Recovers legal h d := by
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
  simp only [valid_recoveryBoard_iff]
  exact PolyFunExamples.Lighthouse.exists_recovers_iff_separates witness legal h

/-- A fixed message assignment supports recovery precisely when it underlies a proper coloring
of the confusability graph. -/
theorem exists_valid_iff_coloring {T E H : Type} (witness : T) (legal : E → T → Prop)
    [∀ e x, Decidable (legal e x)] (h : T → H) :
    (∃ d, Valid .gain (recoveryBoard witness legal) h d) ↔
      ∃ c : (confusabilityGraph legal).Coloring H, (c : T → H) = h := by
  simp only [valid_recoveryBoard_iff]
  exact PolyFunExamples.Lighthouse.exists_recovers_iff_coloring witness legal h

/-- One hidden vertex of the pentagon, with an incident edge supplied to the decoder. -/
@[expose] def singleBoard : Board (Fin 5) (Fin 5) (Fin 5) (Option (Fin 5)) :=
  recoveryBoard 0 AdjacentClue

/-- The three-label code preserves gains on the single-sighting board. -/
theorem single_valid : Valid .gain singleBoard singleHint singleDecoder :=
  (valid_recoveryBoard_iff _ _ _ _).2 PolyFunExamples.Lighthouse.single_recovers

/-- The odd cycle needs at least three colors, hence three signal values. -/
theorem single_lower_bound (j : Nat) (h : Fin 5 → Fin j) (d : Fin j → Fin 5 → Fin 5)
    (hd : Valid .gain singleBoard h d) : 3 ≤ j := by
  exact PolyFunExamples.Lighthouse.single_optimal.2 ⟨h, d, (valid_recoveryBoard_iff _ _ _ _).1 hd⟩

/-- The smallest alphabet for one sighting has three signals. -/
theorem minimum_single : (minimumHint .gain singleBoard).size? = some 3 :=
  HintResult.size?_of_bounds _ single_valid single_lower_bound

/-- The navigator receives the two incident edges separately. -/
@[expose] def jointBoard :
    Board (Fin 5 × Fin 5) (Fin 5 × Fin 5) (Fin 5 × Fin 5) (Option (Fin 5 × Fin 5)) :=
  recoveryBoard (0, 0) fun e p => AdjacentClue e.1 p.1 ∧ AdjacentClue e.2 p.2

/-- The five-label code preserves gains on the two-sighting board. -/
theorem joint_valid : Valid .gain jointBoard jointHint jointDecoder :=
  (valid_recoveryBoard_iff _ _ _ _).2 PolyFunExamples.Lighthouse.joint_recovers

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
