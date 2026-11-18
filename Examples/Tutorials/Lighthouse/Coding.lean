/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Fintype.Prod
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Two sightings from five lighthouses

The sender sees which lighthouse flashed. The receiver sees an edge of the pentagon containing
the flash. One sighting needs three labels. Sending two sightings jointly needs only five. The
four possible pairs at the receiver's two edges have distinct labels.
-/

public section

namespace PolyFunExamples.Lighthouse

/-- A code recovers the sighting for every clue that the receiver could see. -/
abbrev Recovers {T E H : Type*} (legal : E → T → Prop) (encode : T → H)
    (decode : H → E → T) : Prop :=
  ∀ x e, legal e x → decode (encode x) e = x

/-- A decoder exists exactly when the signal distinguishes every pair of distinct states
admitting a common clue. On an unused signal and clue the decoder may return the default. -/
theorem exists_recovers_iff_separates {T E H : Type*} (witness : T) (legal : E → T → Prop)
    (h : T → H) :
    (∃ d, Recovers legal h d) ↔
      ∀ x y, (∃ e, legal e x ∧ legal e y) → h x = h y → x = y := by
  constructor
  · rintro ⟨d, hd⟩ x y ⟨e, hx, hy⟩ same
    have left := hd x e hx
    rw [same] at left
    exact left.symm.trans (hd y e hy)
  · classical
    intro separates
    let d (s : H) (e : E) := if found : ∃ x, h x = s ∧ legal e x then found.choose else witness
    refine ⟨d, ?_⟩
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
theorem exists_recovers_iff_coloring {T E H : Type*} (witness : T) (legal : E → T → Prop)
    (h : T → H) :
    (∃ d, Recovers legal h d) ↔
      ∃ c : (confusabilityGraph legal).Coloring H, (c : T → H) = h := by
  rw [exists_recovers_iff_separates witness]
  constructor
  · intro sep
    exact ⟨SimpleGraph.Coloring.mk h (fun {x y} adj eq => adj.1 (sep x y adj.2 eq)), rfl⟩
  · rintro ⟨c, rfl⟩ x y clue eq
    by_contra ne
    exact c.valid (show (confusabilityGraph legal).Adj x y from ⟨ne, clue⟩) eq

/-! ## One sighting -/

/-- The clue names an edge by its clockwise starting point. -/
@[expose] def AdjacentClue (e x : Fin 5) : Prop := x = e ∨ x = e + 1

instance instDecidableAdjacentClue (e x : Fin 5) : Decidable (AdjacentClue e x) :=
  inferInstanceAs (Decidable (x = e ∨ x = e + 1))

/-- Colors 0 and 1 alternate along four vertices. The fifth vertex has color 2. -/
@[expose] def singleHint (x : Fin 5) : Fin 3 :=
  if x = 4 then 2 else if x.val % 2 = 0 then 0 else 1

/-- Return the endpoint of the edge bearing the received color. -/
@[expose] def singleDecoder (s : Fin 3) (e : Fin 5) : Fin 5 :=
  if singleHint e = s then e else e + 1

/-- Three colors allow recovery on every legal clue, including the wraparound edge. -/
theorem single_recovers : Recovers AdjacentClue singleHint singleDecoder := by decide

/-- The confusable pairs for a single sighting are the edges of Mathlib's five-cycle. -/
theorem confusabilityGraph_adjacentClue :
    confusabilityGraph AdjacentClue = SimpleGraph.cycleGraph 5 := by
  ext x y
  change (x ≠ y ∧ ∃ e, AdjacentClue e x ∧ AdjacentClue e y) ↔ _
  decide +revert

/-- The odd cycle needs at least three colors, hence three signal values. -/
private theorem single_lower_bound (j : Nat) (h : Fin 5 → Fin j) (d : Fin j → Fin 5 → Fin 5)
    (hd : Recovers AdjacentClue h d) : 3 ≤ j := by
  obtain ⟨c, _⟩ := (exists_recovers_iff_coloring 0 AdjacentClue h).1 ⟨d, hd⟩
  have lower := c.colorable.chromaticNumber_le
  rw [confusabilityGraph_adjacentClue,
    SimpleGraph.chromaticNumber_cycleGraph_of_odd 5 (by decide) (by decide)] at lower
  simpa using lower

/-- Three is the least alphabet size that allows recovery of one sighting. -/
theorem single_optimal :
    IsLeast {k : ℕ | ∃ (encode : Fin 5 → Fin k) (decode : Fin k → Fin 5 → Fin 5),
      Recovers AdjacentClue encode decode} 3 := by
  refine ⟨⟨singleHint, singleDecoder, single_recovers⟩, ?_⟩
  rintro k ⟨encode, decode, hd⟩
  exact single_lower_bound k encode decode hd

/-! ## Two sightings -/

/-- The receiver has an incident edge for each of the two sightings. -/
abbrev JointClue (e p : Fin 5 × Fin 5) : Prop :=
  AdjacentClue e.1 p.1 ∧ AdjacentClue e.2 p.2

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
theorem joint_recovers : Recovers JointClue jointHint jointDecoder := by decide

private theorem separated_columns (s : Finset (Fin 5)) (hs : ∀ j ∈ s, j + 1 ∉ s) :
    s.card ≤ 2 := by
  decide +revert

variable {k : Nat} (h : Fin 5 × Fin 5 → Fin k)
  (sep : ∀ p q : Fin 5 × Fin 5,
    (∃ e, JointClue e p ∧ JointClue e q) → h p = h q → p = q)

include sep

/-- A single hint label can cover at most five of the 25 joint sightings. -/
theorem joint_fiber_card_le (c : Fin k) :
    (Finset.univ.filter (fun p => h p = c)).card ≤ 5 := by
  let cells := Finset.univ.filter (fun p => h p = c)
  let inRows (p : Fin 5 × Fin 5) (r : Fin 5) := AdjacentClue r p.1
  have twoRows (p : Fin 5 × Fin 5) :
      2 ≤ (Finset.univ.bipartiteAbove inRows p).card := by
    change 2 ≤ (Finset.univ.filter (fun r => AdjacentClue r p.1)).card
    obtain ⟨i, j⟩ := p
    change 2 ≤ (Finset.univ.filter (fun r => AdjacentClue r i)).card
    decide +revert
  have stripBound (r : Fin 5) : (cells.bipartiteBelow inRows r).card ≤ 2 := by
    let strip := cells.bipartiteBelow inRows r
    have unique {p q : Fin 5 × Fin 5} (hp : p ∈ strip) (hq : q ∈ strip)
        (j : Fin 5) (hpj : AdjacentClue j p.2) (hqj : AdjacentClue j q.2) : p = q := by
      obtain ⟨pc, pr⟩ := (Finset.mem_bipartiteBelow inRows).mp hp
      obtain ⟨qc, qr⟩ := (Finset.mem_bipartiteBelow inRows).mp hq
      exact sep p q ⟨(r, j), ⟨pr, hpj⟩, ⟨qr, hqj⟩⟩
        ((Finset.mem_filter.mp pc).2.trans (Finset.mem_filter.mp qc).2.symm)
    have distinct : Set.InjOn Prod.snd (strip : Set (Fin 5 × Fin 5)) := by
      intro p hp q hq he
      exact unique hp hq p.2 (Or.inl rfl) (Or.inl he.symm)
    change strip.card ≤ 2
    rw [← Finset.card_image_of_injOn distinct]
    apply separated_columns
    intro j hj hnext
    obtain ⟨p, hp, jp⟩ := Finset.mem_image.mp hj
    obtain ⟨q, hq, jq⟩ := Finset.mem_image.mp hnext
    have eq := unique hp hq j (Or.inl jp) (Or.inr jq)
    have same : j = j + 1 := jp.symm.trans ((congrArg Prod.snd eq).trans jq)
    exact (show ∀ i : Fin 5, i ≠ i + 1 by decide) j same
  have count := Finset.card_mul_le_card_mul inRows (s := cells) (t := Finset.univ)
    (fun p _ => twoRows p) (fun r _ => stripBound r)
  change cells.card ≤ 5
  simpa using (Nat.le_of_mul_le_mul_right count (by decide : 0 < 2))

/-- A hint that distinguishes every pair of sightings compatible with a common pair of clues
requires at least five labels. -/
theorem joint_lower_bound : 5 ≤ k := by
  have count := Finset.card_le_mul_card_image_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := h) (fun _ _ => Finset.mem_univ _)
    5 (fun c _ => joint_fiber_card_le h sep c)
  simp [Fintype.card_prod] at count
  omega

omit sep in
/-- Five is the least alphabet size that allows recovery of both sightings. -/
theorem joint_optimal : IsLeast {k : ℕ | ∃ (encode : Fin 5 × Fin 5 → Fin k)
    (decode : Fin k → Fin 5 × Fin 5 → Fin 5 × Fin 5), Recovers JointClue encode decode} 5 := by
  refine ⟨⟨jointHint, jointDecoder, joint_recovers⟩, ?_⟩
  rintro j ⟨encode, decode, hd⟩
  apply joint_lower_bound encode
  exact (exists_recovers_iff_separates (0, 0) JointClue encode).1 ⟨decode, hd⟩

end PolyFunExamples.Lighthouse
