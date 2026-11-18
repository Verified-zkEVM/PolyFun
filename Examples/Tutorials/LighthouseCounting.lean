/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.Lighthouse
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Prod

/-!
# Five labels are necessary for two lighthouse sightings

One label can occupy at most two cells in a pair of adjacent rows. Their columns must be
distinct and nonconsecutive in the five-cycle. Counting all five row pairs counts every cell
twice, so one label covers at most five cells. The whole board has 25 cells.
-/

public section

namespace PolyFunExamples.Bargaining.Replay.Lighthouse

private theorem separated_columns (s : Finset (Fin 5)) (hs : ∀ j ∈ s, j + 1 ∉ s) :
    s.card ≤ 2 := by
  decide +revert

variable {k : Nat} (h : Fin 5 × Fin 5 → Fin k)
  (sep : ∀ p q : Fin 5 × Fin 5,
    (∃ e : Fin 5 × Fin 5,
      (AdjacentClue e.1 p.1 ∧ AdjacentClue e.2 p.2) ∧
      (AdjacentClue e.1 q.1 ∧ AdjacentClue e.2 q.2)) → h p = h q → p = q)

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
/-- The explicit five-label code attains the minimum among all joint hints and decoders. -/
theorem minimum_joint : (minimumHint .gain jointBoard).size? = some 5 := by
  apply HintResult.size?_of_bounds _ joint_valid
  intro j hint decoder hd
  exact joint_lower_bound hint (joint_separates hd)

end PolyFunExamples.Bargaining.Replay.Lighthouse
