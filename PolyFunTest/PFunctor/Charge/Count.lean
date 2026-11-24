/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import PolyFun.PFunctor.Free.Cost.Count

/-!
# Counting contracts

Checks for `PolyFun.PFunctor.Free.Cost.Count`:

* natural numbers, finitely supported counts over infinitely many kinds and pointwise counts over
  finitely many kinds are counting cost types, and their totals are sums;
* in `ℕ∞`, every program meets the budget `⊤`. Under any partial order, `ℕ∞` is not a counting
  cost type, because `⊤ + ⊤ = ⊤` gives `⊤` total `0`;
* under any partial order, a nonzero natural number has a nonzero total. A pair with an integer
  component is not a counting cost type. So no coarse order hides a cost;
* a program that queries a random oracle on an infinite domain meets a counting contract, and the
  contract bounds its calls. The contract holds for a larger budget, under an uncharged map on
  inputs and for a composite;
* per-kind contracts bound each kind of query, and their total bounds all of them;
* in a family with one more kind for each member, every budget has a finite total, but the totals
  grow without bound. A uniform bound on the totals bounds the calls of the whole family.

`PolyFunTest/PFunctor/Charge/Basic.lean` rejects the contract hazards next to the examples that
show them.
-/

@[expose] public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeCount

/-! ## Counting cost types -/

example : Nonempty (CountCost ℕ) := ⟨inferInstance⟩

example : Nonempty (CountCost (ℕ →₀ ℕ)) := ⟨inferInstance⟩

example : Nonempty (CountCost (Fin 3 → ℕ)) := ⟨inferInstance⟩

example : CountCost.total (5 : ℕ) = 5 := by simp

example : CountCost.total (Finsupp.single 7 2 + Finsupp.single 9 1 : ℕ →₀ ℕ) = 3 := by simp

example : CountCost.total (fun b => if b then 2 else 1 : Bool → ℕ) = 3 := by
  simp

/-- In `ℕ∞`, every program meets the budget `⊤`, however many calls it makes. -/
example (M : MeasuredProgram ℕ Bool ℕ∞) : M.CostAtMost ⊤ :=
  fun _ _ => le_top

/-- Under any partial order, `ℕ∞` is not a counting cost type: the total of `⊤` would equal its
double. -/
example (order : PartialOrder ℕ∞) : IsEmpty (@CountCost ℕ∞ _ order) := ⟨fun _ => by
  have h : CountCost.total (⊤ : ℕ∞) = CountCost.total (⊤ + ⊤ : ℕ∞) := by rw [top_add]
  rw [map_add] at h
  exact absurd ((CountCost.total_eq_zero_iff (a := (⊤ : ℕ∞))).1 (by omega)) (by simp)⟩

/-! ## Coarse orders

A counting map is injective, so no order on a counting cost type can forget part of a cost. -/

/-- Under any counting instance on `ℕ`, whatever its partial order, the total of `5` is not `0`. -/
example (order : PartialOrder ℕ) (_ : @CountCost ℕ _ order) : CountCost.total (5 : ℕ) ≠ 0 :=
  fun h => absurd (CountCost.total_eq_zero_iff.1 h) (by decide)

/-- Under any partial order, a pair of a count and a signed integer is not a counting cost type:
the integer component cancels. -/
example (order : PartialOrder (ℕ × ℤ)) : IsEmpty (@CountCost (ℕ × ℤ) _ order) :=
  ⟨fun _ => absurd (CountCost.eq_zero_of_add_eq_zero
    (show ((0 : ℕ), (1 : ℤ)) + (0, -1) = 0 by decide)) (by decide)⟩

/-! ## An oracle on an infinite domain -/

/-- Queries to a random oracle on `ℕ`, one answer bit each. -/
abbrev Oracle : PFunctor.{0, 0} := ⟨ℕ, fun _ => Bool⟩

/-- Three queries at distinct points, each costing one call. -/
def threeQueries : MeasuredProgram Unit Bool ℕ where
  View := Unit
  view := id
  Op := ℕ
  spec _ _ := Bool
  program _ := do
    let _ ← FreeM.lift (P := Oracle) 0
    let _ ← FreeM.lift (P := Oracle) 7
    FreeM.lift (P := Oracle) 1000
  answer _ n := n % 2 == 0
  cost _ := 1

theorem threeQueries_countAtMost : threeQueries.CountAtMost 3 :=
  MeasuredProgram.CostAtMost.countAtMost fun _ p => by
    rcases p with ⟨_, _, _, ⟨⟩⟩
    exact le_rfl

/-- The contract bounds the number of calls on every completed path. -/
example (v : Unit) (p : Path (threeQueries.program v)) : Path.length _ p ≤ 3 := by
  simpa using threeQueries_countAtMost.length_le_total (fun _ => one_ne_zero) v p

/-- A program with no operations meets the contract `0`, whatever it computes. -/
example : (MeasuredProgram.ofFun (ω := ℕ) fun n : ℕ => n ^ n).CountAtMost 0 :=
  MeasuredProgram.countAtMost_ofFun _

/-- Every call is charged, so no smaller budget holds. -/
example : ¬ threeQueries.CountAtMost 2 := fun h =>
  absurd (h.costAtMost () ⟨true, true, true, ⟨⟩⟩) (by decide)

/-- A larger budget keeps the contract. -/
example : threeQueries.CountAtMost 5 :=
  threeQueries_countAtMost.mono (by decide)

/-- The three queries, run twice. The second run ignores the result of the first. -/
abbrev twice : MeasuredProgram Unit Bool ℕ :=
  (threeQueries.contramap fun _ : Bool => ()).comp threeQueries

/-- The composite meets the sum of the two budgets. -/
theorem twice_countAtMost : twice.CountAtMost (3 + 3) :=
  (threeQueries_countAtMost.contramap _).comp threeQueries_countAtMost

/-- The composite makes at most six calls on every completed path. -/
example (v : Unit) (p : Path (twice.program v)) : Path.length _ p ≤ 6 := by
  simpa using twice_countAtMost.length_le_total
    (fun o => by rcases o with ⟨_, _⟩ | ⟨_, _⟩ <;> exact one_ne_zero) v p

/-- Every call of the composite is charged, so no smaller budget holds. -/
example : ¬ twice.CountAtMost 5 := fun h =>
  absurd (h.costAtMost () ⟨true, true, true, true, true, true, ⟨⟩⟩) (by decide)

/-! ## Per-kind counts -/

/-- A hash oracle on `ℕ` (`true`) and a group operation on `ℕ` (`false`). -/
abbrev Ops : PFunctor.{0, 0} := ⟨Bool × ℕ, fun _ => ℕ⟩

/-- Two hashes and one group operation, each kind counted separately. -/
def hashHashGroup : MeasuredProgram ℕ ℕ (Bool → ℕ) where
  View := ℕ
  view := id
  Op := Bool × ℕ
  spec _ _ := ℕ
  program v := do
    let h ← FreeM.lift (P := Ops) (true, v)
    let h' ← FreeM.lift (P := Ops) (true, h)
    FreeM.lift (P := Ops) (false, h + h')
  answer _ o := o.2 + 1
  cost o := Pi.single o.1 1

/-- The per-kind budget: two hashes and one group operation. -/
def hashGroupBudget : Bool → ℕ := fun b => if b then 2 else 1

theorem hashHashGroup_countAtMost : hashHashGroup.CountAtMost hashGroupBudget :=
  MeasuredProgram.CostAtMost.countAtMost fun _ p => by
    rcases p with ⟨_, _, _, ⟨⟩⟩
    intro b
    cases b <;> exact le_rfl

/-- The total of the per-kind budget bounds all calls. -/
example (v : ℕ) (p : Path (hashHashGroup.program v)) : Path.length _ p ≤ 3 := by
  have h := hashHashGroup_countAtMost.length_le_total (fun o => by simp [hashHashGroup]) v p
  simpa [hashGroupBudget] using h

/-! ## Families -/

/-- Each member's budget has a finite total, but the totals grow with the number of kinds. -/
example (N : ℕ) : ∃ n, N < CountCost.total (fun _ => 1 : Fin n → ℕ) :=
  ⟨N + 1, by simp⟩

/-- A uniform bound on the totals of the budgets bounds the calls of the whole family. -/
example {M : (n : ℕ) → MeasuredProgram Unit Bool (Fin n → ℕ)} {B : (n : ℕ) → Fin n → ℕ} {N : ℕ}
    (h : ∀ n, (M n).CountAtMost (B n)) (hcost : ∀ n o, (M n).cost o ≠ 0)
    (hB : ∀ n, CountCost.total (B n) ≤ N) (n : ℕ) (v : (M n).View) (p : Path ((M n).program v)) :
    Path.length _ p ≤ N :=
  ((h n).length_le_total (hcost n) v p).trans (hB n)

end PolyFunTest.ChargeCount
