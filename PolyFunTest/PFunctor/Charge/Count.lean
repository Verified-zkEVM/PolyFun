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

* Natural numbers, finitely supported counts over infinitely many kinds, pointwise counts over
  finitely many kinds and pairs are counting cost types. Their totals are sums. Each of these
  types is also canonically ordered.
* In `ℕ∞`, every program meets the budget `⊤`. The equation `⊤ + ⊤ = ⊤` excludes a counting
  instance under any partial order.
* The natural numbers other than `1`, `{n : ℕ // n ≠ 1}`, have a counting instance. They are not
  canonically ordered.
* The oracle program has an infinite query domain. It meets the budget `3` but not `2`, and makes
  at most three calls. Its counting contract holds for a larger budget, under an uncharged map on
  inputs and for a composite. A program with no operations meets the budget `0`.
* The composite makes at most six calls. It does not meet the budget `5`.
* The total of `5 : ℕ` is nonzero under every counting instance. A pair with an integer component
  has no counting instance.
* On `ℕ`, let `a ≤ b` hold when `a = b` or `b = 0`. Under this partial order, three unit-price
  queries meet the budget `0`. The order has no counting instance. Every counting instance on `ℕ`
  excludes that budget.
* A counting instance on `ℕ` can double the total. Its counting contracts are the same.
* Over no kinds, every program meets the budget `0` and every total is `0`.
* A program with a free operation makes more calls than its total, so the bound on all calls needs
  nonzero prices. The bound on the calls of nonzero price is attained.
* The example with per-kind prices counts two hash queries and one group operation. The total of
  its budget bounds all of its calls. It fails a budget with the same total and one hash query.
* The budget `1` for each of `n` kinds has a finite total, but these totals exceed every bound.
  For every family over `Fin n → ℕ`, a uniform bound on the totals bounds the calls of nonzero
  price on every completed path of every member. When every price is nonzero, it bounds all
  calls.
* Inputs, results and costs live in independent universes.
* A bound on one path gives the call bound on that path. Every measured program can answer each
  of its calls.

`PolyFunTest/PFunctor/Charge/Basic.lean` rejects the other contract hazards next to the examples
that show them.
-/

@[expose] public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeCount

/-! ## Counting cost types -/

example : Nonempty (CountCost ℕ) := ⟨inferInstance⟩

example : Nonempty (CountCost (ℕ →₀ ℕ)) := ⟨inferInstance⟩

example : Nonempty (CountCost (Fin 3 → ℕ)) := ⟨inferInstance⟩

example : Nonempty (CountCost (ℕ × (Bool → ℕ))) := ⟨inferInstance⟩

example : CountCost.total ((2, 3) : ℕ × ℕ) = 5 := by simp

example : CountCost.total ((2, fun b => if b then 1 else 4) : ℕ × (Bool → ℕ)) = 7 := by simp

example : CanonicallyOrderedAdd (ℕ × (ℕ →₀ ℕ) × (Fin 3 → ℕ)) := inferInstance

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

/-! ## A counting cost type that is not canonically ordered

The natural numbers other than `1` are closed under addition. With the order of `ℕ`, they form a
counting cost type. -/

section NeOne

local instance : Zero {n : ℕ // n ≠ 1} := ⟨⟨0, zero_ne_one⟩⟩

/-- A sum of two natural numbers other than `1` is not `1`. -/
local instance : Add {n : ℕ // n ≠ 1} := ⟨fun a b => ⟨a + b, by have := a.2; have := b.2; omega⟩⟩

local instance : AddZeroClass {n : ℕ // n ≠ 1} :=
  Subtype.val_injective.addZeroClass _ rfl fun _ _ => rfl

/-- The natural numbers other than `1` count one kind, as `ℕ` does. -/
noncomputable local instance : CountCost {n : ℕ // n ≠ 1} where
  Kind := Unit
  count := (Finsupp.singleAddHom ()).comp ⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩
  count_le_count_iff := Finsupp.single_le_single

/-- `2 ≤ 3`, but `3 - 2 = 1` is excluded, so no `c` gives `3 = 2 + c`. -/
example : ¬ CanonicallyOrderedAdd {n : ℕ // n ≠ 1} := fun _ => by
  obtain ⟨c, hc⟩ := exists_add_of_le (show (⟨2, by decide⟩ : {n : ℕ // n ≠ 1}) ≤ ⟨3, by decide⟩
    from by decide)
  have h : 3 = 2 + c.1 := congrArg Subtype.val hc
  exact c.2 (by omega)

end NeOne

/-! ## Totals -/

/-- Natural numbers, with every cost counted twice. -/
@[instance_reducible]
noncomputable def doubled : CountCost ℕ where
  Kind := Unit
  count := (Finsupp.singleAddHom ()).comp (nsmulAddMonoidHom 2)
  count_le_count_iff := Finsupp.single_le_single.trans (by simp)

/-- The total depends on the instance. -/
example : @CountCost.total ℕ _ _ doubled 5 = 10 := by
  rw [@CountCost.total_apply ℕ _ _ doubled]
  exact Finsupp.degree_single () 10

/-- The counting contract does not depend on the instance. -/
example (M : MeasuredProgram ℕ Bool ℕ) (B : ℕ) :
    @MeasuredProgram.CountAtMost ℕ Bool ℕ _ _ doubled M B ↔ M.CountAtMost B :=
  (@MeasuredProgram.countAtMost_iff_costAtMost ℕ Bool ℕ _ _ doubled M B).trans
    MeasuredProgram.countAtMost_iff_costAtMost.symm

/-- Over no kinds, every program meets the budget `0`: no call has a nonzero price. -/
example (M : MeasuredProgram ℕ Bool (Empty → ℕ)) : M.CountAtMost 0 :=
  fun _ _ => CountCost.count_le_count_iff.2 (Subsingleton.elim _ _).le

example (B : Empty → ℕ) : CountCost.total B = 0 := by simp

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

/-! ## Free operations -/

/-- One priced query (`true`), then one free lookup (`false`). -/
def queryThenLookup : MeasuredProgram Unit Bool ℕ where
  View := Unit
  view := id
  Op := Bool
  spec _ _ := Bool
  program _ := do
    let _ ← FreeM.lift (P := ⟨Bool, fun _ => Bool⟩) true
    FreeM.lift (P := ⟨Bool, fun _ => Bool⟩) false
  answer _ _ := true
  cost o := if o then 1 else 0

theorem queryThenLookup_countAtMost : queryThenLookup.CountAtMost 1 :=
  MeasuredProgram.CostAtMost.countAtMost fun _ p => by
    rcases p with ⟨_, _, ⟨⟩⟩
    exact le_rfl

/-- The free lookup is a call, so a budget of total `1` does not bound the number of calls. -/
example : ¬ ∀ (v : Unit) (p : Path (queryThenLookup.program v)),
    Path.length _ p ≤ CountCost.total 1 := fun h =>
  absurd (h () ⟨true, true, ⟨⟩⟩) (by rw [CountCost.total_nat]; decide)

/-- The budget bounds the calls of nonzero price. -/
example (v : Unit) (p : Path (queryThenLookup.program v)) :
    Path.charge ({o | queryThenLookup.cost o ≠ 0}.indicator 1) _ p ≤ 1 := by
  simpa using queryThenLookup_countAtMost.charge_indicator_le_total v p

/-- The query is a call of nonzero price, so the bound is attained. -/
example (v : Unit) (p : Path (queryThenLookup.program v)) :
    Path.charge ({o | queryThenLookup.cost o ≠ 0}.indicator 1) _ p = 1 := by
  rcases p with ⟨_, _, ⟨⟩⟩
  change Set.indicator {o : Bool | queryThenLookup.cost o ≠ 0} (1 : Bool → ℕ) true +
    (Set.indicator {o : Bool | queryThenLookup.cost o ≠ 0} (1 : Bool → ℕ) false + 0) = 1
  simp [queryThenLookup]

/-! ## Coarse orders

A counting map is injective, so no order on a counting cost type can forget part of a cost. -/

/-- Under any counting instance on `ℕ`, whatever its partial order, the total of `5` is not `0`. -/
example (order : PartialOrder ℕ) (_ : @CountCost ℕ _ order) : CountCost.total (5 : ℕ) ≠ 0 :=
  fun h => absurd (CountCost.total_eq_zero_iff.1 h) (by decide)

/-- Under any partial order, a pair of a count and a signed integer is not a counting cost type:
the integer component cancels. -/
example (order : PartialOrder (ℕ × ℤ)) : IsEmpty (@CountCost (ℕ × ℤ) _ order) :=
  ⟨fun _ => absurd (CountCost.add_eq_zero.1
    (show ((0 : ℕ), (1 : ℤ)) + (0, -1) = 0 by decide)).1 (by decide)⟩

/-- A coarse partial order on `ℕ`: `a ≤ b` when `a = b` or `b = 0`. -/
@[instance_reducible]
def coarse : PartialOrder ℕ where
  le a b := a = b ∨ b = 0
  lt a b := (a = b ∨ b = 0) ∧ ¬(b = a ∨ a = 0)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hbc with rfl | rfl
    · exact hab
    · exact Or.inr rfl
  le_antisymm a b hab hba := by
    rcases hab with h | h
    · exact h
    · rcases hba with h' | h' <;> omega

/-- Under the coarse partial order, three unit-price calls meet the budget `0`. -/
example : @MeasuredProgram.CostAtMost Unit Bool ℕ _ _ coarse.toLE threeQueries 0 :=
  fun _ _ => Or.inr rfl

/-- The coarse partial order has no counting instance: it puts `3` below `0`. -/
example : IsEmpty (@CountCost ℕ _ coarse) := ⟨fun inst => by
  have h : @LE.le ℕ coarse.toLE 3 0 := Or.inr rfl
  have hz := @CountCost.total_le_total ℕ _ coarse inst _ _ h
  rw [map_zero, Nat.le_zero, @CountCost.total_eq_zero_iff ℕ _ coarse inst] at hz
  exact absurd hz (by decide)⟩

/-- Every counting instance on `ℕ` excludes the budget `0` for the three unit-price calls. -/
example (order : PartialOrder ℕ) (inst : @CountCost ℕ _ order) :
    ¬ @MeasuredProgram.CountAtMost Unit Bool ℕ _ order inst threeQueries 0 := fun h => by
  have hzero := CountCost.total_le_total
    (CountCost.count_le_count_iff.1 (h () ⟨true, true, true, ⟨⟩⟩))
  rw [map_zero, Nat.le_zero, CountCost.total_eq_zero_iff] at hzero
  exact absurd hzero (by decide)

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

/-- The counts along a path are within the budget kind by kind, so their total is within its total,
which is attained. -/
example (v : ℕ) (p : Path (hashHashGroup.program v)) :
    CountCost.total (Path.charge hashHashGroup.cost _ p) ≤ 3 := by
  simpa [hashGroupBudget] using hashHashGroup_countAtMost.total_charge_le v p

example (v : ℕ) (p : Path (hashHashGroup.program v)) :
    CountCost.total (Path.charge hashHashGroup.cost _ p) = 3 := by
  rcases p with ⟨_, _, _, ⟨⟩⟩
  rw [CountCost.total_pi]
  rfl

/-- A budget with the same total but one hash fails: the contract compares each kind. -/
example : ¬ hashHashGroup.CountAtMost fun b => if b then 1 else 2 := fun h =>
  absurd (CountCost.count_le_count_iff.1
    (h (0 : ℕ) ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), ⟨⟩⟩) true) (by decide)

/-! ## Families -/

/-- Each member's budget has a finite total, but the totals grow with the number of kinds. -/
example (N : ℕ) : ∃ n, N < CountCost.total (fun _ => 1 : Fin n → ℕ) :=
  ⟨N + 1, by simp⟩

/-- With nonzero prices, a uniform bound on budget totals bounds the calls of every member. -/
example {M : (n : ℕ) → MeasuredProgram Unit Bool (Fin n → ℕ)} {B : (n : ℕ) → Fin n → ℕ} {N : ℕ}
    (h : ∀ n, (M n).CountAtMost (B n)) (hcost : ∀ n o, (M n).cost o ≠ 0)
    (hB : ∀ n, CountCost.total (B n) ≤ N) (n : ℕ) (v : (M n).View) (p : Path ((M n).program v)) :
    Path.length _ p ≤ N :=
  ((h n).length_le_total (hcost n) v p).trans (hB n)

/-- A uniform bound on budget totals bounds the calls of nonzero price on every completed path of
every member. -/
example {M : (n : ℕ) → MeasuredProgram Unit Bool (Fin n → ℕ)} {B : (n : ℕ) → Fin n → ℕ} {N : ℕ}
    (h : ∀ n, (M n).CountAtMost (B n)) (hB : ∀ n, CountCost.total (B n) ≤ N) (n : ℕ)
    (v : (M n).View) (p : Path ((M n).program v)) :
    Path.charge ({o | (M n).cost o ≠ 0}.indicator 1) ((M n).program v) p ≤ N :=
  ((h n).charge_indicator_le_total v p).trans (hB n)

/-! ## Universes -/

/-- Inputs, results and costs live in independent universes. -/
example {Input : Type 1} {Result : Type 2} {ω : Type 3} [AddMonoid ω] [PartialOrder ω]
    [CountCost ω] {M : MeasuredProgram Input Result ω} {B : ω} (h : M.CountAtMost B)
    (hcost : ∀ o, M.cost o ≠ 0) (v : M.View) (p : Path (M.program v)) :
    Path.length (M.program v) p ≤ CountCost.total B :=
  h.length_le_total hcost v p

/-! ## Bounds on one path -/

/-- A bound on the charge of one path bounds the calls of that path, for any free program. -/
example {P : PFunctor} {α : Type} {c : P.A → ℕ} {B : ℕ} {x : FreeM P α} {p : Path x}
    (h : Path.charge c x p ≤ B) (hc : ∀ a, c a ≠ 0) : Path.length x p ≤ B := by
  simpa using Path.length_le_total hc h

/-- Every measured program can answer each of its calls. -/
example {Input Result : Type} {ω : Type} (M : MeasuredProgram Input Result ω) (v : M.View) :
    (M.program v).ProgramProgress :=
  haveI : ∀ o, Nonempty (M.spec v o) := fun o => ⟨M.answer v o⟩
  programProgress_of_nonempty _

end PolyFunTest.ChargeCount
