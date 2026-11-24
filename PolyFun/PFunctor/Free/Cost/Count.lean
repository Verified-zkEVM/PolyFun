/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import PolyFun.PFunctor.Free.Cost.Measured
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight

/-!
# Counting contracts

`MeasuredProgram.CostAtMost` is defined for any ordered cost type, so its laws also cover signed,
reversed and idempotent valuations. Such a valuation does not bound use. With a negative price, a
refund call meets any budget. Under the reversed order, every program meets the budget `0`. With
`max` as addition, a budget bounds only the largest price. With one count per kind over infinitely
many kinds, a pointwise budget does not bound the total.

A counting cost type, `CountCost ω`, excludes these valuations. It gives an additive map `count`
from `ω` into finitely supported natural-number counts, one count per kind. The map preserves and
reflects the order of `ω`, which is a partial order, so it is an order embedding
(`CountCost.count_le_count_iff`, `CountCost.count_injective`). So `ω` has the addition and the
order of a submonoid of natural-number counts. Instances cover `ℕ`, `K →₀ ℕ` for any `K`, and
`K → ℕ` for finite `K` (`nonempty_countCost_pi_iff`). In a counting cost type, adding a cost
never decreases it (`CountCost.le_self_add`). If a sum of two costs is `0`, the first cost is `0`
(`CountCost.eq_zero_of_add_eq_zero`). The total of a cost, `CountCost.total`, is the
`Finsupp.degree` of its counts. It is a natural number that is zero only at zero
(`CountCost.total_eq_zero_iff`).

`MeasuredProgram.CountAtMost B` is the contract form of `CostAtMost B`. On every completed path of
every view's program, the count of each kind is at most its count in `B`. It is equivalent to
`CostAtMost B` (`countAtMost_iff_costAtMost`), so the laws of `CostAtMost` transfer. Under it,
every completed path makes at most `total B` calls of nonzero price
(`CountAtMost.charge_indicator_le_total`). When every price is nonzero, this bounds the number of
calls (`CountAtMost.length_le_total`). The operations of the program can form an infinite type,
such as the queries to a random oracle on an infinite domain. Only the kinds of count must be
finite or finitely supported.

The contract bounds only the charges of the program's declared operations. The view, the answering
function and the code between calls are not charged, and an operation of price `0` is free. So
`ofFun f` meets the contract `0` for every `f` (`countAtMost_ofFun`).

In a family of programs, every member can meet its contract while the totals of the budgets grow
without bound. An example is `n` kinds at count `1` each. A uniform bound on the totals of the
budgets bounds the calls of the whole family.
-/

@[expose] public section

universe u w uI uI'

namespace PFunctor

/-- A cost type of counts: an additive map into finitely supported natural-number counts, one
count per kind, that preserves and reflects the order. -/
class CountCost (ω : Type w) [AddZeroClass ω] [PartialOrder ω] where
  /-- The kinds that are counted. -/
  Kind : Type w
  /-- The count of each kind. -/
  count : ω →+ (Kind →₀ ℕ)
  /-- Counts compare as their costs do. -/
  count_le_count_iff {a b : ω} : count a ≤ count b ↔ a ≤ b

namespace CountCost

attribute [simp] count_le_count_iff

section Basic

variable {ω : Type w} [AddZeroClass ω] [PartialOrder ω] [CountCost ω]

/-- Distinct costs have distinct counts. -/
theorem count_injective : Function.Injective (count : ω → Kind ω →₀ ℕ) := fun _ _ h =>
  le_antisymm (count_le_count_iff.1 h.le) (count_le_count_iff.1 h.ge)

/-- Adding a cost never decreases it. -/
protected theorem le_self_add (a b : ω) : a ≤ a + b := by
  rw [← count_le_count_iff, map_add]
  exact _root_.le_self_add

/-- If a sum of two costs is `0`, the first cost is `0`. -/
protected theorem eq_zero_of_add_eq_zero {a b : ω} (h : a + b = 0) : a = 0 := by
  refine count_injective ?_
  have hc : count a + count b = 0 := by rw [← map_add, h, map_zero]
  rw [map_zero]
  exact (Finsupp.add_eq_zero_iff _ _).1 hc |>.1

/-- The total count of all kinds: the degree of the counts. -/
noncomputable def total : ω →+ ℕ :=
  Finsupp.degree.comp count

/-- The total of a cost is the degree of its counts. -/
theorem total_apply (a : ω) : total a = (count a).degree :=
  rfl

/-- A larger cost has a larger total. -/
theorem total_le_total {a b : ω} (h : a ≤ b) : total a ≤ total b :=
  Finsupp.degree_mono (count_le_count_iff.2 h)

/-- The total of a cost is `0` only at `0`. -/
theorem total_eq_zero_iff {a : ω} : total a = 0 ↔ a = 0 :=
  (Finsupp.degree_eq_zero_iff _).trans (map_eq_zero_iff count count_injective)

/-- A nonzero cost has total at least `1`. -/
theorem one_le_total_iff {a : ω} : 1 ≤ total a ↔ a ≠ 0 := by
  rw [Nat.one_le_iff_ne_zero, Ne, total_eq_zero_iff]

/-- Adding on the left preserves the order of a counting cost type. -/
theorem addLeftMono : AddLeftMono ω :=
  ⟨fun c a b h => by
    rw [← count_le_count_iff, map_add, map_add]
    exact add_le_add_right (count_le_count_iff.2 h) _⟩

/-- Adding on the right preserves the order of a counting cost type. -/
theorem addRightMono : AddRightMono ω :=
  ⟨fun c a b h => by
    change a + c ≤ b + c
    rw [← count_le_count_iff, map_add, map_add]
    exact add_le_add_left (count_le_count_iff.2 h) _⟩

end Basic

/-! ## Instances -/

/-- Natural numbers count one kind. -/
noncomputable instance instNat : CountCost ℕ where
  Kind := Unit
  count := Finsupp.singleAddHom ()
  count_le_count_iff := Finsupp.single_le_single

/-- Finitely supported counts count their own kinds. -/
noncomputable instance instFinsupp {K : Type u} : CountCost (K →₀ ℕ) where
  Kind := K
  count := AddMonoidHom.id _
  count_le_count_iff := Iff.rfl

/-- Pointwise counts over finitely many kinds count their own kinds. -/
noncomputable instance instPi {K : Type u} [Finite K] : CountCost (K → ℕ) where
  Kind := K
  count := Finsupp.addEquivFunOnFinite.symm.toAddMonoidHom
  count_le_count_iff := Finsupp.coe_le_coe

/-- The total of a natural number is itself. -/
@[simp]
theorem total_nat (n : ℕ) : total n = n :=
  Finsupp.degree_single () n

/-- The total of finitely supported counts is their degree. -/
@[simp]
theorem total_finsupp {K : Type u} (f : K →₀ ℕ) : total f = f.degree :=
  rfl

/-- The total of pointwise counts over finitely many kinds is their sum. -/
@[simp]
theorem total_pi {K : Type u} [Fintype K] (v : K → ℕ) : total v = ∑ k, v k :=
  Finsupp.degree_eq_sum _

/-- Pointwise counts form a counting cost type exactly over finitely many kinds. Over infinitely
many kinds, the budget `1` of every kind bounds no total. -/
theorem nonempty_countCost_pi_iff {K : Type u} : Nonempty (CountCost (K → ℕ)) ↔ Finite K := by
  refine ⟨fun ⟨_⟩ => ?_, fun _ => ⟨instPi⟩⟩
  by_contra hK
  have : Infinite K := not_finite_iff_infinite.1 hK
  classical
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq K (total (1 : K → ℕ) + 1)
  have hle : ∑ k ∈ s, Pi.single k 1 ≤ (1 : K → ℕ) := fun i => by
    rw [Finset.sum_apply]
    simp only [Pi.single_apply, Finset.sum_ite_eq, Pi.one_apply]
    split_ifs <;> simp
  have hsum : s.card ≤ total (∑ k ∈ s, Pi.single k 1 : K → ℕ) := by
    rw [map_sum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun k _ => one_le_total_iff.2 fun h => by simpa using congrFun h k
  have := hsum.trans (total_le_total hle)
  omega

end CountCost

namespace FreeM.MeasuredProgram

variable {Input : Type uI} {Mid Result : Type u} {ω : Type w}

/-- On every completed path of every view's program, the count of each kind is at most its count
in `B`. The contract bounds only the charges of the program's declared operations. The view, the
answering function and the code between calls are not charged. -/
def CountAtMost [AddMonoid ω] [PartialOrder ω] [CountCost ω] (M : MeasuredProgram Input Result ω)
    (B : ω) : Prop :=
  ∀ v (p : Path (M.program v)),
    CountCost.count (Path.charge M.cost (M.program v) p) ≤ CountCost.count B

variable [AddMonoid ω] [PartialOrder ω] [CountCost ω] {M : MeasuredProgram Input Result ω} {B : ω}

/-- A counting contract is a cost bound, and conversely. -/
theorem countAtMost_iff_costAtMost : M.CountAtMost B ↔ M.CostAtMost B :=
  forall₂_congr fun _ _ => CountCost.count_le_count_iff

alias ⟨CountAtMost.costAtMost, CostAtMost.countAtMost⟩ := countAtMost_iff_costAtMost

/-- A counting contract holds for every larger budget. -/
theorem CountAtMost.mono (h : M.CountAtMost B) {B' : ω} (hB : B ≤ B') : M.CountAtMost B' :=
  (h.costAtMost.mono hB).countAtMost

/-- A program with no operations meets the counting contract `0`. -/
theorem countAtMost_ofFun {Input : Type u} (f : Input → Result) :
    (ofFun f (ω := ω)).CountAtMost 0 :=
  (costAtMost_ofFun f).countAtMost

/-- Precomposing an uncharged map on inputs keeps a counting contract. -/
theorem CountAtMost.contramap {Input' : Type uI'} (h : M.CountAtMost B) (g : Input' → Input) :
    (M.contramap g).CountAtMost B :=
  h

/-- Composite counting contracts add: the inner budget, then the outer one. -/
theorem CountAtMost.comp {outer : MeasuredProgram Mid Result ω}
    {inner : MeasuredProgram Input Mid ω} {outerBudget innerBudget : ω}
    (ho : outer.CountAtMost outerBudget) (hi : inner.CountAtMost innerBudget) :
    (outer.comp inner).CountAtMost (innerBudget + outerBudget) :=
  haveI := CountCost.addLeftMono (ω := ω)
  haveI := CountCost.addRightMono (ω := ω)
  (ho.costAtMost.comp hi.costAtMost).countAtMost

/-- Under a counting contract, the total count of every completed path is at most the total of
the budget. -/
theorem CountAtMost.total_charge_le (h : M.CountAtMost B) (v : M.View)
    (p : Path (M.program v)) :
    CountCost.total (Path.charge M.cost (M.program v) p) ≤ CountCost.total B :=
  CountCost.total_le_total (CountCost.count_le_count_iff.1 (h v p))

/-- Under a counting contract, every completed path makes at most `total B` calls of nonzero
price. -/
theorem CountAtMost.charge_indicator_le_total (h : M.CountAtMost B) (v : M.View)
    (p : Path (M.program v)) :
    Path.charge ({o | M.cost o ≠ 0}.indicator 1) (M.program v) p ≤ CountCost.total B := by
  refine (Path.charge_mono (fun o => ?_) _ p).trans
    ((Path.charge_map_addMonoidHom CountCost.total _ p).trans_le (h.total_charge_le v p))
  by_cases ho : M.cost o = 0
  · simp [ho]
  · simpa [ho] using CountCost.one_le_total_iff.2 ho

/-- Under a counting contract with nonzero prices, every completed path makes at most `total B`
calls. -/
theorem CountAtMost.length_le_total (h : M.CountAtMost B) (hcost : ∀ o, M.cost o ≠ 0)
    (v : M.View) (p : Path (M.program v)) :
    Path.length (M.program v) p ≤ CountCost.total B := by
  have hcalls := h.charge_indicator_le_total v p
  rw [show {o | M.cost o ≠ 0} = Set.univ from Set.eq_univ_of_forall hcost,
    Set.indicator_univ] at hcalls
  rw [Path.length_eq_charge_one]
  exact hcalls

end FreeM.MeasuredProgram

end PFunctor
