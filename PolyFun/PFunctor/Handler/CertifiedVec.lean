/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.PFunctor.Handler.Certified
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Vector charges, prices and demands

A charge `c : P.A → ι → ω` with values in the pointwise order on `ι → ω` counts one resource per
index `i`. Suprema and sums in `ι → ω` are pointwise, so the component `i` of the worst-case cost
is the worst-case cost at the component charge `fun a => c a i` (`costWith_pi_apply`), and a
vector bound on the cost is the family of its component bounds (`cost_le_pi_iff`). The budget
form is `isChargeBound_pi_iff`.

Two monotone additive maps convert vectors of resource counts:

* pricing at nonnegative prices `p : ι → ω`, `u ↦ ∑ i, p i * u i` (`priceHom`), turns a vector
  bound `u` into the scalar bound `∑ i, p i * u i` at the priced charge
  `fun a => ∑ i, p i * c a i` (`IsChargeBound.price`, `cost_price_le`);
* the demand map of per-resource demands `d : ι → ι' → ω`, `u ↦ ∑ i, u i • d i` (`demandHom`),
  where `d i` is the use vector over `ι'` of one unit of resource `i`.

A handler whose implementation of each call at `a` has use vector `∑ i, c a i • d i` is certified
with the demand map as its exchange (`Handler.Certified.ofDemand`). A program with use vector `u`
then runs through it with use vector `∑ i, u i • d i` (`Handler.isChargeBound_liftM_demand`), and
two such handlers compose with the composite demand (`Handler.isChargeBound_liftM_demand_comp`).
-/

@[expose] public section

universe uA uA₂ uA₃ uB uB₂ uB₃ v w

open scoped BigOperators

namespace PFunctor

/-! ## Prices and demands -/

section Hom

variable {ι ι' ι'' : Type*} [Fintype ι] {ω : Type w} [CommSemiring ω] [PartialOrder ω]
  [IsOrderedRing ω]

/-- Pricing a vector of resource counts at nonnegative prices `p`: `u ↦ ∑ i, p i * u i`. -/
def priceHom (p : ι → ω) (hp : 0 ≤ p) : (ι → ω) →+o ω where
  toFun u := ∑ i, p i * u i
  map_zero' := by simp
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  monotone' u v h := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hp i)

@[simp]
theorem priceHom_apply (p : ι → ω) (hp : 0 ≤ p) (u : ι → ω) :
    priceHom p hp u = ∑ i, p i * u i :=
  rfl

/-- The demand map of per-resource demands `d i : ι' → ω`: a use vector `u` over `ι` demands
`∑ i, u i • d i` over `ι'`. -/
def demandHom (d : ι → ι' → ω) (hd : 0 ≤ d) : (ι → ω) →+o (ι' → ω) where
  toFun u := ∑ i, u i • d i
  map_zero' := by
    funext j
    simp [Finset.sum_apply]
  map_add' u v := by
    funext j
    simp [Finset.sum_apply, add_mul, Finset.sum_add_distrib]
  monotone' u v h j := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (hd i j)

@[simp]
theorem demandHom_apply (d : ι → ι' → ω) (hd : 0 ≤ d) (u : ι → ω) :
    demandHom d hd u = ∑ i, u i • d i :=
  rfl

/-- Demands compose: the demand of the demand of `u` is `u`'s demand at the composite demands
`fun i => demandHom e he (d i)`. -/
theorem demandHom_demandHom [Fintype ι'] (d : ι → ι' → ω) (hd : 0 ≤ d) (e : ι' → ι'' → ω)
    (he : 0 ≤ e) (u : ι → ω) :
    demandHom e he (demandHom d hd u) = ∑ i, u i • demandHom e he (d i) := by
  funext k
  simp only [demandHom_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end Hom

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v} {ι : Type*} {ω : Type w}

/-! ## Vector costs -/

section Vector

variable [AddCommMonoid ω] [CompleteLattice ω]

/-- The component `i` of the cost at a vector charge is the cost at the component `i` of the
charge, with the component `i` of the leaf costs. -/
theorem costWith_pi_apply (c : P.A → ι → ω) (x : FreeM P α) (k : α → ι → ω) (i : ι) :
    costWith c x k i = costWith (fun a => c a i) x fun r => k r i := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih => simp only [costWith_liftBind, Pi.add_apply, iSup_apply, ih]

/-- The component `i` of the worst-case cost at a vector charge is the worst-case cost at the
component `i` of the charge. -/
theorem cost_pi_apply (c : P.A → ι → ω) (x : FreeM P α) (i : ι) :
    cost c x i = cost (fun a => c a i) x :=
  costWith_pi_apply c x _ i

/-- A vector bound on the worst-case cost is the family of its component bounds. -/
theorem cost_le_pi_iff {c : P.A → ι → ω} {x : FreeM P α} {u : ι → ω} :
    cost c x ≤ u ↔ ∀ i, cost (fun a => c a i) x ≤ u i := by
  simp only [Pi.le_def, cost_pi_apply]

end Vector

/-! ## Pricing a vector bound -/

section Price

variable [Fintype ι] [CommSemiring ω] [PartialOrder ω] [IsOrderedRing ω]

/-- **Pricing a vector budget.** A budget `u` at the vector charge `c` gives, at nonnegative
prices `p`, the budget `∑ i, p i * u i` at the priced charge `fun a => ∑ i, p i * c a i`. -/
theorem IsChargeBound.price {x : FreeM P α} {c : P.A → ι → ω} {u s : ι → ω} (p : ι → ω)
    (hp : 0 ≤ p) (h : IsChargeBound x c u s) :
    IsChargeBound x (fun a => ∑ i, p i * c a i) (∑ i, p i * u i) (∑ i, p i * s i) :=
  h.map (priceHom p hp)

end Price

section PriceValue

variable [Fintype ι] [CommSemiring ω] [CompleteLattice ω] [IsOrderedRing ω]

/-- **Pricing a vector cost.** The worst-case cost at the priced charge is at most the priced
worst-case vector cost. -/
theorem cost_price_le (c : P.A → ι → ω) (p : ι → ω) (hp : 0 ≤ p) (x : FreeM P α) :
    cost (fun a => ∑ i, p i * c a i) x ≤ ∑ i, p i * cost c x i :=
  cost_comp_le (priceHom p hp) c x

/-- A vector bound `u` on the worst-case cost gives the bound `∑ i, p i * u i` at the priced
charge. -/
theorem cost_price_le_of_le {c : P.A → ι → ω} (p : ι → ω) (hp : 0 ≤ p) {x : FreeM P α}
    {u : ι → ω} (h : cost c x ≤ u) :
    cost (fun a => ∑ i, p i * c a i) x ≤ ∑ i, p i * u i :=
  (cost_price_le c p hp x).trans ((priceHom p hp).monotone' h)

end PriceValue

end FreeM

/-! ## Handlers certified by demands -/

namespace Handler

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {ι ι' ι'' : Type*} [Fintype ι] {ω : Type w} [CommSemiring ω] [PartialOrder ω]
  [IsOrderedRing ω] {α : Type uB}

/-- A handler whose implementation of each call at `a` has use vector at most
`∑ i, c a i • d i`, certified with the demand map of `d` as its exchange. -/
def Certified.ofDemand {c : P.A → ι → ω} {e : Q.A → ι' → ω} (h : Handler (FreeM Q) P)
    (d : ι → ι' → ω) (hd : 0 ≤ d) (hh : ∀ a, (h a).IsChargeBound e (∑ i, c a i • d i)) :
    Certified P Q c e :=
  ⟨h, demandHom d hd, hh⟩

/-- **Use bounds through a handler.** If `x` has use vector `u` and each call at `a` is
implemented with use vector `∑ i, c a i • d i`, then `x.liftM h` has use vector
`∑ i, u i • d i`. -/
theorem isChargeBound_liftM_demand {c : P.A → ι → ω} {e : Q.A → ι' → ω}
    {h : Handler (FreeM Q) P} {d : ι → ι' → ω} (hd : 0 ≤ d)
    (hh : ∀ a, (h a).IsChargeBound e (∑ i, c a i • d i)) {x : FreeM P α} {u : ι → ω}
    (hx : x.IsChargeBound c u) :
    (x.liftM h).IsChargeBound e (∑ i, u i • d i) := by
  have := (Certified.ofDemand h d hd hh).transfer hx
  rwa [map_zero] at this

/-- **Use bounds through two handlers.** Running `x` through `h₁` with demands `d₁` and then
through `h₂` with demands `d₂` has the use vector of `u` at the composite demands
`fun i => ∑ j, d₁ i j • d₂ j`. -/
theorem isChargeBound_liftM_demand_comp [Fintype ι'] {Q : PFunctor.{uA₂, uB}} {c : P.A → ι → ω}
    {e : Q.A → ι' → ω}
    {f : R.A → ι'' → ω} {h₁ : Handler (FreeM Q) P} {h₂ : Handler (FreeM R) Q}
    {d₁ : ι → ι' → ω} {d₂ : ι' → ι'' → ω} (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hh₁ : ∀ a, (h₁ a).IsChargeBound e (∑ i, c a i • d₁ i))
    (hh₂ : ∀ b, (h₂ b).IsChargeBound f (∑ j, e b j • d₂ j)) {x : FreeM P α} {u : ι → ω}
    (hx : x.IsChargeBound c u) :
    (x.liftM (h₂.comp h₁)).IsChargeBound f (∑ i, u i • ∑ j, d₁ i j • d₂ j) := by
  let g := (Certified.ofDemand h₂ d₂ hd₂ hh₂).comp (Certified.ofDemand h₁ d₁ hd₁ hh₁)
  have h := g.transfer hx
  rw [map_zero] at h
  have hu : g.exchange u = ∑ i, u i • ∑ j, d₁ i j • d₂ j :=
    demandHom_demandHom d₁ hd₁ d₂ hd₂ u
  rw [hu] at h
  exact h

end Handler

end PFunctor
