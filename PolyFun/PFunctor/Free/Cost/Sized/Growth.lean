/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import PolyFun.PFunctor.Free.Cost.Sized
public import ToCslib.Data.Nat.PolynomialBound

/-!
# Growth of sized contracts

`PolyCost`, `PolyCostUnder` and `FamilyPolyCost` ask for a natural-number polynomial envelope.
This file relates them to `Cslib.PolynomiallyBounded`, the growth predicate on functions `ℕ → ℕ`:

- A polynomial contract is a sized contract with an envelope of polynomial growth
  (`polyCost_iff`, `polyCostUnder_iff`, `familyPolyCost_iff`).
- A lower bound on some completed path at every size is then polynomially bounded
  (`PolyCost.polynomiallyBounded_of_le_charge`, `PolyCostUnder.polynomiallyBounded_of_le_charge`,
  `FamilyPolyCost.polynomiallyBounded_of_le_charge`), so an exponential lower bound refutes the
  contract. Over `Answered`, the lower bound is on the path of the run
  (`PolyCostUnder.polynomiallyBounded_of_le_charge_answered`).
-/

@[expose] public section

universe u uI uP

namespace PFunctor.FreeM.MeasuredProgram

open Cslib

variable {Input : Type uI} {Result : Type u} {size : Input → ℕ}

/-- A polynomial contract is a sized contract with an envelope of polynomial growth. -/
theorem polyCost_iff {M : MeasuredProgram Input Result ℕ} :
    M.PolyCost size ↔ ∃ envelope, PolynomiallyBounded envelope ∧ M.CostWithin size envelope := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.eval, polynomiallyBounded_eval q, hq⟩
  · rintro ⟨envelope, he, h⟩
    obtain ⟨q, hq⟩ := polynomiallyBounded_iff_exists_polynomial.1 he
    exact ⟨q, h.mono hq⟩

/-- A polynomial contract over allowed answers is a sized contract over allowed answers with an
envelope of polynomial growth. -/
theorem polyCostUnder_iff {M : MeasuredProgram Input Result ℕ}
    {allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop} :
    M.PolyCostUnder allows size ↔
      ∃ envelope, PolynomiallyBounded envelope ∧ M.CostWithinUnder allows size envelope := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.eval, polynomiallyBounded_eval q, hq⟩
  · rintro ⟨envelope, he, h⟩
    obtain ⟨q, hq⟩ := polynomiallyBounded_iff_exists_polynomial.1 he
    exact ⟨q, h.mono hq⟩

/-- **Lower bounds refute polynomial cost.** If the program has a polynomial contract and, at every
size `n`, some input of size at most `n` has a completed path costing at least `lower n`, then
`lower` is polynomially bounded. -/
theorem PolyCost.polynomiallyBounded_of_le_charge {M : MeasuredProgram Input Result ℕ}
    (h : M.PolyCost size) {lower : ℕ → ℕ}
    (hlower : ∀ n, ∃ i, size i ≤ n ∧ ∃ p : Path (M.program (M.view i)),
      lower n ≤ Path.charge M.cost (M.program (M.view i)) p) :
    PolynomiallyBounded lower := by
  obtain ⟨q, hq⟩ := h
  refine (polynomiallyBounded_eval q).mono (Filter.Eventually.of_forall fun n => ?_)
  obtain ⟨i, hi, p, hp⟩ := hlower n
  exact hp.trans ((hq i p).trans (q.eval_mono hi))

/-- **Lower bounds refute polynomial cost over allowed answers.** If the program has a polynomial
contract over allowed answers and, at every size `n`, some input of size at most `n` has a
completed path of the restricted program costing at least `lower n`, then `lower` is polynomially
bounded. -/
theorem PolyCostUnder.polynomiallyBounded_of_le_charge {M : MeasuredProgram Input Result ℕ}
    {allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop} (h : M.PolyCostUnder allows size)
    {lower : ℕ → ℕ}
    (hlower : ∀ n, ∃ i, size i ≤ n ∧
      ∃ p : Path ((M.program (M.view i)).restrict (allows (M.view i))),
        lower n ≤ Path.charge M.cost _ p) :
    PolynomiallyBounded lower := by
  obtain ⟨q, hq⟩ := h
  refine (polynomiallyBounded_eval q).mono (Filter.Eventually.of_forall fun n => ?_)
  obtain ⟨i, hi, p, hp⟩ := hlower n
  exact hp.trans ((hq i p).trans (q.eval_mono hi))

/-- **Lower bounds on the run refute polynomial cost over `Answered`.** If the program has a
polynomial contract over the answers of `answer` and, at every size `n`, the run of some input of
size at most `n` costs at least `lower n`, then `lower` is polynomially bounded. -/
theorem PolyCostUnder.polynomiallyBounded_of_le_charge_answered
    {M : MeasuredProgram Input Result ℕ} (h : M.PolyCostUnder M.Answered size) {lower : ℕ → ℕ}
    (hlower : ∀ n, ∃ i, size i ≤ n ∧ lower n ≤
      Path.charge M.cost _ (Path.ofHandler (M.answer (M.view i)) (M.program (M.view i)))) :
    PolynomiallyBounded lower := by
  obtain ⟨q, hq⟩ := h
  have hrun := costWithinUnder_answered_iff.1 hq
  refine (polynomiallyBounded_eval q).mono (Filter.Eventually.of_forall fun n => ?_)
  obtain ⟨i, hi, hp⟩ := hlower n
  exact hp.trans ((hrun i).trans (q.eval_mono hi))

section Family

variable {ι : Type uP} {Input : ι → Type uI} {Result : ι → Type u}

/-- **Lower bounds refute polynomial cost of a family.** If the family has a polynomial contract
and, at every size `n`, some member has an input of size at most `n` with a completed path costing
at least `lower n`, then `lower` is polynomially bounded. -/
theorem FamilyPolyCost.polynomiallyBounded_of_le_charge
    {M : ∀ π, MeasuredProgram (Input π) (Result π) ℕ} {size : ∀ π, Input π → ℕ}
    (h : FamilyPolyCost M size) {lower : ℕ → ℕ}
    (hlower : ∀ n, ∃ π i, size π i ≤ n ∧ ∃ p : Path ((M π).program ((M π).view i)),
      lower n ≤ Path.charge (M π).cost ((M π).program ((M π).view i)) p) :
    PolynomiallyBounded lower := by
  obtain ⟨q, hq⟩ := h
  refine (polynomiallyBounded_eval q).mono (Filter.Eventually.of_forall fun n => ?_)
  obtain ⟨π, i, hi, p, hp⟩ := hlower n
  exact hp.trans ((hq π i p).trans (q.eval_mono hi))

/-- A family has polynomial cost exactly when its members' sized contracts share one envelope of
polynomial growth. -/
theorem familyPolyCost_iff {M : ∀ π, MeasuredProgram (Input π) (Result π) ℕ}
    {size : ∀ π, Input π → ℕ} :
    FamilyPolyCost M size ↔
      ∃ envelope, PolynomiallyBounded envelope ∧ ∀ π, (M π).CostWithin (size π) envelope := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.eval, polynomiallyBounded_eval q, hq⟩
  · rintro ⟨envelope, he, h⟩
    obtain ⟨q, hq⟩ := polynomiallyBounded_iff_exists_polynomial.1 he
    exact ⟨q, fun π => (h π).mono hq⟩

end Family

end PFunctor.FreeM.MeasuredProgram
