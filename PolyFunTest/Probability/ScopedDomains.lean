/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedDomains
public import PolyFun.Control.Semantics.Measure
public import ToCslib.Probability.UniformOn

/-!
# Output measures of the lazy tutorial's decoded meanings

The `ScopedDomains` tutorial certifies the decoded lazy meaning of `addTwo` against `(· + 2)`
(`addTwoDecoded`), and its lazy meaning of `pred` corresponds to `(· - 1)` on positive inputs.
Under any measure on native inputs, the decoded meaning of `addTwo` has the pushforward along
`(· + 2)` as its values and no failure mass. Under a uniform draw from `{1, 2, 3}`, every input is
positive, so the decoded `pred` has the pushforward along `(· - 1)` as its values and no failure
mass. Under a uniform draw from `{0, 1, 2, 3}`, its failure mass is the mass of `0`, where it
diverges. The output encoding of both, `DomainResult.valueEmbedding`, is measurable by `fun_prop`.
-/

public section

open MeasureTheory ProbabilityTheory Control.Semantics Examples.ScopedDomains
open IPFunctor IPFunctor.ScopedSignature

namespace PolyFunTest.Probability.ScopedDomains

/-- The output encoding of the decoded certificates is measurable, by `fun_prop`. -/
example : Measurable ⇑(DomainResult.valueEmbedding : ℕ ↪ DomainResult Empty ℕ) := by fun_prop

/-- The decoded meaning of `addTwo` returns `n + 2` as a value at every input. -/
example (μ : Measure ℕ) :
    DomainResult.success (μ.map (addTwoDecoded.meaning ∘ natEmbedding)) = μ.map (· + 2) :=
  addTwoDecoded.success_map_meaning Measurable.of_discrete.aemeasurable

example (μ : Measure ℕ) :
    DomainResult.failureMass (μ.map (addTwoDecoded.meaning ∘ natEmbedding)) = 0 :=
  addTwoDecoded.failureMass_map_meaning Measurable.of_discrete.aemeasurable

/-- The decoded meaning of `pred`. -/
noncomputable abbrev predDecoded : Ty.nat.Comp → DomainResult Empty ℕ :=
  decodeNat ∘ fun d => pred.denoteDomain algebra (Env.single d)

/-- The decoded `pred` corresponds to `(· - 1)` on positive inputs. -/
theorem predDecoded_correspondsOn :
    CorrespondsOn natEmbedding DomainResult.valueEmbedding (0 < ·) predDecoded (· - 1) :=
  pred_correspondsOn.comp (decodeNatCertified.correspondsOn fun _ => True) fun _ _ => trivial

/-- Almost every draw from `{1, 2, 3}` is positive. -/
theorem ae_pos_uniformOn : ∀ᵐ n ∂uniformOn ({1, 2, 3} : Set ℕ), 0 < n := by
  rw [ae_iff, uniformOn_eq_zero_iff (Set.toFinite _)]
  ext n
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and, not_lt, nonpos_iff_eq_zero]
  omega

/-- On positive inputs, the decoded `pred` returns `n - 1` as a value. -/
example : DomainResult.success
    ((uniformOn ({1, 2, 3} : Set ℕ)).map (predDecoded ∘ natEmbedding)) =
      (uniformOn ({1, 2, 3} : Set ℕ)).map (· - 1) :=
  predDecoded_correspondsOn.success_map_meaning_ae ae_pos_uniformOn
    Measurable.of_discrete.aemeasurable

/-- On positive inputs, the decoded `pred` never diverges. -/
example : DomainResult.failureMass
    ((uniformOn ({1, 2, 3} : Set ℕ)).map (predDecoded ∘ natEmbedding)) = 0 :=
  predDecoded_correspondsOn.failureMass_map_meaning_ae ae_pos_uniformOn
    Measurable.of_discrete.aemeasurable

/-- At `0` the decoded `pred` diverges, so a uniform draw from `{0, 1, 2, 3}` fails with the mass
of `0`. -/
example : DomainResult.failureMass
    ((uniformOn ({0, 1, 2, 3} : Set ℕ)).map (predDecoded ∘ natEmbedding)) =
      uniformOn ({0, 1, 2, 3} : Set ℕ) {0} := by
  rw [DomainResult.failureMass_map Measurable.of_discrete.aemeasurable]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Function.comp_apply]
  constructor
  · intro h
    by_contra hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have := predDecoded_correspondsOn (m + 1) (Nat.succ_pos m)
    simp only [Function.comp_apply] at this
    rw [this] at h
    exact absurd h (by simp)
  · rintro rfl
    change DomainResult.toOption (decodeNat (pred.denoteDomain algebra (Env.single (number 0)))) =
      none
    rw [pred_zero]
    rfl

end PolyFunTest.Probability.ScopedDomains
