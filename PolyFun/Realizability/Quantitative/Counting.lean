/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Description
public import ToCslib.Algebra.PolynomialGrowth

/-!
# The counting separation for description measures

A family of finite input types whose predicate spaces grow like `2 ^ |D n|` cannot be realized,
at polynomially bounded description size, by a backend whose canonical descriptions at a
superpolynomial threshold `t n` number fewer than `2 ^ |D n|`. The argument is the classical one:
cover the realizable predicates at size `t n` by finitely many functions, diagonalize against the
cover, and note that every polynomial bound is eventually below `t n`.

Only a `DescriptionMeasure` enters; cost, time, and categorical structure play no role. The
faithfulness of every codomain representation is a hypothesis, so a measure that is only
inhabited under an unsatisfiable predicate cannot feed the separation.
`exists_not_realizableLE_poly` takes an arbitrary threshold; the corollary fixes `2 ^ (n / 4)`, at
which every natural-number polynomial is eventually bounded, leaving the backend only its
description count to prove. The conclusion rules out a realizer family that is polynomially
description-bounded only *eventually*, not merely one bounded at every `n`: a bound that holds
cofinitely is the honest reading, since any finite prefix can be absorbed into the measure.
-/

public section

universe u v w x

open Filter

namespace PFunctor.QuantitativeStepClass.DescriptionMeasure

variable {C : StepClass.{u, v}} {Q : QuantitativeStepClass.{u, v, w} C}
  {Faithful : ∀ {B : Type u}, C.Str B → Prop} (M : Q.DescriptionMeasure Faithful)

/-- A family of finite sets of predicates that eventually falls short of the predicate space
eventually misses some predicate family. -/
theorem exists_diagonal {D : ℕ → Type u} [∀ n, Fintype (D n)]
    (S : (n : ℕ) → Finset (D n → Bool))
    (hS : ∀ᶠ n in atTop, (S n).card < 2 ^ Fintype.card (D n)) :
    ∃ f : (n : ℕ) → D n → Bool, ∀ᶠ n in atTop, f n ∉ S n := by
  classical
  have key : ∀ n, (S n).card < 2 ^ Fintype.card (D n) → ∃ g : D n → Bool, g ∉ S n := by
    intro n hn
    have hlt : (S n).card < (Finset.univ : Finset (D n → Bool)).card := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
      exact hn
    obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨e, he⟩
  refine ⟨fun n => if h : (S n).card < 2 ^ Fintype.card (D n) then (key n h).choose
    else fun _ ↦ false, ?_⟩
  refine hS.mono fun n hn => ?_
  simp only [dite_eq_left hn]
  exact (key n hn).choose_spec

/-- **Counting separation.** Against faithful codomain representations, if every polynomial is
eventually below the threshold `t n` and the canonical-description count at `t n` is eventually
below the predicate count `2 ^ |D n|`, some Boolean predicate family (tagged into the codomain by
the injections `ι n`) is not description-bounded by any polynomial on any cofinite set of
parameters. -/
theorem exists_not_realizableLE_poly {D E : ℕ → Type u} [∀ n, Fintype (D n)]
    (a : ∀ n, C.Str (D n)) (b : ∀ n, C.Str (E n))
    (ι : ∀ n, Bool → E n) (hι : ∀ n, Function.Injective (ι n))
    (hb : ∀ n, Faithful (b n)) (t : ℕ → ℕ)
    (ht_poly : ∀ q : Polynomial ℕ, ∀ᶠ n in atTop, q.eval n ≤ t n)
    (ht_count : ∀ᶠ n in atTop,
      Fintype.card (M.Desc (a n) (b n) (t n)) < 2 ^ Fintype.card (D n)) :
    ∃ f : (n : ℕ) → D n → Bool, ¬ ∃ q : Polynomial ℕ,
      ∀ᶠ n in atTop, (ι n ∘ f n) ∈ M.RealizableLE (a n) (b n) (q.eval n) := by
  classical
  let cover : (n : ℕ) → Finset (D n → E n) :=
    fun n ↦ (M.exists_realizableLE_covering (a n) (hb n) (t n)).choose
  have covered : ∀ n, M.RealizableLE (a n) (b n) (t n) ⊆ ↑(cover n) := fun n ↦
    (M.exists_realizableLE_covering (a n) (hb n) (t n)).choose_spec.1
  have cardBound : ∀ n, (cover n).card ≤ Fintype.card (M.Desc (a n) (b n) (t n)) := fun n ↦
    (M.exists_realizableLE_covering (a n) (hb n) (t n)).choose_spec.2
  let decodeBool : ∀ n, (D n → E n) → (D n → Bool) := fun n g x ↦ decide (g x = ι n true)
  let S : (n : ℕ) → Finset (D n → Bool) := fun n ↦ (cover n).image (decodeBool n)
  have hS : ∀ᶠ n in atTop, (S n).card < 2 ^ Fintype.card (D n) :=
    ht_count.mono fun n bound ↦ lt_of_le_of_lt (Finset.card_image_le.trans (cardBound n)) bound
  obtain ⟨f, misses⟩ := exists_diagonal S hS
  refine ⟨f, fun ⟨q, realizable⟩ ↦ ?_⟩
  have belongs : ∀ᶠ n in atTop, f n ∈ S n :=
    ((ht_poly q).and realizable).mono fun n ⟨bound, hrealizable⟩ ↦ by
      have hmem : (ι n ∘ f n) ∈ cover n :=
        Finset.mem_coe.mp (covered n (M.realizableLE_mono bound hrealizable))
      refine Finset.mem_image.mpr ⟨_, hmem, ?_⟩
      funext x
      simp [decodeBool, (hι n).eq_iff]
  obtain ⟨n, belongsAtN, missesAtN⟩ := (belongs.and misses).exists
  exact missesAtN belongsAtN

/-- The counting separation at the standard threshold `2 ^ (n / 4)`: a backend only has to bound
its canonical-description count there. -/
theorem exists_not_realizableLE_poly_of_card_lt {D E : ℕ → Type u} [∀ n, Fintype (D n)]
    (a : ∀ n, C.Str (D n)) (b : ∀ n, C.Str (E n))
    (ι : ∀ n, Bool → E n) (hι : ∀ n, Function.Injective (ι n))
    (hb : ∀ n, Faithful (b n))
    (ht_count : ∀ᶠ n in atTop,
      Fintype.card (M.Desc (a n) (b n) (2 ^ (n / 4))) < 2 ^ Fintype.card (D n)) :
    ∃ f : (n : ℕ) → D n → Bool, ¬ ∃ q : Polynomial ℕ,
      ∀ᶠ n in atTop, (ι n ∘ f n) ∈ M.RealizableLE (a n) (b n) (q.eval n) :=
  M.exists_not_realizableLE_poly a b ι hι hb (fun n ↦ 2 ^ (n / 4))
    Polynomial.eventually_eval_le_two_pow_div_four ht_count

end PFunctor.QuantitativeStepClass.DescriptionMeasure
