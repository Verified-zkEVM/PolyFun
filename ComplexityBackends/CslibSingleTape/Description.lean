/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Backend
public import ComplexityBackends.CslibSingleTape.Counting
public import PolyFun.Realizability.Quantitative.Counting
public import Mathlib.Data.FinEnum

/-!
# The single-tape backend as a description measure

The description size of a witness is its machine's state count, and the canonical descriptions at
size `d` are the `d`-state tables `TMTable d`; the boundary is ignored because the tape alphabet is
fixed. Only four machine facts enter: state relabeling (`exists_tmTable_of_card_le`), determinism of
runs (`Outputs_unique`), the output law of a witness (`PolyTimeComputable.outputs` with
`map_encode`), and the table count (`card_tmTable`, `eventually_count_lt`). Faithfulness of a
codomain representation is injectivity of the encoding.

`exists_not_realizableLE_poly` is the generic counting separation at the pinned canonical
bitvector and optional-Boolean encodings; `Nontriviality` turns it into the failure of a P/poly
certificate.
-/

public section

open PFunctor Cslib.Turing.SingleTapeTM Filter

namespace ComplexityBackends.CslibSingleTape

namespace EncPolyTime

variable {A B : Type} {a : A → List Bool} {b : B → List Bool} {f : A → B}

/-- A witness's machine outputs the encoded result on every encoded input. -/
theorem outputs_encode (r : EncPolyTime a b f) (x : A) :
    r.polyTime.tm.Outputs (a x) (b (f x)) := by
  have h := r.polyTime.outputs (a x)
  rwa [r.map_encode x] at h

/-- The canonical `d`-state table of a witness whose machine has at most `d` states. -/
noncomputable def describeTable (r : EncPolyTime a b f) {d : ℕ} (h : r.size ≤ d) : TMTable d :=
  (exists_tmTable_of_card_le r.polyTime.tm (r.size_eq_card ▸ h)).choose

/-- The canonical table computes exactly what the witness's machine computes. -/
theorem describeTable_outputs (r : EncPolyTime a b f) {d : ℕ} (h : r.size ≤ d)
    (l l' : List Bool) :
    (reify (r.describeTable h)).Outputs l l' ↔ r.polyTime.tm.Outputs l l' :=
  (exists_tmTable_of_card_le r.polyTime.tm (r.size_eq_card ▸ h)).choose_spec l l'

end EncPolyTime

namespace Backend

/-- Faithfulness of a raw string representation is injectivity of the encoding. -/
abbrev Faithful {B : Type} (b : encodingStepClass.Str B) : Prop := Function.Injective b

/-- **The single-tape backend is a description measure**: description size is the state count,
canonical descriptions are `d`-state tables, and equal tables compute equal functions against an
injective codomain encoding. Exposed so that `descSize` reduces to `EncPolyTime.size`. -/
@[expose] noncomputable def description :
    quantitative.{0}.DescriptionMeasure Faithful where
  descSize r := r.size
  Desc _ _ d := TMTable d
  descFintype _ _ _ := inferInstance
  describe := by
    intro A B a b f r d h
    exact r.describeTable h
  describe_determines := by
    intro A B a b hb f f' r r' d h h' heq
    funext x
    apply hb
    have o1 : (reify (r.describeTable h)).Outputs (a x) (b (f x)) :=
      (r.describeTable_outputs h _ _).mpr (r.outputs_encode x)
    have o2 : (reify (r'.describeTable h')).Outputs (a x) (b (f' x)) :=
      (r'.describeTable_outputs h' _ _).mpr (r'.outputs_encode x)
    rw [← heq] at o2
    exact Outputs_unique _ o1 o2

/-- The description size of a witness is its state count. -/
@[simp] theorem descSize_eq {A B : Type} {a : A → List Bool} {b : B → List Bool} {f : A → B}
    (r : EncPolyTime a b f) : description.descSize r = r.size :=
  rfl

/-- The table count at the threshold `2 ^ (n / 4)` is eventually below the predicate count. -/
theorem eventually_card_tmTable_lt :
    ∀ᶠ n in atTop, Fintype.card (TMTable (2 ^ (n / 4))) < 2 ^ Fintype.card (BitVec n) := by
  refine eventually_count_lt.mono fun n h ↦ ?_
  rwa [card_tmTable, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-- **Counting separation for the single-tape backend**, at the canonical bitvector input and
optional-Boolean output encodings: some Boolean predicate family has no realizer family whose
state count is polynomially bounded on any cofinite set of parameters. -/
theorem exists_not_realizableLE_poly :
    ∃ f : (n : ℕ) → BitVec n → Bool, ¬ ∃ q : Polynomial ℕ,
      ∀ᶠ n in atTop, (some ∘ f n) ∈
        description.RealizableLE (BitEncFam.bitVecX.enc n) (BitEncFam.bool.option.enc n)
          (q.eval n) :=
  description.exists_not_realizableLE_poly_of_card_lt (D := fun n ↦ BitVec n)
    (E := fun _ ↦ Option Bool) (fun n ↦ BitEncFam.bitVecX.enc n)
    (fun n ↦ BitEncFam.bool.option.enc n) (fun _ ↦ some) (fun _ ↦ Option.some_injective _)
    (fun n ↦ BitEncFam.bool.option.enc_injective n) eventually_card_tmTable_lt

end Backend

end ComplexityBackends.CslibSingleTape
