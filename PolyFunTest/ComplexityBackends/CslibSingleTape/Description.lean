/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Nontriviality

/-!
# Adversarial canaries for the single-tape description measure

What a dishonest prover cannot do, and what the definitions deliberately leave to the pinned
boundary:

* a witness has at least one state, so description sizes never vanish;
* a non-injective codomain encoding makes `EncPolyTime` trivially inhabited (the erasing machine),
  which is why faithfulness is a hypothesis of the separation and never derived;
* an injective, polynomially wide `BitEncFam` may still cache the function in its encoding, which
  is why boundaries are assembled from canonical constructors and never chosen existentially;
* against the pinned coin boundary, some family has no witness at all.
-/

public section

open PFunctor ComplexityBackends.CslibSingleTape ComplexityBackends.CslibSingleTape.PPoly
open Cslib.Turing.SingleTapeTM

namespace PolyFunTest.ComplexityBackends.CslibSingleTape.Description

variable {A B : Type} {a : A → List Bool} {b : B → List Bool} {f : A → B}

/-- Every witness has at least one state. -/
theorem one_le_size (r : EncPolyTime a b f) : 1 ≤ r.size := by
  rw [EncPolyTime.size_eq_card]
  exact Fintype.card_pos_iff.mpr ⟨r.polyTime.tm.q₀⟩

/-- The erasing machine witnesses every function against the empty codomain encoding. -/
noncomputable def erasingWitness (a : A → List Bool) (f : A → B) :
    EncPolyTime a (fun _ ↦ []) f where
  toFun _ := []
  polyTime := constPolyTimeComputable []
  map_encode _ := rfl

/-- The erasing witness is tiny: raw `EncPolyTime` is not a certificate without a faithful
codomain encoding. -/
example : (erasingWitness a f).size ≤ 2 := by
  rw [EncPolyTime.size_eq_card, ← PolyTimeComputable.size_eq_card]
  exact size_constPolyTimeComputable_le []

/-- An injective, fixed-width, polynomially wide family that caches `f` in its last bit. It is a
legal `BitEncFam`; only pinning boundaries to canonical constructors rules it out. -/
noncomputable def cachingFam (f : (n : ℕ) → BitVec n → Bool) : BitEncFam (fun n ↦ BitVec n) where
  wid n := BitEncFam.bitVecX.wid n + 1
  widBound := BitEncFam.bitVecX.widBound + 1
  wid_le n := by
    have := BitEncFam.bitVecX.wid_le n
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    omega
  enc n x := BitEncFam.bitVecX.enc n x ++ [f n x]
  len_eq n x := by simp [BitEncFam.bitVecX.len_eq]
  enc_injective n x y h :=
    BitEncFam.bitVecX.enc_injective n (List.append_inj_left' h rfl)

/-- Against the pinned coin boundary some family has no witness at all. -/
theorem exists_isEmpty_witness :
    ∃ f : (n : ℕ) → BitVec n → Bool,
      IsEmpty (Witness coinBoundary (fun n v ↦ FreeM.pure (f n v))) := by
  obtain ⟨f, h⟩ := exists_not_isPPolyBy_pure
  exact ⟨f, ⟨fun witness ↦ h (IsPPolyBy.intro witness)⟩⟩

/-- The polynomial may depend on the predicate family, and it only has to bound the description
size cofinitely; even this nonuniform, eventual claim fails. -/
example : ¬ ∀ f : (n : ℕ) → BitVec n → Bool, ∃ q : Polynomial ℕ,
    ∀ᶠ n in Filter.atTop, (some ∘ f n) ∈
      Backend.description.RealizableLE (BitEncFam.bitVecX.enc n)
        (BitEncFam.bool.option.enc n) (q.eval n) := by
  obtain ⟨f, notRealizable⟩ := Backend.exists_not_realizableLE_poly
  exact fun allFamilies ↦ notRealizable (allFamilies f)

end PolyFunTest.ComplexityBackends.CslibSingleTape.Description
