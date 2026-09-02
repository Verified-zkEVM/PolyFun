/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFunCslib.PPoly
public import ToCslib.Computability.SingleTape.Counting

/-!
# Non-triviality of the cslib-backed P/poly model

This module connects the semantic `IsPPolyBy` certificate to `ToCslib`'s
machine-counting theorem at one pinned Boolean boundary. The resulting theorem
says that polynomially bounded non-uniform machine families cannot contain all
families of Boolean predicates on `BitVec n`.
-/

public section

open Filter
open ToCslib.Computability

namespace PFunctor.CslibPPoly

/-! ## The pinned pure-Boolean boundary -/

/-- One Boolean-answer query. The non-triviality theorem concerns pure programs,
but retaining a genuine query interface makes it directly reusable by oracle
libraries. -/
abbrev Coin : PFunctor := PFunctor.mk PUnit fun _ ↦ Bool

/-- The parameter-constant family of Boolean-answer query interfaces. -/
abbrev CoinFam : ℕ → PFunctor := fun _ ↦ Coin

instance instDecidableEqCoinFam : (n : ℕ) → DecidableEq (CoinFam n).A :=
  fun _ ↦ inferInstanceAs (DecidableEq PUnit)

noncomputable instance instFintypeCoinIndex : Fintype Coin.Idx := by
  change Fintype (Σ _ : PUnit, Bool)
  infer_instance

/-- Canonical, fixed representations for bitvector inputs, Boolean results, the
single query position, and its Boolean answer. -/
noncomputable def coinBoundary :
    Boundary CoinFam (fun n ↦ BitVec n) (fun _ ↦ Bool) where
  input := BitEncFam.bitVecX
  output := BitEncFam.bool
  position := BitEncFam.unit
  index := BitEncFam.const Coin.Idx

/-- Extract a returned Boolean, rejecting the sole query position. -/
def decodeCoinHead : Bool ⊕ PUnit → Option Bool
  | .inl value => some value
  | .inr _ => none

/-- Finite-table decoder from the combined return-or-query head to the canonical
optional Boolean encoding used by the counting theorem. -/
noncomputable def decodeCoinHeadCode :
    EncPolyTimeFam coinBoundary.head.enc BitEncFam.bool.option.enc
      (fun _ ↦ decodeCoinHead) :=
  .ofFintype coinBoundary.head.enc_injective (fun _ ↦ decodeCoinHead)
    (.C 3) (fun _ ↦ by simp [Coin, CoinFam])
    coinBoundary.head.bound coinBoundary.head.len_le
    BitEncFam.bool.option.widBound
    (fun n value ↦
      (BitEncFam.bool.option.len_eq n (decodeCoinHead value)).le.trans
        (BitEncFam.bool.option.wid_le n))

/-- A pure Boolean P/poly certificate yields the two cslib machines counted by
`RealizableLE`: initialization, followed by decoded initial-state observation. -/
theorem realizableLE_of_isPPolyBy_pure
    {function : (n : ℕ) → BitVec n → Bool}
    (certificate : IsPPolyBy coinBoundary
      (fun n value ↦ FreeM.pure (function n value))) :
    ∃ q : Polynomial ℕ, ∀ n, function n ∈ RealizableLE n (q.eval n) := by
  obtain ⟨witness⟩ := certificate.toNonempty
  let outputCode := witness.realization.headCode.comp decodeCoinHeadCode
  refine ⟨witness.realization.initCode.size + outputCode.size, fun n ↦ ?_⟩
  apply mem_realizableLE.mpr
  refine ⟨(witness.realization.machine n).State, witness.realization.state.enc n,
    (witness.realization.machine n).init,
    decodeCoinHead ∘ (witness.realization.machine n).head,
    witness.realization.initCode.wit n, outputCode.wit n, ?_, ?_, ?_⟩
  · have initBound := witness.realization.initCode.size_le n
    simp only [Polynomial.eval_add]
    exact initBound.trans (Nat.le_add_right _ _)
  · have outputBound := outputCode.size_le n
    simp only [Polynomial.eval_add]
    exact outputBound.trans (Nat.le_add_left _ _)
  · intro value
    rw [Function.comp_apply, witness.head_init_eq_of_pure]
    rfl

/-! ## Diagonalization -/

private theorem existsDiagonalRealizable :
    ∃ (function : (n : ℕ) → BitVec n → Bool)
      (cover : (n : ℕ) → Finset (BitVec n → Bool)),
      (∀ n, RealizableLE n (2 ^ (n / 4)) ⊆ ↑(cover n)) ∧
        (∀ᶠ n in atTop, function n ∉ cover n) := by
  classical
  let cover : (n : ℕ) → Finset (BitVec n → Bool) :=
    fun n ↦ (exists_realizableLE_covering n (2 ^ (n / 4))).choose
  have covered : ∀ n, RealizableLE n (2 ^ (n / 4)) ⊆ ↑(cover n) := fun n ↦
    (exists_realizableLE_covering n (2 ^ (n / 4))).choose_spec.1
  have cardBound : ∀ n,
      (cover n).card ≤ Cslib.Turing.SingleTapeTM.B (2 ^ (n / 4)) ^ 2 := fun n ↦
    (exists_realizableLE_covering n (2 ^ (n / 4))).choose_spec.2
  have coverSmall : ∀ᶠ n in atTop, (cover n).card < 2 ^ (2 ^ n) :=
    eventually_count_lt.mono fun n bound ↦ lt_of_le_of_lt (cardBound n) bound
  obtain ⟨function, misses⟩ := exists_diagonal cover coverSmall
  exact ⟨function, cover, covered, misses⟩

private theorem notRealizableOfDiagonal
    {function : (n : ℕ) → BitVec n → Bool}
    {cover : (n : ℕ) → Finset (BitVec n → Bool)}
    (covered : ∀ n, RealizableLE n (2 ^ (n / 4)) ⊆ ↑(cover n))
    (misses : ∀ᶠ n in atTop, function n ∉ cover n)
    (q : Polynomial ℕ) (realizable : ∀ n, function n ∈ RealizableLE n (q.eval n)) :
    False := by
  have belongs : ∀ᶠ n in atTop, function n ∈ cover n :=
    (eventually_poly_le q).mono fun n bound ↦
      Finset.mem_coe.mp (covered n (realizableLE_mono bound (realizable n)))
  obtain ⟨n, belongsAtN, missesAtN⟩ := (belongs.and misses).exists
  exact missesAtN belongsAtN

/-- There is a Boolean predicate family whose pure programs have no
cslib-backed non-uniform P/poly certificate at the pinned coin boundary. -/
theorem exists_not_isPPolyBy_pure :
    ∃ function : (n : ℕ) → BitVec n → Bool,
      ¬ IsPPolyBy coinBoundary
        (fun n value ↦ FreeM.pure (function n value)) := by
  obtain ⟨function, cover, covered, misses⟩ := existsDiagonalRealizable
  refine ⟨function, fun certificate ↦ ?_⟩
  obtain ⟨q, realizable⟩ := realizableLE_of_isPPolyBy_pure certificate
  exact notRealizableOfDiagonal covered misses q realizable

end PFunctor.CslibPPoly
