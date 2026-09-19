/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import ComplexityBackends.CslibSingleTape.PPoly
public import ComplexityBackends.CslibSingleTape.Description

/-!
# Non-triviality of the cslib-backed P/poly model

This module connects the semantic `IsPPolyBy` certificate to the counting
separation for this backend's description measure at one pinned Boolean
boundary. A pure certificate yields, at every parameter, a single composed
witness (initialization followed by decoded observation) whose state count is
polynomially bounded; the separation says no such family exists for some
Boolean predicate family on `BitVec n`.
-/

public section

open PFunctor

namespace ComplexityBackends.CslibSingleTape.PPoly

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

/-- A pure Boolean P/poly certificate yields, at every parameter, one cslib machine computing
`some ∘ function n` at the canonical encodings: initialization composed with decoded observation.
Its state count is bounded by the sum of the two code families' description bounds. -/
theorem realizableLE_of_witness {function : (n : ℕ) → BitVec n → Bool}
    (witness : Witness coinBoundary (fun n value ↦ FreeM.pure (function n value))) (n : ℕ) :
    (some ∘ function n) ∈ Backend.description.RealizableLE (coinBoundary.input.enc n)
      (BitEncFam.bool.option.enc n)
      ((witness.realization.initCode.size +
        (witness.realization.headCode.comp decodeCoinHeadCode).size).eval n) := by
  let outputCode := witness.realization.headCode.comp decodeCoinHeadCode
  let code := (witness.realization.initCode.wit n).comp (outputCode.wit n)
  refine Backend.description.mem_realizableLE.mpr ⟨code.copy _ ?_, ?_⟩
  · intro value
    simp only [Function.comp_apply, witness.head_init_eq_of_pure, decodeCoinHead]
  · rw [Backend.descSize_eq, EncPolyTime.size_copy, EncPolyTime.size_comp, Polynomial.eval_add]
    exact Nat.add_le_add (witness.realization.initCode.size_le n) (outputCode.size_le n)

/-- There is a Boolean predicate family whose pure programs have no
cslib-backed non-uniform P/poly certificate at the pinned coin boundary. -/
theorem exists_not_isPPolyBy_pure :
    ∃ function : (n : ℕ) → BitVec n → Bool,
      ¬ IsPPolyBy coinBoundary
        (fun n value ↦ FreeM.pure (function n value)) := by
  obtain ⟨function, notRealizable⟩ := Backend.exists_not_realizableLE_poly
  refine ⟨function, fun certificate ↦ notRealizable ?_⟩
  obtain ⟨witness⟩ := certificate.toNonempty
  exact ⟨_, fun n ↦ realizableLE_of_witness witness n⟩

end ComplexityBackends.CslibSingleTape.PPoly
