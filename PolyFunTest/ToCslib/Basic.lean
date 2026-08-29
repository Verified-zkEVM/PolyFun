/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin, Quang Dao
-/

module

public import ToCslib

/-!
# Direct canaries for the ToCslib substrate

These examples pin bit order, finite-table semantic orientation, overwrite
selection, and the cardinality used by the machine-counting argument.
-/

open ToCslib.Computability

example : natToBits 3 5 = [true, false, true] := by decide

example (bit : Bool) :
    let encoding : Bool → List Bool := fun value => [value]
    let witness := EncPolyTime.ofFintype encoding (by
      intro left right equality
      have headEquality := congrArg List.head? equality
      simpa [encoding] using headEquality) encoding (!·)
    witness.toFun (encoding bit) = encoding (!bit) := by
  dsimp only
  exact EncPolyTime.map_encode _ bit

example {n index : ℕ} (hindex : index < n) (bit : Bool) (value : BitVec n) :
    (value.overwriteBit index bit).getLsbD index = bit := by
  exact BitVec.getLsbD_overwriteBit_self hindex bit value

example : Fintype.card (BitVec 2 → Bool) = 16 := by
  simpa using card_bitVec_fun 2

example (state : StrEncFam fun _ ↦ Bool) (parameter : ℕ) (value : Bool) :
    state.option.enc parameter none ≠ state.option.enc parameter (some value) := by
  simp

example (input : List Bool) :
    (EncPolyTime.appendBit id true).toFun input = input ++ [true] := rfl
