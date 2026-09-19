/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin, Quang Dao
-/

module

public import ToCslib.Data.BitVec

/-!
# Direct canaries for single-bit overwrites

This example pins the overwrite selection of `BitVec.overwriteBit`.
-/

example {n index : ℕ} (hindex : index < n) (bit : Bool) (value : BitVec n) :
    (value.overwriteBit index bit).getLsbD index = bit := by
  exact BitVec.getLsbD_overwriteBit_self hindex bit value
