/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Realizability.Backend.Cslib.PPoly

/-!
# Direct canaries for the cslib-backed P/poly adapter

The producer example below assembles a complete certificate for an immediately
returning Boolean program. The remaining examples exercise the derived resource
bounds and compositional API through the public surface.
-/

open ToCslib.Computability

@[expose] public section

namespace PFunctor.CslibPPolyTest

open CslibPPoly

abbrev ConstBool : ℕ → PFunctor := fun _ ↦ PFunctor.C Bool
abbrev BoolFam : ℕ → Type := fun _ ↦ Bool

instance : (n : ℕ) → DecidableEq (ConstBool n).A :=
  fun _ ↦ inferInstanceAs (DecidableEq Bool)

noncomputable def emptyIndexEncoding : BitEncFam fun _ ↦ (PFunctor.C Bool).Idx where
  wid _ := 0
  widBound := 0
  wid_le _ := by simp
  enc _ index := index.2.elim
  len_eq _ index := index.2.elim
  enc_injective _ index := index.2.elim

noncomputable def boolBoundary : Boundary ConstBool BoolFam BoolFam where
  input := BitEncFam.bool
  output := BitEncFam.bool
  position := BitEncFam.bool
  index := emptyIndexEncoding

noncomputable def boolMachine (_n : ℕ) :
    DynSystem.DynComputation (PFunctor.C Bool) Bool Bool :=
  .ofFn id

noncomputable def boolRealization : CslibPPoly.Realization boolBoundary where
  machine := boolMachine
  rounds := 0
  state := BitEncFam.bool.toStrEncFam
  initCode := .ofFintype BitEncFam.bool.enc_injective (fun _ ↦ id)
    (.C 2) (fun _ ↦ by simp) BitEncFam.bool.widBound
    (fun n value ↦ (BitEncFam.bool.len_eq n value).le.trans (BitEncFam.bool.wid_le n))
    BitEncFam.bool.widBound
    (fun n value ↦ (BitEncFam.bool.len_eq n value).le.trans (BitEncFam.bool.wid_le n))
  headCode := .ofFintype BitEncFam.bool.enc_injective
    (fun _ value ↦ Sum.inl value)
    (.C 2) (fun _ ↦ by simp) BitEncFam.bool.widBound
    (fun n value ↦ (BitEncFam.bool.len_eq n value).le.trans (BitEncFam.bool.wid_le n))
    boolBoundary.head.bound (fun n value ↦ boolBoundary.head.len_le n _)
  updateCode := (EncPolyTimeFam.const
      (BitEncFam.bool.toStrEncFam.pairVar boolBoundary.index).enc
      (fun _ ↦ none)
      BitEncFam.bool.toStrEncFam.option.bound
      (fun n ↦ BitEncFam.bool.toStrEncFam.option.len_le n none)).copy _
    (fun _ step ↦ step.2.2.elim)

noncomputable def boolWitness : Witness boolBoundary (fun _ value ↦ FreeM.pure value) where
  realization := boolRealization
  implements _ value := by
    simp [boolRealization, boolMachine]

example : IsPPolyBy boolBoundary (fun _ value ↦ FreeM.pure value) :=
  ⟨boolWitness⟩

example (n : ℕ) (value : Bool) :
    ((boolRealization.initCode.wit n).time).eval
        (boolBoundary.input.enc n value).length ≤ boolRealization.initTime.eval n :=
  boolRealization.initTime_le n value

example (n : ℕ) (value : Bool) :
    (FreeM.pure value : (ConstBool n).FreeM Bool).IsTotalRollBound
      (boolRealization.rounds.eval n) :=
  boolWitness.isTotalRollBound n value

end PFunctor.CslibPPolyTest
