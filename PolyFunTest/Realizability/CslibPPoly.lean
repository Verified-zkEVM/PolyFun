/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFunCslib.PPoly

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

/-! ## A branch-distinguishing one-query machine -/

abbrev BoolInteraction : PFunctor := PFunctor.mk Bool fun _ ↦ Bool
abbrev BoolInteractionFam : ℕ → PFunctor := fun _ ↦ BoolInteraction
abbrev BoolStepState : Type := Bool × Option Bool

instance instDecidableEqBoolInteractionFam :
    (n : ℕ) → DecidableEq (BoolInteractionFam n).A := fun _ ↦ inferInstanceAs (DecidableEq Bool)

noncomputable instance instFintypeBoolInteractionIndex : Fintype BoolInteraction.Idx :=
  inferInstanceAs (Fintype ((_ : Bool) × Bool))

def boolInteractionIndexEquiv : BoolInteraction.Idx ≃ Bool × Bool where
  toFun index := (index.1, index.2)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_boolInteractionIndex : Fintype.card BoolInteraction.Idx = 4 := by
  rw [Fintype.card_congr boolInteractionIndexEquiv]
  decide

noncomputable instance instFintypeBoolStepInput :
    (n : ℕ) → Fintype (BoolStepState × (BoolInteractionFam n).Idx) :=
  fun _ ↦ inferInstance

noncomputable def boolIndexEncoding :
    BitEncFam fun _ ↦ BoolInteraction.Idx where
  wid _ := 2
  widBound := .C 2
  wid_le _ := by simp
  enc _ index := [index.1, index.2]
  len_eq _ _ := rfl
  enc_injective _ left right equality := by
    rcases left with ⟨leftPosition, leftAnswer⟩
    rcases right with ⟨rightPosition, rightAnswer⟩
    injection equality with positionEquality tailEquality
    injection tailEquality with answerEquality
    cases positionEquality
    cases answerEquality
    rfl

noncomputable def boolStepBoundary :
    Boundary BoolInteractionFam BoolFam BoolFam where
  input := BitEncFam.bool
  output := BitEncFam.bool
  position := BitEncFam.bool
  index := boolIndexEncoding

noncomputable def boolStepStateEncoding : StrEncFam fun _ ↦ BoolStepState :=
  (BitEncFam.bool.pair BitEncFam.bool.option).toStrEncFam

@[reducible] def boolStepMachine (_n : ℕ) :
    DynSystem.DynComputation BoolInteraction Bool Bool :=
  .ofStep (S := BoolStepState)
    (fun
      | (position, none) => Sum.inr ⟨position, fun answer ↦ (position, some answer)⟩
      | (_, some answer) => Sum.inl answer)
    (fun position ↦ (position, none))

noncomputable def boolStepRealization : CslibPPoly.Realization boolStepBoundary where
  machine := boolStepMachine
  rounds := .C 1
  state := boolStepStateEncoding
  initCode := .ofFintype BitEncFam.bool.enc_injective
    (fun n ↦ (boolStepMachine n).init) (.C 2) (fun _ ↦ by simp)
    BitEncFam.bool.widBound
    (fun n value ↦ (BitEncFam.bool.len_eq n value).le.trans (BitEncFam.bool.wid_le n))
    boolStepStateEncoding.bound (fun n value ↦ boolStepStateEncoding.len_le n _)
  headCode := .ofFintype boolStepStateEncoding.enc_injective
    (fun n ↦ (boolStepMachine n).head) (.C 6) (fun _ ↦ by norm_num [BoolStepState])
    boolStepStateEncoding.bound boolStepStateEncoding.len_le
    boolStepBoundary.head.bound (fun n value ↦ boolStepBoundary.head.len_le n _)
  updateCode := .ofFintype
    (boolStepStateEncoding.pairVar boolStepBoundary.index).enc_injective
    (fun n ↦ (boolStepMachine n).update?) (.C 24)
    (fun _ ↦ by
      rw [Fintype.card_prod, card_boolInteractionIndex]
      norm_num [BoolStepState])
    (boolStepStateEncoding.pairVar boolStepBoundary.index).bound
    (fun n value ↦ (boolStepStateEncoding.pairVar boolStepBoundary.index).len_le n _)
    boolStepStateEncoding.option.bound
    (fun n value ↦ boolStepStateEncoding.option.len_le n _)

def boolQueryProgram (_n : ℕ) (position : Bool) : FreeM BoolInteraction Bool :=
  FreeM.liftBind position FreeM.pure

noncomputable def boolStepWitness : Witness boolStepBoundary boolQueryProgram where
  realization := boolStepRealization
  implements n position := by
    simp only [boolStepRealization, Polynomial.eval_C]
    cases position <;> rfl

example : IsPPolyBy boolStepBoundary boolQueryProgram := ⟨boolStepWitness⟩

example (position answer : Bool) :
    (boolStepMachine 0).update? ((position, none), ⟨position, answer⟩) =
      some (position, some answer) := by
  change (if _ : position = position then some (position, some answer) else none) = _
  simp

example (position answer : Bool) :
    (boolStepMachine 0).update? ((position, none), ⟨!position, answer⟩) = none := by
  have viewEquation : (boolStepMachine 0).view (position, none) =
      Sum.inr ⟨position, fun selected ↦ (position, some selected)⟩ := by rfl
  exact DynSystem.DynComputation.update?_of_view_query_of_ne
    (boolStepMachine 0) viewEquation (index := ⟨!position, answer⟩) (by
      intro equality
      cases position <;> simp at equality)

example (position : Bool) :
    (boolStepMachine 0).update? ((position, none), ⟨position, false⟩) ≠
      (boolStepMachine 0).update? ((position, none), ⟨position, true⟩) := by
  have viewEquation : (boolStepMachine 0).view (position, none) =
      Sum.inr ⟨position, fun answer ↦ (position, some answer)⟩ := by rfl
  rw [DynSystem.DynComputation.update?_of_view_query
      (boolStepMachine 0) viewEquation false,
    DynSystem.DynComputation.update?_of_view_query
      (boolStepMachine 0) viewEquation true]
  simp

example (n : ℕ) (position answer : Bool) :
    let trace : boolStepRealization.ExecutionTrace n
        ((boolStepRealization.machine n).init position)
        (show (boolStepRealization.machine n).State from (position, some answer)) :=
      .query (position := position)
        (next := fun selected ↦ (position, some selected))
        (by change (boolStepMachine n).view (position, none) = _; rfl)
        answer (.nil _)
    ((boolStepRealization.initCode.wit n).time).eval
          (boolStepBoundary.input.enc n position).length + trace.work ≤
        boolStepRealization.totalTime.eval n := by
  dsimp only
  exact CslibPPoly.Realization.ExecutionTrace.runWork_le_totalTime
    (realization := boolStepRealization) (n := n) position _ (by
      simp [CslibPPoly.Realization.ExecutionTrace.length, boolStepRealization])

/-! The two closure canaries below use nontrivial maps. They ensure that both
the certificate-level theorem and its encoded-machine plumbing elaborate. -/

noncomputable def boolNegCode :
    EncPolyTimeFam BitEncFam.bool.enc BitEncFam.bool.enc (fun _ value ↦ !value) :=
  .ofFintype BitEncFam.bool.enc_injective (fun _ value ↦ !value)
    (.C 2) (fun _ ↦ by simp)
    BitEncFam.bool.widBound
    (fun n value ↦ (BitEncFam.bool.len_eq n value).le.trans (BitEncFam.bool.wid_le n))
    BitEncFam.bool.widBound
    (fun n value ↦ (BitEncFam.bool.len_eq n (!value)).le.trans (BitEncFam.bool.wid_le n))

example : IsPPolyBy boolStepBoundary (fun n value ↦ boolQueryProgram n (!value)) :=
  IsPPolyBy.precomp ⟨boolStepWitness⟩ (fun _ value ↦ !value)
    BitEncFam.bool boolNegCode

noncomputable def boolNegHeadCode :
    EncPolyTimeFam boolStepBoundary.head.enc boolStepBoundary.head.enc
      (fun _ ↦ Sum.map (!·) id) :=
  .ofFintype boolStepBoundary.head.enc_injective (fun _ ↦ Sum.map (!·) id)
    (.C 4) (fun _ ↦ by simp)
    boolStepBoundary.head.bound boolStepBoundary.head.len_le
    boolStepBoundary.head.bound
    (fun n value ↦ boolStepBoundary.head.len_le n (Sum.map (!·) id value))

example : IsPPolyBy boolStepBoundary (fun n value ↦
    FreeM.map (!·) (boolQueryProgram n value)) :=
  IsPPolyBy.mapResult ⟨boolStepWitness⟩ (fun _ value ↦ !value)
    BitEncFam.bool boolNegHeadCode

end PFunctor.CslibPPolyTest
