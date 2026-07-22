/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded

/-! # Bounded returning-computation examples -/

@[expose] public section

open PFunctor

namespace PFunctor.DynSystem.DynComputation

/-! ## Boundary behavior and universes -/

def emptyReturn : DynComputation (0 : PFunctor.{0, 0}) Nat Nat :=
  ofFn (· + 1)

example : emptyReturn.run 0 4 = FreeM.pure (some 5) := by
  simp [emptyReturn]

universe uA uB uα uβ uγ uState uState₂

def boundedUniverseCanary {p : PFunctor.{uA, uB}} {α : Type uα}
    {β : Type uβ} (M : DynComputation.{uState} p α β)
    (k : ℕ) (state : M.State) : FreeM p (Option β) :=
  M.unroll k state

def closedTrajectoryUniverseCanary {α : Type uα} {β : Type uβ}
    (M : DynComputation.{uState} X.{uA, uB} α β)
    (state : M.State) (k : ℕ) : M.State :=
  M.closedStutterIterate state k

theorem boundedSeqUniverseCanary {p : PFunctor.{uA, uB}} {α : Type uα}
    {β : Type uβ} {γ : Type uγ} (M₁ : DynComputation.{uState} p α β)
    (M₂ : DynComputation.{uState₂} p β γ) (program₁ : α → FreeM p β)
    (program₂ : β → FreeM p γ) (k₁ k₂ : ℕ)
    (h₁ : M₁.ImplementsWithin program₁ k₁)
    (h₂ : M₂.ImplementsWithin program₂ k₂) :
    (M₁.seqComp M₂).ImplementsWithin
      (fun input => FreeM.bind (program₁ input) program₂) (k₁ + k₂) :=
  h₁.seqComp h₂

abbrev branchP : PFunctor := monomial Bool Bool

def branchProgram (_ : Unit) : FreeM branchP Nat :=
  FreeM.liftBind false fun answer : Bool =>
    pure (if answer = true then 11 else 10)

def branchMachine : DynComputation branchP Unit Nat :=
  ofFreeM branchProgram

theorem branchProgram_bound : (branchProgram ()).IsTotalRollBound 1 := by
  unfold branchP
  rw [show branchProgram () = FreeM.liftBind false (fun answer : Bool =>
    pure (if answer = true then 11 else 10)) from rfl,
    FreeM.liftBind_eq,
    FreeM.isTotalRollBound_lift_bind_iff]
  exact ⟨by omega, fun _ => by simp⟩

example : branchMachine.run 0 () = FreeM.pure none := rfl

example : branchMachine.run 1 () = FreeM.map some (branchProgram ()) := rfl

example : branchMachine.ResolvesIn 1 (branchMachine.init ()) := by
  rw [resolvesIn_iff_isTotalRollBound_of_behavior_eq branchMachine 1 _
    (branchProgram ())]
  · exact branchProgram_bound
  · exact denote_ofFreeM branchProgram ()

example : ¬branchMachine.ResolvesIn 0 (branchMachine.init ()) := by
  apply branchMachine.not_resolvesIn_query_zero _ false _
  rfl

example : branchMachine.unroll 1 (branchMachine.init ()) =
    Resumption.truncate 1
      (branchMachine.toDynSystem.behavior (branchMachine.init ())) :=
  branchMachine.unroll_eq_truncate 1 _

example : branchMachine.ImplementsWithin branchProgram 1 := by
  rw [implementsWithin_iff_implements_and_bound]
  refine ⟨implements_ofFreeM branchProgram, fun input => ?_⟩
  cases input
  exact branchProgram_bound

example : branchMachine.ImplementsWithin branchProgram 4 :=
  (show branchMachine.ImplementsWithin branchProgram 1 by
    rw [implementsWithin_iff_implements_and_bound]
    refine ⟨implements_ofFreeM branchProgram, fun input => ?_⟩
    cases input
    exact branchProgram_bound).mono (by omega)

example : ¬branchMachine.ImplementsWithin branchProgram 0 := by
  intro h
  have := h ()
  cases this

def wrongBranchProgram (_ : Unit) : FreeM branchP Nat := pure 99

example : ¬branchMachine.ImplementsWithin wrongBranchProgram 1 := by
  intro h
  have := h ()
  cases this

/-! An empty direction type makes a query branch vacuously resolve after one
layer, while zero fuel still cuts it off. -/

def emptyDirectionP : PFunctor := monomial Unit Empty

def emptyDirectionTree : Resumption emptyDirectionP Nat :=
  Resumption.query () fun direction => Empty.elim direction

def emptyDirectionMachine : DynComputation emptyDirectionP Unit Nat :=
  ofResumption fun _ => emptyDirectionTree

example : ¬emptyDirectionMachine.ResolvesIn 0 (emptyDirectionMachine.init ()) := by
  apply emptyDirectionMachine.not_resolvesIn_query_zero _ () _
  rfl

example : emptyDirectionMachine.ResolvesIn 1 (emptyDirectionMachine.init ()) := by
  rw [emptyDirectionMachine.resolvesIn_query_succ_iff 0 _ () _ rfl]
  exact fun direction => Empty.elim direction

/-! ## Closed deterministic trajectories -/

/-- One Collatz step. The small trajectory below is used only as an executable
closed-system canary; no global Collatz termination claim is made. -/
def collatzNext (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The return-or-query view of the Collatz producer. -/
def collatzView (n : ℕ) : ℕ ⊕ X.{0, 0}.Obj ℕ :=
  if n = 1 then Sum.inl n
  else Sum.inr ⟨PUnit.unit, fun _ => collatzNext n⟩

/-- The polynomial coalgebra step corresponding to `collatzView`. -/
def collatzOut (n : ℕ) : (C.{0, 0} ℕ + X.{0, 0}).Obj ℕ :=
  Resumption.pack (collatzView n)

/-- A closed deterministic Collatz producer that returns at `1` and otherwise
makes the unique `X` query before advancing. -/
def collatzMachine : DynComputation X.{0, 0} ℕ ℕ where
  State := ℕ
  toDynSystem := (fun n => (collatzOut n).1) ⇆ fun n => (collatzOut n).2
  init := id

@[simp] theorem init_collatzMachine (n : ℕ) : collatzMachine.init n = n := rfl

@[simp] theorem view_collatzMachine (n : ℕ) :
    collatzMachine.view n = collatzView n := by
  change Resumption.unpack (collatzOut n) = collatzView n
  exact Resumption.unpack_pack (collatzView n)

@[simp] theorem closedStutterStep_collatzMachine (n : ℕ) :
    collatzMachine.closedStutterStep n =
      if n = 1 then n else collatzNext n := by
  by_cases h : n = 1 <;> simp [closedStutterStep, collatzView, h]

example : collatzMachine.view (collatzMachine.init 1) = Sum.inl 1 := by
  simp [collatzView]
  rfl

example : collatzMachine.closedStutterStep (collatzMachine.init 1) =
    collatzMachine.init 1 := by
  simp

example : collatzMachine.closedStutterIterate (collatzMachine.init 6) 8 =
    collatzMachine.init 1 := by
  norm_num [closedStutterIterate, collatzNext]

theorem collatz_resolvesIn_eight :
    collatzMachine.ResolvesIn 8 (collatzMachine.init 6) := by
  norm_num [ResolvesIn, collatzView, collatzNext]

example : collatzMachine.ResolvesIn 8 (collatzMachine.init 6) := by
  rw [collatzMachine.resolvesIn_iff_exists_le_closedStutterIterate_return]
  refine ⟨8, le_rfl, 1, ?_⟩
  norm_num [closedStutterIterate, collatzView, collatzNext]
  rfl

example : ∃ j ≤ 8, ∃ value,
    collatzMachine.view
      (collatzMachine.closedStutterIterate (collatzMachine.init 6) j) =
        Sum.inl value :=
  (collatzMachine.resolvesIn_iff_exists_le_closedStutterIterate_return 8 _).mp
    collatz_resolvesIn_eight

example : ¬collatzMachine.ResolvesIn 7 (collatzMachine.init 6) := by
  norm_num [ResolvesIn, collatzView, collatzNext]

example : ∃ k, collatzMachine.ResolvesIn k (collatzMachine.init 6) := by
  rw [collatzMachine.exists_resolvesIn_iff_exists_closedStutterIterate_return]
  refine ⟨8, 1, ?_⟩
  norm_num [closedStutterIterate, collatzView, collatzNext]
  rfl

/-! ## Bounded simulation -/

def boolRealization : DynComputation branchP Unit Nat where
  State := Bool
  toDynSystem :=
    (fun
      | false => Sum.inr false
      | true => Sum.inl (10 : Nat)) ⇆
    fun
      | false => fun _ => true
      | true => PEmpty.elim
  init := fun _ => false

def constantBranchProgram (_ : Unit) : FreeM branchP Nat :=
  FreeM.liftBind false fun _ => pure 10

theorem constantBranchProgram_bound :
    (constantBranchProgram ()).IsTotalRollBound 1 := by
  unfold branchP
  rw [show constantBranchProgram () =
      FreeM.liftBind false (fun _ : Bool => pure 10) from rfl,
    FreeM.liftBind_eq,
    FreeM.isTotalRollBound_lift_bind_iff]
  exact ⟨by omega, fun _ => by simp⟩

inductive BoolResidual : Bool → FreeM branchP Nat → Prop
  | start : BoolResidual false (constantBranchProgram ())
  | done : BoolResidual true (FreeM.pure 10)

theorem boolSimulation : IsSimulation boolRealization.toDynSystem
    (ofFreeM constantBranchProgram).toDynSystem BoolResidual where
  expose_eq := by
    intro state residual related
    cases related <;> rfl
  update_rel := by
    intro state residual related direction
    cases related with
    | start => exact BoolResidual.done
    | done => exact PEmpty.elim direction

example : boolRealization.ImplementsWithin constantBranchProgram 1 := by
  apply implementsWithin_of_isSimulation boolRealization constantBranchProgram
    BoolResidual boolSimulation
  · intro input
    cases input
    exact BoolResidual.start
  · intro input
    cases input
    exact constantBranchProgram_bound

/-! ## Additive sequencing -/

def firstProgram (_ : Unit) : FreeM branchP Bool :=
  FreeM.liftBind false fun answer : Bool => pure answer

def secondProgram (first : Bool) : FreeM branchP Nat :=
  FreeM.liftBind first fun answer : Bool =>
    pure (if first = true then if answer = true then 11 else 12
      else if answer = true then 20 else 21)

def firstMachine : DynComputation branchP Unit Bool := ofFreeM firstProgram

def secondMachine : DynComputation branchP Bool Nat := ofFreeM secondProgram

theorem firstProgram_bound : (firstProgram ()).IsTotalRollBound 1 := by
  unfold branchP
  rw [show firstProgram () =
      FreeM.liftBind false (fun answer : Bool => pure answer) from rfl,
    FreeM.liftBind_eq,
    FreeM.isTotalRollBound_lift_bind_iff]
  exact ⟨by omega, fun _ => by simp⟩

theorem secondProgram_bound (first : Bool) :
    (secondProgram first).IsTotalRollBound 1 := by
  unfold branchP
  rw [show secondProgram first = FreeM.liftBind first (fun answer : Bool =>
      pure (if first = true then if answer = true then 11 else 12
        else if answer = true then 20 else 21)) from rfl,
    FreeM.liftBind_eq,
    FreeM.isTotalRollBound_lift_bind_iff]
  exact ⟨by omega, fun _ => by simp⟩

theorem firstWithin : firstMachine.ImplementsWithin firstProgram 1 := by
  rw [implementsWithin_iff_implements_and_bound]
  refine ⟨implements_ofFreeM firstProgram, fun input => ?_⟩
  cases input
  exact firstProgram_bound

theorem secondWithin : secondMachine.ImplementsWithin secondProgram 1 := by
  rw [implementsWithin_iff_implements_and_bound]
  exact ⟨implements_ofFreeM secondProgram, secondProgram_bound⟩

example : (firstMachine.seqComp secondMachine).ImplementsWithin
    (fun input => FreeM.bind (firstProgram input) secondProgram) 2 :=
  firstWithin.seqComp secondWithin

example : (firstMachine.seqComp secondMachine).ResolvesIn 2
    ((firstMachine.seqComp secondMachine).init ()) :=
  (firstWithin.resolvesIn ()).seqComp_init secondWithin.resolvesIn

example : ¬(firstMachine.seqComp secondMachine).ResolvesIn 1
    ((firstMachine.seqComp secondMachine).init ()) := by
  rw [resolvesIn_iff_isTotalRollBound_of_behavior_eq
    (firstMachine.seqComp secondMachine) 1 _
      (FreeM.bind (firstProgram ()) secondProgram)]
  · unfold branchP
    rw [show FreeM.bind (firstProgram ()) secondProgram =
        FreeM.liftBind false (fun first : Bool => secondProgram first) from rfl,
      FreeM.liftBind_eq,
      FreeM.isTotalRollBound_lift_bind_iff]
    intro h
    have hfalse := h.2 false
    rw [show secondProgram false = FreeM.liftBind false (fun answer : Bool =>
        pure (if false = true then if answer = true then 11 else 12
          else if answer = true then 20 else 21)) from rfl,
      FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff] at hfalse
    simp at hfalse
  · change (firstMachine.seqComp secondMachine).denote () =
      FreeM.toResumption (FreeM.bind (firstProgram ()) secondProgram)
    exact (implements_ofFreeM firstProgram).seqComp
      (implements_ofFreeM secondProgram) ()

def positionHandler : Handler Option branchP := fun position => some position

def failingHandler : Handler Option branchP := fun _ => none

example : (firstMachine.seqComp secondMachine).runWithInput positionHandler 2 () =
    some (some 21) := by
  rw [runWithInput_seqComp firstMachine secondMachine positionHandler 1 1 ()
    (firstWithin.resolvesIn ()) secondWithin.resolvesIn]
  rfl

example : (firstMachine.seqComp secondMachine).runWithInput failingHandler 2 () = none := rfl

def immediateBool : DynComputation branchP Unit Bool := ofFn fun _ => true

example : (immediateBool.seqComp secondMachine).runWithInput positionHandler 1 () =
    some (some 11) := by
  have hfirst : immediateBool.ResolvesIn 0 (immediateBool.init ()) := by
    apply immediateBool.resolvesIn_return 0 _ true
    rfl
  rw [show 1 = 0 + 1 by omega,
    runWithInput_seqComp immediateBool secondMachine positionHandler 0 1 ()
      hfirst secondWithin.resolvesIn]
  rfl

def immediateNat : DynComputation branchP Bool Nat := ofFn fun value => if value then 7 else 8

example : (firstMachine.seqComp immediateNat).runWithInput positionHandler 1 () =
    some (some 8) := by
  have hsecond : ∀ value, immediateNat.ResolvesIn 0 (immediateNat.init value) := by
    intro value
    apply immediateNat.resolvesIn_return 0 _ (if value then 7 else 8)
    rfl
  rw [show 1 = 1 + 0 by omega,
    runWithInput_seqComp firstMachine immediateNat positionHandler 1 0 ()
      (firstWithin.resolvesIn ()) hsecond]
  rfl

/-! ## Stateful handler branch order -/

def answerOppositeState : Handler (StateT Bool Option) branchP :=
  fun _ state => some (!state, state)

example : (firstMachine.runWith answerOppositeState 1 (firstMachine.init ())).run false =
    some (some true, false) := rfl

def failingStateHandler : Handler (StateT Bool Option) branchP :=
  fun _ _ => none

example : (immediateBool.runWith failingStateHandler 5 (immediateBool.init ())).run false =
    some (some true, false) := rfl

end PFunctor.DynSystem.DynComputation
