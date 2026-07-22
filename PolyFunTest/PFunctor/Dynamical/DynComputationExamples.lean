/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.DynComputation

/-! # Returning dynamical computation examples -/

@[expose] public section

open PFunctor

namespace PFunctor.DynSystem.DynComputation

/-- Immediately returning computations exist even over the empty interface,
which has no point that could supply unreachable interaction data. -/
def emptyOfFn : DynComputation 0 Nat Nat := ofFn (· + 1)

example : emptyOfFn.view (emptyOfFn.init 4) = Sum.inl 5 := by simp [emptyOfFn]

example : emptyOfFn.denote 4 = Resumption.pure 5 := by simp [emptyOfFn]

/-- The `Pure` instance ignores the input and returns its constant value. -/
def emptyPure : DynComputation 0 Nat Nat := pure 5

example : emptyPure.view (emptyPure.init 4) = Sum.inl 5 := by simp [emptyPure]

example : emptyPure.denote 4 = Resumption.pure 5 := by simp [emptyPure]

example : emptyPure = ofFn (fun _ : Nat => 5) := by
  unfold emptyPure
  exact pure_eq_ofFn 5

/-- A computation that perpetually exposes the unique query of `X`. -/
def querying : DynComputation.{0} X.{0, 0} Unit Nat where
  State := Unit
  toDynSystem := (fun _ : Unit => Sum.inr PUnit.unit) ⇆ fun _ _ => ()
  init := id

example : querying.view (querying.init ()) =
    Sum.inr ⟨PUnit.unit, fun _ => querying.init ()⟩ := rfl

example : Resumption.dest (querying.denote ()) =
    Sum.map (fun value : Nat => value) (X.map querying.toDynSystem.behavior)
      (querying.view (querying.init ())) :=
  by simpa only using dest_denote querying ()

/-! ## Canonical resumption realizations -/

/-- A resumption realization preserves both its state-level view and its
state-free denotation. -/
def realizedQuerying : DynComputation X Unit Nat :=
  ofResumption fun _ => querying.denote ()

example : realizedQuerying.view (realizedQuerying.init ()) =
    Resumption.dest (querying.denote ()) := by
  simp [realizedQuerying]

example : realizedQuerying.denote () = querying.denote () := by
  simp [realizedQuerying]

universe uA uB uα uβ uState

/-- Inputs, outputs, and both polynomial universes remain independent in the
canonical realization. -/
def universeSeparatedOfResumption {p : PFunctor.{uA, uB}} {α : Type uα}
    {β : Type uβ} (semantics : α → Resumption p β) : DynComputation p α β :=
  ofResumption semantics

/-- Qualitative implementation does not couple the hidden-state universe to
the interface, input, or output universes. -/
example {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    (M : DynComputation.{uState} p α β) (program : α → FreeM p β) : Prop :=
  M.Implements program

/-! ## Finite programs and qualitative implementation -/

/-- A one-query finite program used to exercise the residual-program
realization. -/
def oneQuery (_ : Unit) : FreeM X Nat :=
  FreeM.liftBind PUnit.unit fun _ => pure 7

example : (ofFreeM oneQuery).denote () = FreeM.toResumption (oneQuery ()) := by
  exact denote_ofFreeM oneQuery ()

example :
    (ofResumption fun input => FreeM.toResumption (oneQuery input)).denote () =
      FreeM.toResumption (oneQuery ()) := by
  exact denote_ofResumption _ ()

open scoped PFunctor.DynComputation

example : ofFreeM oneQuery ⊨ oneQuery := by
  exact implements_ofFreeM oneQuery

/-- A noncanonical realization uses `Bool` states instead of residual programs. -/
def boolRealization : DynComputation X Unit Nat where
  State := Bool
  toDynSystem :=
    (fun
      | false => Sum.inr PUnit.unit
      | true => Sum.inl (7 : Nat)) ⇆
    fun
      | false => fun _ => true
      | true => PEmpty.elim
  init := fun _ => false

/-- Relate the implementation states to the corresponding residual programs. -/
inductive BoolResidual : Bool → FreeM X Nat → Prop
  | start : BoolResidual false (oneQuery ())
  | done : BoolResidual true (FreeM.pure 7)

theorem boolSimulation : IsSimulation boolRealization.toDynSystem
    (ofFreeM oneQuery).toDynSystem BoolResidual where
  expose_eq := by
    intro state residual related
    cases related <;> rfl
  update_rel := by
    intro state residual related direction
    cases related with
    | start => exact BoolResidual.done
    | done => exact PEmpty.elim direction

/-- The simulation bridge proves semantics for a genuinely different state
representation, rather than only for the two canonical realizations. -/
theorem boolImplements : boolRealization ⊨ oneQuery := by
  apply implements_of_isSimulation boolRealization oneQuery BoolResidual boolSimulation
  intro input
  cases input
  exact BoolResidual.start

example : ObsEq boolRealization (ofFreeM oneQuery) :=
  ObsEq.of_implements boolImplements (implements_ofFreeM oneQuery)

example : ObsEq (boolRealization.mapResult (· + 1))
    ((ofFreeM oneQuery).mapResult (· + 1)) :=
  (ObsEq.of_implements boolImplements (implements_ofFreeM oneQuery)).mapResult (· + 1)

/-! ## Variance and observational equivalence -/

universe uA₂ uB₂ uγ uδ

/-- Every relevant universe remains independent, including the source and
target direction universes of interface transport. -/
def varianceUniverseCanary {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}
    {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    (M : DynComputation.{uState} p α β) (inputMap : γ → α)
    (resultMap : β → δ) (lens : Lens p q) : DynComputation.{uState} q γ δ :=
  (M.dimap inputMap resultMap).wrap lens

example : (emptyOfFn.contramapInput (fun n : Nat => n + 1)).denote 3 =
    Resumption.pure 5 := by simp [emptyOfFn]

example : emptyOfFn.contramapInput id = emptyOfFn := by simp

example (f g : Nat → Nat) :
    (emptyOfFn.contramapInput f).contramapInput g =
      emptyOfFn.contramapInput (f ∘ g) :=
  contramapInput_comp emptyOfFn f g

example : (emptyOfFn.mapResult (· % 2)).view (emptyOfFn.init 4) = Sum.inl 1 := by
  simp [emptyOfFn]

example : (querying.mapResult (· + 1)).view (querying.init ()) =
    Sum.inr ⟨PUnit.unit, fun _ => querying.init ()⟩ := by
  rw [mapResult_view]
  rfl

example : emptyOfFn.mapResult id = emptyOfFn :=
  mapResult_id emptyOfFn

example (f g : Nat → Nat) :
    (emptyOfFn.mapResult f).mapResult g = emptyOfFn.mapResult (g ∘ f) :=
  mapResult_comp emptyOfFn f g

example : (emptyOfFn.dimap (· + 1) (· * 2)).denote 3 = Resumption.pure 10 := by
  simp [emptyOfFn]

example : emptyOfFn.dimap id id = emptyOfFn := by simp

example (f₁ g₁ f₂ g₂ : Nat → Nat) :
    (emptyOfFn.dimap f₁ g₁).dimap f₂ g₂ =
      emptyOfFn.dimap (f₁ ∘ f₂) (g₂ ∘ g₁) :=
  dimap_comp emptyOfFn f₁ g₁ f₂ g₂

/-- A branch-sensitive interface with a genuinely nonidentity answer map. -/
def branchSource : PFunctor.{0, 0} := monomial Bool Bool

def branchTarget : PFunctor.{0, 0} := monomial (Fin 2) (Fin 3)

def branchFinal : PFunctor.{0, 0} := monomial Bool Bool

def branchLens : Lens branchSource branchTarget where
  toFunA output := by
    change Bool at output
    change Fin 2
    exact if output then 1 else 0
  toFunB _ answer := by
    change Fin 3 at answer
    change Bool
    exact decide (answer = 2)

def branchLens₂ : Lens branchTarget branchFinal where
  toFunA output := by
    change Fin 2 at output
    change Bool
    exact decide (output = 1)
  toFunB _ answer := by
    change Bool at answer
    change Fin 3
    exact if answer then 2 else 1

def branchMachine : DynComputation branchSource Unit Nat where
  State := Bool
  toDynSystem :=
    (fun
      | false => Sum.inr false
      | true => Sum.inl (9 : Nat)) ⇆
    fun
      | false => fun answer => answer
      | true => PEmpty.elim
  init := fun _ => false

example : (branchMachine.wrap branchLens).view false =
    Sum.inr ⟨(0 : Fin 2), fun answer => by
      change Fin 3 at answer
      exact decide (answer = 2)⟩ := by
  rw [wrap_view]
  rfl

example : (branchMachine.wrap branchLens).view true = Sum.inl 9 := by
  rw [wrap_view]
  rfl

example : branchMachine.wrap (Lens.id branchSource) = branchMachine :=
  wrap_id branchMachine

example : (branchMachine.wrap branchLens).wrap branchLens₂ =
    branchMachine.wrap (Lens.comp branchLens₂ branchLens) :=
  wrap_comp branchMachine branchLens branchLens₂

example : (Lens.comp branchLens₂ branchLens).toFunA false = false := by
  change decide ((0 : Fin 2) = 1) = false
  decide

example (answer : Bool) :
    (Lens.comp branchLens₂ branchLens).toFunB false answer = answer := by
  change decide ((if answer then 2 else 1 : Fin 3) = 2) = answer
  cases answer <;> decide

example : (branchMachine.mapResult (· + 1)).wrap branchLens =
    (branchMachine.wrap branchLens).mapResult (· + 1) :=
  mapResult_wrap branchMachine (· + 1) branchLens

/-! Lossy maps preserve equivalence but do not reflect it. These countermodels
pin the intended one-way API. -/

def boolResult (value : Bool) : DynComputation 0 Unit Bool :=
  ofFn fun _ => value

example : ¬ ObsEq (boolResult false) (boolResult true) := by
  intro h
  have hdenote := h ()
  have hdest := congrArg Resumption.dest hdenote
  simp [boolResult] at hdest

example : ObsEq
    ((boolResult false).mapResult (fun _ => ()))
    ((boolResult true).mapResult (fun _ => ())) := by
  intro input
  simp [boolResult]

/-- The outer interface can observe only the `false` source answer. -/
def lossySource : PFunctor.{0, 0} := monomial Unit Bool

def lossyLens : Lens lossySource X where
  toFunA _ := PUnit.unit
  toFunB _ _ := false

def sourceTree (trueResult : Nat) : Resumption lossySource Nat :=
  Resumption.query () fun answer => by
    change Bool at answer
    exact Resumption.pure (if answer then trueResult else 0)

def sourceMachine (trueResult : Nat) : DynComputation lossySource Unit Nat :=
  ofResumption fun _ => sourceTree trueResult

def observeTrueResult (tree : Resumption lossySource Nat) : Option Nat :=
  match Resumption.dest tree with
  | Sum.inl _ => none
  | Sum.inr ⟨_, next⟩ =>
      match Resumption.dest (next true) with
      | Sum.inl value => some value
      | Sum.inr _ => none

example : ¬ ObsEq (sourceMachine 1) (sourceMachine 2) := by
  intro h
  have hdenote := h ()
  have hobserved := congrArg observeTrueResult hdenote
  norm_num [sourceMachine, sourceTree, observeTrueResult, lossySource] at hobserved

example : ObsEq
    ((sourceMachine 1).wrap lossyLens)
    ((sourceMachine 2).wrap lossyLens) := by
  intro input
  cases input
  simp [sourceMachine, sourceTree, lossyLens, lossySource]

example : (ofFreeM oneQuery).mapResult (· + 1) ⊨
    (fun input => FreeM.map (· + 1) (oneQuery input)) := by
  exact (implements_ofFreeM oneQuery).mapResult (· + 1)

example : (ofFreeM oneQuery).wrap (Lens.id X) ⊨
    (fun input => (oneQuery input).mapLens (Lens.id X)) := by
  exact (implements_ofFreeM oneQuery).wrap (Lens.id X)

/-! ## Semantic transport producer canaries -/

/-- An input-dependent program makes input precomposition observable. -/
def inputProgram (input : Nat) : FreeM X Nat :=
  FreeM.liftBind PUnit.unit fun _ => pure (input + 1)

def inputFreeMachine : DynComputation X Nat Nat := ofFreeM inputProgram

def inputResumptionMachine : DynComputation X Nat Nat :=
  ofResumption fun input => FreeM.toResumption (inputProgram input)

theorem inputMachinesObsEq : ObsEq inputFreeMachine inputResumptionMachine :=
  ObsEq.of_implements (implements_ofFreeM inputProgram)
    (implements_ofResumption inputProgram)

def boolInput : Bool → Nat := Bool.rec 3 7

example : ObsEq
    (inputFreeMachine.contramapInput boolInput)
    (inputResumptionMachine.contramapInput boolInput) :=
  inputMachinesObsEq.contramapInput boolInput

example : ObsEq
    (inputFreeMachine.dimap boolInput (· * 2))
    (inputResumptionMachine.dimap boolInput (· * 2)) :=
  inputMachinesObsEq.dimap boolInput (· * 2)

example : inputResumptionMachine ⊨ inputProgram :=
  (inputMachinesObsEq.implements_iff inputProgram).mp
    (implements_ofFreeM inputProgram)

example : inputFreeMachine ⊨ inputProgram :=
  (inputMachinesObsEq.implements_iff inputProgram).mpr
    (implements_ofResumption inputProgram)

example : (inputFreeMachine.contramapInput boolInput) ⊨
    (fun input => inputProgram (boolInput input)) :=
  (implements_ofFreeM inputProgram).contramapInput boolInput

example : (inputFreeMachine.dimap boolInput (· * 2)) ⊨
    (fun input => FreeM.map (· * 2) (inputProgram (boolInput input))) :=
  (implements_ofFreeM inputProgram).dimap boolInput (· * 2)

/-- A second realization over `lossySource` pins nonidentity lens congruence. -/
def lossyProgram (input : Nat) : FreeM lossySource Nat :=
  FreeM.liftBind () fun answer => pure (Bool.rec input (input + 1) answer)

def lossyFreeMachine : DynComputation lossySource Nat Nat := ofFreeM lossyProgram

def lossyResumptionMachine : DynComputation lossySource Nat Nat :=
  ofResumption fun input => FreeM.toResumption (lossyProgram input)

theorem lossyMachinesObsEq : ObsEq lossyFreeMachine lossyResumptionMachine :=
  ObsEq.of_implements (implements_ofFreeM lossyProgram)
    (implements_ofResumption lossyProgram)

example : ObsEq
    (lossyFreeMachine.wrap lossyLens)
    (lossyResumptionMachine.wrap lossyLens) :=
  lossyMachinesObsEq.wrap lossyLens

end PFunctor.DynSystem.DynComputation
