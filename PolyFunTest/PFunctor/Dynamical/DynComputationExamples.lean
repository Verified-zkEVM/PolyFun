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
example : boolRealization ⊨ oneQuery := by
  apply implements_of_isSimulation boolRealization oneQuery BoolResidual boolSimulation
  intro input
  cases input
  exact BoolResidual.start

end PFunctor.DynSystem.DynComputation
