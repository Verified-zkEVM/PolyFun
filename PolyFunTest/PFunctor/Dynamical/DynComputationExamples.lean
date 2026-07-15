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

universe uA uB uα uβ

/-- Inputs, outputs, and both polynomial universes remain independent in the
canonical realization. -/
def universeSeparatedOfResumption {p : PFunctor.{uA, uB}} {α : Type uα}
    {β : Type uβ} (semantics : α → Resumption p β) : DynComputation p α β :=
  ofResumption semantics

end PFunctor.DynSystem.DynComputation
