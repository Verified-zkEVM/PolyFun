/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.RunN
public import PolyFun.PFunctor.Dynamical.PointedMachine

/-!
# Examples for `n`-step systems and the monad-parametric run

Regression tests: `nStep` preserves the state set and collapses to `twoStep` at
`n = 2`, and the monad-parametric `runWith` gives a concrete deterministic run in
`Option` (the non-probabilistic pays-rent instance), including one-step unfolding
and fuel irrelevance.
-/

@[expose] public section

universe u

namespace PFunctor

variable {p : PFunctor.{u, u}} {α β mid : Type u}

/-- `nStep` preserves the state set. -/
example (φ : DynSystem p) (n : ℕ) : (φ.nStep n).State = φ.State := rfl

/-- `Run_2` collapses to `twoStep` after the inner unitor. -/
example (φ : DynSystem p) :
    (Lens.id p ◃ₗ Lens.Equiv.compX.toLens) ∘ₗ (φ.nStep 2).toLens = φ.twoStep.toLens :=
  DynSystem.twoStep_toLens_eq φ

/-! ## The monad-parametric run in `Option` (pays-rent instance) -/

/-- A one-step-delay machine over `y`: it runs for one step, then halts with `b`
(concrete universe so the `Bool` state set lives in the machine's state type). -/
def delayMachine (b : Bool) : PointedMachine X.{0, 0} PUnit Bool where
  State := Bool
  expose := fun _ => PUnit.unit
  update := fun _ _ => true
  init := fun _ => false
  output := fun s => if s then some b else none

/-- The `Option`-handler on `y`: every position resolves to the unique direction. -/
def unitHandler : PointedMachine.Handler Option X.{0, 0} := fun _ => some PUnit.unit

/-- Two steps of fuel resolve the delayed output. -/
example (b : Bool) : (delayMachine b).runWith unitHandler 2 false = some (some b) := rfl

/-- One step of fuel is not enough — the run is still unresolved. -/
example (b : Bool) : (delayMachine b).runWith unitHandler 1 false = some none := rfl

/-- **Fuel irrelevance**: once resolved, more fuel does not change the run. -/
example (b : Bool) :
    (delayMachine b).runWith unitHandler 3 false
      = (delayMachine b).runWith unitHandler 2 false := rfl

/-- A halted state reads off its value at any positive fuel (via
`runWith_output_some`). -/
example (b : Bool) : (delayMachine b).runWith unitHandler 1 true = some (some b) :=
  PointedMachine.runWith_output_some _ _ 0 rfl

/-- Zero fuel always yields `none`. -/
example (b : Bool) : (delayMachine b).runWith unitHandler 0 false = some none := rfl

end PFunctor
