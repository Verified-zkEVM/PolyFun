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

universe u v w uA

namespace PFunctor

variable {S : Type u} {p : PFunctor.{u, u}} {α β mid : Type u}

/-- `nStep` preserves the state set, visible in its type: an `n`-step system on
states `S` is again a system on states `S`. -/
example (φ : DynSystem S p) (n : ℕ) : DynSystem S (compNth p n) := φ.nStep n

/-- `Run_2` collapses to `twoStep` after the inner unitor. -/
example (φ : DynSystem S p) :
    (Lens.id p ◃ₗ Lens.Equiv.compX.toLens) ∘ₗ φ.nStep 2 = φ.twoStep :=
  DynSystem.nStep_two_eq_twoStep φ

/-- `Run_0` performs no transition. -/
example (φ : DynSystem S p) (state : S)
    (direction : (compNth p 0).B ((φ.nStep 0).expose state)) :
    (φ.nStep 0).expose state = PUnit.unit ∧
      (φ.nStep 0).update state direction = state :=
  ⟨DynSystem.nStep_zero_expose φ state,
    DynSystem.nStep_zero_update φ state direction⟩

/-- `Run_1` exposes and executes exactly one transition of the original
system. -/
example (φ : DynSystem S p) (state : S)
    (direction : (compNth p 1).B ((φ.nStep 1).expose state)) :
    (φ.nStep 1).expose state = ⟨φ.expose state, fun _ => PUnit.unit⟩ ∧
      (φ.nStep 1).update state direction = φ.update state direction.1 :=
  ⟨DynSystem.nStep_one_expose φ state,
    DynSystem.nStep_one_update φ state direction⟩

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
def unitHandler : Handler Option X.{0, 0} := fun _ => some PUnit.unit

/-- `runWith` also preserves the independent input, effect, and interface
universes admitted by its monad. -/
example {q : PFunctor.{uA, v}} {m : Type v → Type w} [Monad m]
    {α : Type u} {β : Type v} (M : PointedMachine q α β)
    (h : Handler m q) (s : M.State) :
    M.runWith h 0 s = pure (M.output s) := rfl

/-- A handler whose effect fails if the machine attempts a query. -/
def lossyUnitHandler : Handler Option X.{0, 0} := fun _ => none

/-- One answered query resolves the delayed output: fuel counts queries, and the
readout after the answer is free. -/
example (b : Bool) : (delayMachine b).runWith unitHandler 1 false = some (some b) := rfl

/-- Zero fuel allows no query — the run is still unresolved. -/
example (b : Bool) : (delayMachine b).runWith unitHandler 0 false = some none := rfl

/-- **Fuel irrelevance**: once resolved, more fuel does not change the run. -/
example (b : Bool) :
    (delayMachine b).runWith unitHandler 2 false
      = (delayMachine b).runWith unitHandler 1 false := rfl

/-- A halted state reads off its value at any fuel. The lossy handler witnesses
that no query effect is performed after halting. -/
example (b : Bool) : (delayMachine b).runWith unitHandler 0 true = some (some b) :=
  PointedMachine.runWith_of_output_eq_some _ _ 0 rfl

example (b : Bool) : (delayMachine b).runWith lossyUnitHandler 8 true = some (some b) := by
  exact PointedMachine.runWith_of_output_eq_some _ _ 8 rfl

/-- The output equation is available directly to `simp`. -/
example (M : PointedMachine X.{0, 0} PUnit Bool) (h : Handler Option X.{0, 0})
    (k : ℕ) (s : M.State) (b : Bool) (hb : M.output s = some b) :
    M.runWith h k s = some (some b) := by
  simp [hb]

end PFunctor
