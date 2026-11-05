/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure
public import PolyFun.PFunctor.Free.Measure.Kernel
public import PolyFun.PFunctor.Free.Measure.Path
public import PolyFun.PFunctor.Wiring.Measure

/-!
# Measure and kernel semantics of free programs

Regression tests for the measure fold, the kernel extension of a stateful kernel handler, and the
path measure, over a fair coin, and the universes of the kernel semantics of wiring.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.FreeM

namespace PolyFunTest.Probability.FreeMeasure

/-- One operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A fair coin: uniform answers on the two-point type. -/
noncomputable instance : Coin.AnswerMeasure := AnswerMeasure.uniformOfFiniteNonempty Coin

/-- Two independent flips. -/
@[expose] def twoFlips : FreeM Coin (Bool × Bool) := do
  let x ← FreeM.lift (P := Coin) ()
  let y ← FreeM.lift (P := Coin) ()
  pure (x, y)

/-- A single flip denotes the uniform measure on its answers. -/
example : denote (FreeM.lift (P := Coin) ()) = uniformOn Set.univ := denote_lift (P := Coin) ()

/-- Every program over discrete answers is lossless. -/
example : IsProbabilityMeasure (denote twoFlips) := inferInstance

/-- Two independent flips denote the product of the two flip measures. -/
example :
    denote (FreeM.bind (FreeM.lift (P := Coin) ()) fun x =>
      FreeM.bind (FreeM.lift (P := Coin) ()) fun y => pure (x, y)) =
      (uniformOn Set.univ : Measure Bool).prod (uniformOn Set.univ) := by
  rw [denote_bind_bind_prod_mk_eq_prod (P := Coin), denote_lift (P := Coin)]
  rfl

/-- Mapping an output pushes the measure forward. -/
example : denote (FreeM.map Prod.fst twoFlips) = (denote twoFlips).map Prod.fst :=
  denote_map_of_discrete twoFlips Prod.fst

/-- A kernel handler that answers with a fair coin and counts the calls in its state. -/
noncomputable def countingCoin : KernelHandler Coin ℕ := fun _ =>
  Kernel.ofFunOfCountable fun n => (uniformOn Set.univ : Measure Bool).map fun b => (b, n + 1)

/-- The kernel extension runs a single call as that call's kernel. -/
example (n : ℕ) : runKernel countingCoin (FreeM.lift ()) n = countingCoin () n :=
  runKernel_lift countingCoin () n

/-- Each call of the counting handler is lossless, so the whole run is a subprobability kernel. -/
example (program : FreeM Coin Bool) [∀ a, IsSubprobabilityKernel (countingCoin a)] :
    IsSubprobabilityKernel (runKernel countingCoin program) := inferInstance

/-- Wiring has kernel semantics at the universes of `Wiring.eval`: boxes in `Type 1`, inputs in
`Type 2`, arities in `Type 1`, and interfaces whose positions lie above their answers. -/
noncomputable example {Boxes : Type 1} {Inputs : Type 2} {Arity : Boxes → Type 1}
    {Dom : (b : Boxes) → Arity b → PFunctor.{1, 0}} {Cod : Boxes → PFunctor.{1, 0}}
    {inputInterface : Inputs → PFunctor.{1, 0}} {output : PFunctor.{1, 0}}
    [∀ a, MeasurableSpace ((PFunctor.sigma inputInterface).B a)]
    [∀ a, Countable ((PFunctor.sigma inputInterface).B a)]
    [∀ a, MeasurableSingletonClass ((PFunctor.sigma inputInterface).B a)]
    (implementation : (b : Boxes) → (a : (Cod b).A) →
      FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (services : KernelHandler (PFunctor.sigma inputInterface) ℕ)
    (wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output) (a : output.A)
    [MeasurableSpace (output.B a)] : Kernel ℕ (output.B a × ℕ) :=
  Wiring.runKernel implementation services wiring a

end PolyFunTest.Probability.FreeMeasure
