/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunProbability.PFunctor.Free.Kernel.Handler

/-!
# Constructions of kernel handlers

Regression tests for deterministic kernel handlers, Markov program kernels, pullback along free
handlers, and the agreement of the stateless kernel of answer measures with the measure fold.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.FreeM

namespace PolyFunTest.Probability.KernelHandler

/-- One operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A deterministic step: answer `true` and count the call. -/
@[expose] def countTrue (_ : Coin.A) (n : ℕ) : Bool × ℕ := (true, n + 1)

theorem measurable_countTrue (a : Coin.A) : Measurable (countTrue a) := Measurable.of_discrete

/-- A single call of the counting handler is the Dirac mass at its step. -/
example : runKernel (KernelHandler.ofFun countTrue measurable_countTrue) (FreeM.lift ()) 0 =
    Measure.dirac (true, 1) :=
  runKernel_ofFun countTrue measurable_countTrue (FreeM.lift ()) 0

/-- Deterministic operation kernels are Markov, so the program kernel is Markov. -/
example (program : FreeM Coin Bool) :
    IsMarkovKernel (runKernel (fun a => Kernel.deterministic (countTrue a)
      (measurable_countTrue a)) program) := inferInstance

/-- The stateless kernel of answer measures agrees with the measure fold. -/
example (ν : (a : Coin.A) → Measure (Coin.B a)) (program : FreeM Coin Bool) :
    runKernel (KernelHandler.ofMeasure.{0, 0, 0} ν) program PUnit.unit =
      (measureFold ν program).map fun x => (x, PUnit.unit) :=
  runKernel_ofMeasure ν program PUnit.unit

end PolyFunTest.Probability.KernelHandler
