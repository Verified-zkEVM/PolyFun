/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.Kernel.Handler

/-!
# Constructions of kernel handlers

Regression tests for deterministic kernel handlers, Markov program kernels, pullback along free
handlers, and the agreement of the stateless kernel of answer measures with the measure fold. The
Markov and subprobability tests go through the named constructors, so they check that instance
search sees through `ofFun`, `ofMeasure` and `comap`.
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

/-- The handler of a deterministic step is Markov, so the program kernel is Markov. -/
example (program : FreeM Coin Bool) :
    IsMarkovKernel (runKernel (KernelHandler.ofFun countTrue measurable_countTrue) program) := by
  infer_instance

/-- Probability answer measures give a Markov program kernel. -/
example (ν : (a : Coin.A) → Measure (Coin.B a)) [∀ a, IsProbabilityMeasure (ν a)]
    (program : FreeM Coin Bool) :
    IsMarkovKernel (runKernel (KernelHandler.ofMeasure.{0, 0, 0} ν) program) := by
  infer_instance

/-- Subprobability answer measures give a subprobability program kernel. -/
example (ν : (a : Coin.A) → Measure (Coin.B a)) [∀ a, IsSubprobabilityMeasure (ν a)]
    (program : FreeM Coin Bool) :
    IsSubprobabilityKernel (runKernel (KernelHandler.ofMeasure.{0, 0, 0} ν) program) := by
  infer_instance

/-- Each coin flip runs as two flips, keeping the second answer. -/
@[expose] def flipTwice (_ : Coin.A) : FreeM Coin Bool :=
  FreeM.lift () >>= fun _ => FreeM.lift ()

/-- Pulling the Markov counting handler back along a free handler keeps it Markov. -/
example (program : FreeM Coin Bool) :
    IsMarkovKernel (runKernel
      ((KernelHandler.ofFun countTrue measurable_countTrue).comap flipTwice) program) := by
  infer_instance

/-- Pulling a subprobability kernel handler back along a free handler keeps the bound. -/
example (impl : KernelHandler Coin ℕ) [∀ a, IsSubprobabilityKernel (impl a)]
    (program : FreeM Coin Bool) :
    IsSubprobabilityKernel (runKernel (impl.comap flipTwice) program) := by
  infer_instance

/-- The stateless kernel of answer measures agrees with the measure fold. -/
example (ν : (a : Coin.A) → Measure (Coin.B a)) (program : FreeM Coin Bool) :
    runKernel (KernelHandler.ofMeasure.{0, 0, 0} ν) program PUnit.unit =
      (measureFold ν program).map fun x => (x, PUnit.unit) :=
  runKernel_ofMeasure ν program PUnit.unit

end PolyFunTest.Probability.KernelHandler
