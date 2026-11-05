/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunProbability.PFunctor.Free.Kernel
public import PolyFunProbability.PFunctor.Free.Measure

/-!
# Constructions of kernel handlers

A kernel handler samples each operation's answer together with a successor state, and
`PFunctor.FreeM.runKernel` extends it to whole programs. This module gives the constructions that
relate kernel handlers to PolyFun's other handlers and to the measure fold:

* `KernelHandler.comap impl h` runs each operation of `P` as the program `h a` over `Q` under
  `impl`. Interpreting a simulated program is interpreting the source under the pulled-back
  handler (`runKernel_comap`), and pulling back along two free handlers in turn is pulling back
  along their composite (`KernelHandler.comap_comap`).
* `KernelHandler.ofFun step` is the Dirac kernel handler of a measurable deterministic stateful
  step. Its run is the Dirac mass at the deterministic run (`runKernel_ofFun`).
* Markov operation kernels give a Markov program kernel
  (`runKernel.instIsMarkovKernel`).
* `KernelHandler.ofMeasure ν` is the stateless kernel handler of answer measures. Its run is the
  measure fold paired with the unit state (`runKernel_ofMeasure`), so the kernel and measure
  interpretations agree.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe uA uB uS uR uQ

namespace PFunctor

namespace KernelHandler

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uQ, uB}} {S : Type uS}
  [∀ a, MeasurableSpace (P.B a)] [∀ a, MeasurableSpace (Q.B a)] [MeasurableSpace S]

/-- Run each operation of `P` as a program over `Q` under the kernel handler `impl`. -/
noncomputable def comap [∀ b, Countable (Q.B b)] [∀ b, MeasurableSingletonClass (Q.B b)]
    (impl : KernelHandler Q S) (handler : (a : P.A) → FreeM Q (P.B a)) : KernelHandler P S :=
  fun a => FreeM.runKernel impl (handler a)

/-- The Dirac kernel handler of a measurable deterministic stateful step. -/
noncomputable def ofFun (step : (a : P.A) → S → P.B a × S) (hstep : ∀ a, Measurable (step a)) :
    KernelHandler P S :=
  fun a => Kernel.deterministic (step a) (hstep a)

end KernelHandler

namespace FreeM

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type uR}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace α]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

/-- Interpreting a program simulated by a free handler is interpreting the source program under
the pulled-back kernel handler. -/
theorem runKernel_comap {Q : PFunctor.{uQ, uB}} [∀ b, MeasurableSpace (Q.B b)]
    [∀ b, Countable (Q.B b)] [∀ b, MeasurableSingletonClass (Q.B b)] {X : Type uB}
    [MeasurableSpace X] (impl : KernelHandler Q S) (handler : (a : P.A) → FreeM Q (P.B a))
    (program : FreeM P X) (state : S) :
    runKernel impl (program.liftM handler) state = runKernel (impl.comap handler) program state :=
  runKernel_liftM impl handler program state

/-- Markov operation kernels give a Markov program kernel: a lossless kernel handler interprets
every program losslessly. -/
instance runKernel.instIsMarkovKernel (impl : KernelHandler P S) [∀ a, IsMarkovKernel (impl a)]
    (program : FreeM P α) : IsMarkovKernel (runKernel impl program) := by
  induction program with
  | pure x => exact ⟨fun state => by rw [runKernel_pure]; infer_instance⟩
  | lift_bind a next ih =>
      refine ⟨fun state => ⟨?_⟩⟩
      rw [← FreeM.liftBind_eq, runKernel_liftBind, Measure.bind_apply MeasurableSet.univ
        (measurable_runKernel_continuation impl next).aemeasurable]
      simp only [measure_univ, MeasureTheory.lintegral_const, one_mul]

/-- The deterministic run of a stateful step function. -/
def runFun (step : (a : P.A) → S → P.B a × S) : FreeM P α → S → α × S
  | .pure x, state => (x, state)
  | .liftBind a next, state => runFun step (next (step a state).1) (step a state).2

/-- The Dirac kernel handler of a deterministic step runs a program to the Dirac mass at its
deterministic run. -/
theorem runKernel_ofFun (step : (a : P.A) → S → P.B a × S) (hstep : ∀ a, Measurable (step a))
    (program : FreeM P α) (state : S) :
    runKernel (KernelHandler.ofFun step hstep) program state =
      Measure.dirac (runFun step program state) := by
  induction program using FreeM.rec generalizing state with
  | pure x => exact runKernel_pure _ x state
  | liftBind a next ih =>
      rw [runKernel_liftBind, KernelHandler.ofFun, Kernel.deterministic_apply,
        Measure.dirac_bind (measurable_runKernel_continuation _ next)]
      exact ih _ _

end FreeM

namespace KernelHandler

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uQ, uB}} {R : PFunctor.{uQ, uB}} {S : Type uS}
  [∀ a, MeasurableSpace (P.B a)] [∀ a, MeasurableSpace (Q.B a)] [∀ a, MeasurableSpace (R.B a)]
  [MeasurableSpace S]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  [∀ a, Countable (Q.B a)] [∀ a, MeasurableSingletonClass (Q.B a)]
  [∀ a, Countable (R.B a)] [∀ a, MeasurableSingletonClass (R.B a)]

omit [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)] in
/-- Pulling a kernel handler back along two free handlers in turn is pulling it back along their
composite. -/
theorem comap_comap (impl : KernelHandler R S) (handler : (b : Q.A) → FreeM R (Q.B b))
    (handler' : (a : P.A) → FreeM Q (P.B a)) :
    (impl.comap handler).comap handler' = impl.comap fun a => (handler' a).liftM handler := by
  funext a
  ext1 state
  exact (FreeM.runKernel_liftM impl handler (handler' a) state).symm

end KernelHandler

/-! ## The stateless kernel of answer measures -/

namespace KernelHandler

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)]

/-- The stateless kernel handler of answer measures. -/
noncomputable def ofMeasure (ν : (a : P.A) → Measure (P.B a)) : KernelHandler P PUnit.{uS + 1} :=
  fun a => Kernel.const _ ((ν a).map fun b => (b, PUnit.unit))

end KernelHandler

namespace FreeM

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)]
  [∀ a, DiscreteMeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] (ν : (a : P.A) → Measure (P.B a))
  {α : Type uR} [MeasurableSpace α]

/-- The kernel interpretation under the stateless kernel of answer measures is the measure fold,
paired with the unit state. -/
theorem runKernel_ofMeasure (program : FreeM P α) (state : PUnit.{uS + 1}) :
    runKernel (KernelHandler.ofMeasure ν) program state =
      (measureFold ν program).map fun x => (x, state) := by
  have hpair : ∀ {β : Type uR} [MeasurableSpace β] (u : PUnit.{uS + 1}),
      Measurable fun x : β => (x, u) := fun _ => measurable_id.prodMk measurable_const
  induction program using FreeM.rec with
  | pure x =>
      change runKernel _ (pure x) state = (measureFold ν (pure x)).map _
      rw [runKernel_pure, measureFold_pure, Measure.map_dirac' (hpair state)]
  | liftBind a next ih =>
      rw [runKernel_liftBind, measureFold_liftBind ν a next Measurable.of_discrete.aemeasurable]
      simp only [KernelHandler.ofMeasure, Kernel.const_apply]
      rw [Measure.bind_map (f := fun b : P.B a => (b, PUnit.unit))
          (measurable_id.prodMk measurable_const).aemeasurable
          (measurable_runKernel_continuation _ next).aemeasurable,
        Measure.map_bind Measurable.of_discrete.aemeasurable (hpair state).aemeasurable]
      refine Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ?_)
      exact ih b

end FreeM

end PFunctor
