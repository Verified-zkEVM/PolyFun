/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Multiparty.Observation
public import PolyFun.PFunctor.Free.Measure.Kernel
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Terminal decisions on deterministic observations

An observation refinement supplies a single function on reports. Its deterministic kernel
transports a randomized decision for every execution of a polynomial program.
-/

public section

open ProbabilityTheory PFunctor

namespace Interaction.Multiparty.Observation

/-- A decision on a coarse observation can be used after a finer discrete report by first
applying a deterministic function. The function is shared across handlers and initial states. -/
theorem Refines.exists_comp_runKernel {α S : Type*}
    [MeasurableSpace α] [MeasurableSpace S]
    {coarse fine : Observation (α × S)} [MeasurableSpace coarse.1] [MeasurableSpace fine.1]
    [DiscreteMeasurableSpace fine.1] (h : coarse.Refines fine)
    (hc : Measurable coarse.2) (hf : Measurable fine.2) :
    ∃ f : fine.1 → coarse.1,
      ∀ {Action : Type*} [MeasurableSpace Action] (d : Kernel coarse.1 Action)
        {P : PFunctor} [∀ a, MeasurableSpace (P.B a)]
        [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
        (impl : KernelHandler P S) (program : FreeM P α),
      d ∘ₖ (Kernel.deterministic coarse.2 hc ∘ₖ FreeM.runKernel impl program) =
        (d ∘ₖ Kernel.deterministic f Measurable.of_discrete) ∘ₖ
          (Kernel.deterministic fine.2 hf ∘ₖ FreeM.runKernel impl program) := by
  obtain ⟨f, hfactor⟩ := h
  refine ⟨f, ?_⟩
  intro Action _ d P _ _ _ impl program
  apply FreeM.comp_runKernel_of_factor
  rw [Kernel.deterministic_comp_deterministic]
  congr 1
  exact funext hfactor

end Interaction.Multiparty.Observation
