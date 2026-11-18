/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.Lighthouse

/-!
# Certifying the five-label result for the ferry solver

The joint decoder witnesses feasibility. The coding theorem bounds every competing
decoder, so the solver's certificate follows without enumerating partitions of the 25 sightings.
-/

public section

namespace PolyFunExamples.Bargaining.Replay.Lighthouse

export PolyFunExamples.Lighthouse (joint_fiber_card_le joint_lower_bound)

/-- The explicit five-label code attains the minimum among all joint hints and decoders. -/
theorem minimum_joint : (minimumHint .gain jointBoard).size? = some 5 := by
  apply HintResult.size?_of_bounds _ joint_valid
  intro j hint decoder hd
  exact PolyFunExamples.Lighthouse.joint_optimal.2
    ⟨hint, decoder, (valid_recoveryBoard_iff _ _ _ _).1 hd⟩

end PolyFunExamples.Bargaining.Replay.Lighthouse
