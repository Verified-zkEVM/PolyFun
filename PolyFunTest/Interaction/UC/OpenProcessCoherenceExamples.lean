/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.OpenProcessModel
import all PolyFun.Interaction.UC.OpenProcessSamplerEquiv
public import PolyFun.Interaction.UC.OpenProcessCoherence
public import PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessSamplerEquiv

/-!
# A finite boundary between activation and sampler equivalence

Interleaving two idle processes is activation-equivalent to one idle process.
The composite has two complete step paths, distinguished by the scheduler's
choice, while one idle process has a single path. Therefore no strong sampler
bisimulation can relate even one pair of their states, for any monad relation.
This includes a deterministic scheduler that only samples one of the paths:
strong sampler bisimulation requires a bijection of all structural paths.

The proof inspects the model's unit and sampler-equivalence definitions.
Ordinary-import coherence consumers are checked in `PolyFunTest.ModuleAPI.Interaction`.
-/

public section

namespace PolyFunTest.Interaction.UC.OpenProcessCoherenceExamples

open _root_.Interaction _root_.Interaction.UC

/-- A one-state process with a completed step tree. -/
abbrev idle := openTheoryUnit.{0, 0, 0, 0} PUnit Id

/-- Two idle components with a deterministic scheduler. -/
abbrev doubled := idle.interleave idle
  (TypeTree.Node.ContextHom.id _) (TypeTree.Node.ContextHom.id _)
  (schedulerNode PUnit PortBoundary.empty) ⟨true⟩

/-- Absorbing the silent component preserves activation behavior. -/
theorem doubled_activationEquiv : OpenProcessActivationEquiv doubled idle := by
  let : Inhabited idle.Proc := ⟨PUnit.unit⟩
  exact interleave_unit_left_activationEquiv idle idle (openTheoryUnit_isSilentStep PUnit Id)
    (OpenNodeContext.preservesActivation_id _) (OpenNodeContext.preservesActivation_id _)
    (schedulerNode_isActivated PUnit _) _

/-- Two scheduler paths cannot be put in bijection with the unique idle path. -/
private theorem no_path_equiv (s : doubled.Proc) (t : idle.Proc)
    (e : (doubled.step s).tree.Path ≃ (idle.step t).tree.Path) : False := by
  let : Subsingleton (idle.step t).tree.Path := inferInstanceAs (Subsingleton PUnit)
  have heq := e.injective (Subsingleton.elim (e ⟨⟨true⟩, ⟨⟩⟩) (e ⟨⟨false⟩, ⟨⟩⟩))
  have : true = false := congrArg (fun path => path.1.down) heq
  cases this

/-- Even the coarsest monad relation cannot supply the missing path bijection. -/
example (R : MonadRelFamily Id) : ¬ OpenProcessSamplerEquiv R doubled idle := by
  rintro ⟨rel, hsim, htotal, _⟩
  obtain ⟨t, hrel⟩ := htotal (PUnit.unit, PUnit.unit)
  obtain ⟨e, _⟩ := hsim.step_equiv _ t hrel
  exact no_path_equiv _ t e

end PolyFunTest.Interaction.UC.OpenProcessCoherenceExamples
