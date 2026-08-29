/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Interaction.UC.Realizability
public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Representation
public import Mathlib.Data.Fintype.Sigma

/-!
# Dynamical and open-process realizability examples

Regression examples for the non-returning realization boundary and its bridge
to composition-closed UC sub-theories.
-/

public section

namespace PFunctor.DynSystemRealizabilityExamples

/-- A small polynomial interface used to exercise the first-order update
extension without any interaction-specific structure. -/
@[expose]
def bitInterface : PFunctor where
  A := Bool
  B := fun _ => Bool

/-- A state machine that exposes its Boolean state and replaces it with the
direction selected by its environment. -/
@[expose]
def bitSystem : DynSystem Bool bitInterface :=
  DynSystem.mk' id fun _ direction => direction

/-- The generic non-vacuity theorem applies to non-returning systems. -/
example : DynSystem.IsRealizableBy StepClass.unconstrained.{0, 0}
    (DynSystem.Boundary.unconstrained bitInterface) bitSystem :=
  DynSystem.isRealizableBy_unconstrained bitSystem

/-- Changing a pinned interface representation through a mutually admissible
translation does not change structural realizability. -/
example (left right : DynSystem.Boundary StepClass.unconstrained.{0, 0}
    bitInterface) :
    DynSystem.IsRealizableBy StepClass.unconstrained left bitSystem ↔
      DynSystem.IsRealizableBy StepClass.unconstrained right bitSystem :=
  DynSystem.isRealizableBy_iff_of_boundary_polyTranslatable
    ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩

/-! ### Finite-state closure under asynchronous choice -/

instance : DecidableEq bitInterface.A :=
  inferInstanceAs (DecidableEq Bool)

instance : DecidableEq (PFunctor.prod bitInterface bitInterface).A :=
  inferInstanceAs (DecidableEq (Bool × Bool))

/-- The pinned finite representations of the bit interface. -/
def bitBoundary : DynSystem.Boundary StepClass.finite.{0} bitInterface :=
  ⟨inferInstanceAs (Fintype Bool), inferInstanceAs (Fintype (Σ _ : Bool, Bool))⟩

/-- The pinned finite representations of the paired interface, including the
sigma-shaped flattened index space. -/
def bitPairBoundary :
    DynSystem.Boundary StepClass.finite.{0}
      (PFunctor.prod bitInterface bitInterface) :=
  ⟨inferInstanceAs (Fintype (Bool × Bool)),
    inferInstanceAs (Fintype (Σ _ : Bool × Bool, Bool ⊕ Bool))⟩

/-- The bit machine is finite-state realizable with its literal update
extension. -/
def bitRealization :
    DynSystem.Realization StepClass.finite.{0} bitBoundary bitSystem :=
  ⟨inferInstanceAs (Fintype Bool), True.intro, bitSystem.update?, True.intro,
    bitSystem.update?_of_eq⟩

/-- The product-state combinator produces a finite-state witness for the
wrapped asynchronous choice of two bit machines. -/
example : DynSystem.IsRealizableBy StepClass.finite.{0} bitPairBoundary
    ((bitSystem.choiceProd bitSystem).wrap
      (PFunctor.Lens.id (PFunctor.prod bitInterface bitInterface))) :=
  DynSystem.IsRealizableBy.wrapChoiceProd ⟨bitRealization⟩ ⟨bitRealization⟩
    ⟨True.intro,
      (PFunctor.Lens.id (PFunctor.prod bitInterface bitInterface)).pullChoicePosIdx,
      True.intro,
      (PFunctor.Lens.id
        (PFunctor.prod bitInterface bitInterface)).pullChoicePosIdx_enabled⟩

/-- The routed pullback reports a mismatched position tag as a disabled
step. -/
example (a : Bool × Bool) (index : (PFunctor.prod bitInterface bitInterface).Idx)
    (hne : index.1 ≠ a) :
    (PFunctor.Lens.id
      (PFunctor.prod bitInterface bitInterface)).pullChoicePosIdx (a, index) =
      none := by
  unfold PFunctor.Lens.pullChoicePosIdx
  rw [dif_neg]
  exact fun h => hne h

end PFunctor.DynSystemRealizabilityExamples

namespace Interaction.UC.OpenProcessRealizabilityExamples

open PFunctor

abbrev Party := PUnit
abbrev M := Id

def schedulerSampler : M (ULift Bool) := ULift.up true

/-- The unconstrained boundary family pins the unique representation at every
open boundary. -/
def boundary (Δ : PortBoundary) :
    OpenProcess.StructuralBoundary.{0, 0, 0, 0}
      StepClass.unconstrained.{1, 0} Party Δ :=
  ⟨PUnit.unit, PUnit.unit⟩

/-- In the unconstrained class every lens is admissible, so the four
certificate fields of the closure contract are inhabited.  The composite
closure theorems `par_mem` / `wire_mem` / `plug_mem` are *not* assumed: they
fire generically through the product-state combinator. -/
noncomputable instance : OpenProcess.IsRealizabilityClosed Party
    StepClass.unconstrained.{1, 0} boundary where
  mapAdmissible := by
    intro _ _ φ
    exact Lens.IsDynAdmissible.unconstrained
      (OpenProcess.structuralMapLens Party φ)
  parAdmissible := by
    intro Δ₁ Δ₂
    exact Lens.IsChoiceAdmissible.unconstrained _
  wireAdmissible := by
    intro Δ₁ Γ Δ₂
    exact Lens.IsChoiceAdmissible.unconstrained _
  plugAdmissible := by
    intro Δ
    exact Lens.IsChoiceAdmissible.unconstrained _

/-- Direct realizability now forms a plug-closed sub-theory. -/
example : (realizableSubTheory Party StepClass.unconstrained.{1, 0}
    boundary schedulerSampler).IsPlugClosed := inferInstance

/-- The composite closure theorems fire end-to-end through the product-state
combinator. -/
example {Δ₁ Δ₂ : PortBoundary}
    {left : OpenProcess M Party Δ₁} {right : OpenProcess M Party Δ₂}
    (h₁ : left.IsStructurallyRealizableBy
      StepClass.unconstrained.{1, 0} (boundary Δ₁))
    (h₂ : right.IsStructurallyRealizableBy
      StepClass.unconstrained.{1, 0} (boundary Δ₂)) :
    ((openTheory Party M schedulerSampler).par left
      right).IsStructurallyRealizableBy
      StepClass.unconstrained.{1, 0} (boundary (PortBoundary.tensor Δ₁ Δ₂)) :=
  OpenProcess.IsRealizabilityClosed.par_mem schedulerSampler h₁ h₂

/-- In the unconstrained instance every open process is directly allowed. -/
example {Δ : PortBoundary} (process : OpenProcess M Party Δ) :
    (realizableSubTheory Party StepClass.unconstrained.{1, 0}
      boundary schedulerSampler).mem process :=
  DynSystem.isRealizableBy_unconstrained _

end Interaction.UC.OpenProcessRealizabilityExamples
