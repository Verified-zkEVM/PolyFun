/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Representation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi

/-! # A finite two-worker controller

Only occupancy is modeled: `false` selects the first slot and `true` the second. A request to
assign a busy slot is rejected without changing occupancy. Completion frees that slot. Job payloads,
OS processes, and unbounded histories are deliberately outside this finite-state boundary.
The example constructs real finite representations, not an unconstrained realizability witness.
-/

@[expose] public section

namespace PolyFunExamples.BoundedController

open PFunctor

/-- Occupancy of the two independently addressable slots. -/
abbrev Slots := Bool → Bool

/-- A slot and its requested occupancy: `true` assigns, `false` completes. -/
abbrev Request := Bool × Bool

/-- Assigning a busy slot is rejected; all other requests update only the selected slot. -/
def accepted (slots : Slots) (request : Request) : Bool :=
  !(request.2 && slots request.1)

/-- The controller has no access to the payload of a job. -/
def update (slots : Slots) (request : Request) : Slots :=
  if accepted slots request then Function.update slots request.1 request.2 else slots

/-- Observations are occupancy; responses are requests from the surrounding application. -/
def interface : PFunctor := ⟨Slots, fun _ ↦ Request⟩

instance : DecidableEq interface.A := inferInstanceAs (DecidableEq Slots)

/-- One ongoing finite-state controller. -/
def controller : DynSystem Slots interface := (fun slots ↦ slots) ⇆ update

/-- Reassignment of a busy slot is rejected without changing either slot. -/
theorem update_busy (slots : Slots) (slot : Bool) (busy : slots slot = true) :
    accepted slots (slot, true) = false ∧ update slots (slot, true) = slots := by
  simp [accepted, update, busy]

/-- A completed job frees its slot. -/
theorem update_complete (slots : Slots) (slot : Bool) :
    update slots (slot, false) slot = false := by
  simp [update, accepted]

/-- No request can overwrite another worker's occupancy. -/
theorem update_other (slots : Slots) (request : Request) (other : Bool)
    (different : other ≠ request.1) : update slots request other = slots other := by
  unfold update
  split <;> simp [Function.update_of_ne different]

/-- The exact number of control states is four, independent of job contents. -/
theorem card_slots : Fintype.card Slots = 4 := by decide

/-- Actual finite enumerations of the observable boundary and its dependent indices. -/
def boundary : DynSystem.Boundary StepClass.finite interface :=
  ⟨inferInstanceAs (Fintype Slots), inferInstanceAs (Fintype (Σ _ : Slots, Request))⟩

/-- Finite private states and the existing checked dependent update extension. -/
def realization : DynSystem.Realization StepClass.finite boundary controller :=
  ⟨inferInstanceAs (Fintype Slots), True.intro, controller.update?, True.intro,
    controller.update?_of_eq⟩

/-- A pair of bits is an equivalent concrete presentation of occupancy. -/
def slotsEquiv : Slots ≃ Bool × Bool where
  toFun slots := (slots false, slots true)
  invFun pair slot := if slot then pair.2 else pair.1
  left_inv slots := by funext slot; cases slot <;> rfl
  right_inv pair := by cases pair; rfl

/-- Re-enumerate the same observable states through their pair representation. -/
def pairBoundary : DynSystem.Boundary StepClass.finite interface :=
  ⟨Fintype.ofEquiv (Bool × Bool) slotsEquiv.symm,
    inferInstanceAs (Fintype (Σ _ : Slots, Request))⟩

/-- Boundary translation preserves the realization; it asserts no time complexity bound. -/
def pairRealization : DynSystem.Realization StepClass.finite pairBoundary controller :=
  realization.translateBoundary ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩

/-- A small assign/reassign/complete session. -/
def session : List (Bool × Bool) :=
  [(false, true), (false, true), (true, true), (false, false)]

/-- Only the second worker remains occupied after the session. -/
example : slotsEquiv (session.foldl update (fun _ ↦ false)) = (false, true) := rfl

end PolyFunExamples.BoundedController
