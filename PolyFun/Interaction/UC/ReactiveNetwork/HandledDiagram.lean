/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveNetwork.Factorization.Right

/-!
# Reactive diagrams with intrinsic effect interpreters

A handled diagram carries the interpretation of each component's polynomial operations.
Composition and factorization preserve those interpreters alongside the component machines.
The chosen effect monad is explicit. Specializing it to a stateless sampling monad gives
local random operations without granting access to another component's private state;
choosing a shared-state monad grants the capabilities expressed by that monad instead.

The interpreter's internal work is not counted by a single network activation. Computational
admission must bound that work separately, along with routing and machine updates.
-/

public section

namespace Interaction.UC.ReactiveNetwork

open PFunctor ReactiveProcess

/-- An open reactive diagram together with the interpretation of every local operation. -/
structure HandledDiagram (m : Type → Type) (Node : Type) (boundary : PortBoundary)
    (result : Type) extends Diagram Node boundary result where
  /-- The local interpreter is part of the component's executable data. -/
  handler : (node : Node) → Handler m (effect node)

namespace HandledDiagram

variable {m : Type → Type} {N N₁ N₂ K result : Type} {Δ Δ₁ Δ₂ Γ : PortBoundary}

/-- Equality retains both the routing diagram and its local interpretations. -/
@[ext] theorem ext {left right : HandledDiagram m N Δ result}
    (hdiagram : left.toDiagram = right.toDiagram) (hhandler : HEq left.handler right.handler) :
    left = right := by
  cases left
  cases right
  cases hdiagram
  cases hhandler
  rfl

/-- One initialized polynomial machine with its declared effect interpreter. -/
@[expose] def atom {effect : PFunctor.{0, 0}} (process : Process effect Δ Unit result)
    (handler : Handler m effect) : HandledDiagram m Unit Δ result where
  toDiagram := Diagram.atom process
  handler _ := handler

/-- Relabel components and their local interpreters together. -/
@[expose] def reindex (diagram : HandledDiagram m N Δ result) (e : N₁ ≃ N) :
    HandledDiagram m N₁ Δ result where
  toDiagram := diagram.toDiagram.reindex e
  handler node := diagram.handler (e node)

/-- External boundary adaptation preserves local interpretations. -/
@[expose] def map (f : PortBoundary.Hom Δ₁ Δ₂) (diagram : HandledDiagram m N Δ₁ result) :
    HandledDiagram m N Δ₂ result where
  toDiagram := diagram.toDiagram.map f
  handler := diagram.handler

/-- Parallel fragments retain their own interpreters on disjoint component identities. -/
@[expose] def par (left : HandledDiagram m N₁ Δ₁ result)
    (right : HandledDiagram m N₂ Δ₂ result) :
    HandledDiagram m (N₁ ⊕ N₂) (PortBoundary.tensor Δ₁ Δ₂) result where
  toDiagram := left.toDiagram.par right.toDiagram
  handler
    | .inl node => left.handler node
    | .inr node => right.handler node

/-- Wiring changes packet routes and retains both local interpreters. -/
@[expose] def wire (left : HandledDiagram m N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledDiagram m N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result) :
    HandledDiagram m (N₁ ⊕ N₂) (PortBoundary.tensor Δ₁ Δ₂) result where
  toDiagram := left.toDiagram.wire right.toDiagram
  handler
    | .inl node => left.handler node
    | .inr node => right.handler node

/-- Closure retains the effects of both protocol and context components. -/
@[expose] def plug (left : HandledDiagram m N₁ Δ result)
    (right : HandledDiagram m N₂ (PortBoundary.swap Δ) result) :
    HandledDiagram m (N₁ ⊕ N₂) PortBoundary.empty result where
  toDiagram := left.toDiagram.plug right.toDiagram
  handler
    | .inl node => left.handler node
    | .inr node => right.handler node

/-- Move the right parallel fragment into a context without changing its interpreter. -/
@[expose] def parContextLeft (right : HandledDiagram m N₂ Δ₂ result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    HandledDiagram m (K ⊕ N₂) (PortBoundary.swap Δ₁) result where
  toDiagram := right.toDiagram.parContextLeft context.toDiagram
  handler
    | .inl node => context.handler node
    | .inr node => right.handler node

/-- Move the left parallel fragment into a context without changing its interpreter. -/
@[expose] def parContextRight (left : HandledDiagram m N₁ Δ₁ result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    HandledDiagram m (K ⊕ N₁) (PortBoundary.swap Δ₂) result where
  toDiagram := left.toDiagram.parContextRight context.toDiagram
  handler
    | .inl node => context.handler node
    | .inr node => left.handler node

/-- Move the right wired fragment into a context while retaining both effect interpretations. -/
@[expose] def wireContextLeft
    (right : HandledDiagram m N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    HandledDiagram m (K ⊕ N₂) (PortBoundary.swap (PortBoundary.tensor Δ₁ Γ)) result where
  toDiagram := right.toDiagram.wireContextLeft context.toDiagram
  handler
    | .inl node => context.handler node
    | .inr node => right.handler node

/-- Move the left wired fragment into a context while retaining both effect interpretations. -/
@[expose] def wireContextRight (left : HandledDiagram m N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    HandledDiagram m (K ⊕ N₁) (PortBoundary.swap (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      result where
  toDiagram := left.toDiagram.wireContextRight context.toDiagram
  handler
    | .inl node => context.handler node
    | .inr node => left.handler node

attribute [local implicit_reducible] reindex par wire plug parContextLeft parContextRight
  wireContextLeft wireContextRight

/-- Parallel factorization retains the actual interpretations of all component operations. -/
theorem close_par_left (left : HandledDiagram m N₁ Δ₁ result)
    (right : HandledDiagram m N₂ Δ₂ result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    ((left.par right).plug context).reindex (Diagram.parContextLeftEquiv N₁ N₂ K) =
      left.plug (right.parContextLeft context) := by
  apply HandledDiagram.ext
  · exact Diagram.close_par_left _ _ _
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node | node <;> rfl

/-- Right parallel factorization retains all local interpreters. -/
theorem close_par_right (left : HandledDiagram m N₁ Δ₁ result)
    (right : HandledDiagram m N₂ Δ₂ result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    ((left.par right).plug context).reindex (Diagram.parContextRightEquiv N₁ N₂ K) =
      right.plug (left.parContextRight context) := by
  apply HandledDiagram.ext
  · exact Diagram.close_par_right _ _ _
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node | node <;> rfl

/-- Left wired factorization retains all local interpreters. -/
theorem close_wire_left (left : HandledDiagram m N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledDiagram m N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    ((left.wire right).plug context).reindex (Diagram.parContextLeftEquiv N₁ N₂ K) =
      left.plug (right.wireContextLeft context) := by
  apply HandledDiagram.ext
  · exact Diagram.close_wire_left _ _ _
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node | node <;> rfl

/-- Right wired factorization retains all local interpreters. -/
theorem close_wire_right (left : HandledDiagram m N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledDiagram m N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    ((left.wire right).plug context).reindex (Diagram.parContextRightEquiv N₁ N₂ K) =
      right.plug (left.wireContextRight context) := by
  apply HandledDiagram.ext
  · exact Diagram.close_wire_right _ _ _
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node | node <;> rfl

/-- A directly connected pair of initialized machines and their local interpreters. -/
@[expose] def closedPair {p q : PFunctor.{0, 0}} (left : Process p Δ Unit result)
    (leftHandler : Handler m p) (right : Process q (PortBoundary.swap Δ) Unit result)
    (rightHandler : Handler m q) : HandledDiagram m (Unit ⊕ Unit) PortBoundary.empty result where
  toDiagram := { (Diagram.atom left).plug (Diagram.atom right) with
    route
      | .inl _, packet => .inl ⟨.inr (), packet⟩
      | .inr _, packet => .inl ⟨.inl (), packet⟩ }
  handler
    | .inl _ => leftHandler
    | .inr _ => rightHandler

attribute [local implicit_reducible] atom closedPair

/-- Closing two atoms runs the directly connected pair, with no intermediate relay component. -/
theorem atom_plug_atom {p q : PFunctor.{0, 0}} (left : Process p Δ Unit result)
    (leftHandler : Handler m p) (right : Process q (PortBoundary.swap Δ) Unit result)
    (rightHandler : Handler m q) :
    (atom left leftHandler).plug (atom right rightHandler) =
      closedPair left leftHandler right rightHandler := by
  apply HandledDiagram.ext
  · apply Diagram.ext
    · rfl
    · rfl
    · rfl
    · apply heq_of_eq
      funext node packet
      rcases node with node | node
      · exact Diagram.plug_route_left (Diagram.atom left) (Diagram.atom right) node packet
      · exact Diagram.plug_route_right (Diagram.atom left) (Diagram.atom right) node packet
    · rfl
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node <;> rfl

/-- Select the one global environment after all fragments have been composed. -/
@[expose] def network (diagram : HandledDiagram m N Δ result) (environment : N) :
    Network N Δ result := diagram.toDiagram.withEnvironment environment

variable [Monad m]

/-- Lift local operations into the runner's unit service state. The component's own machine
state remains private; any ambient capabilities are exactly those of the explicit monad `m`. -/
@[expose] def handlers (diagram : HandledDiagram m N Δ result) (environment : N) :
    (node : N) → Handler (StateT Unit m) ((diagram.network environment).effect node) :=
  fun node operation _ => (fun response => (response, ())) <$> diagram.handler node operation

/-- Execute the actual token runner and read the chosen environment's terminal outcome. -/
@[expose] def tokenObservation [DecidableEq N] (diagram : HandledDiagram m N Δ result)
    (environment : N) (fuel : ℕ) : m (Option (Outcome result)) :=
  outcome environment <$> runToken (diagram.handlers environment) fuel
    (initial (diagram.network environment) ())

/-- Execute the actual FIFO runner and read the chosen environment's terminal outcome. -/
@[expose] def fifoObservation [DecidableEq N] (diagram : HandledDiagram m N Δ result)
    (environment : N) (schedule : List (Activation N)) : m (Option (Outcome result)) :=
  outcome environment <$> runFIFO (diagram.handlers environment) schedule
    (initial (diagram.network environment) ())

variable [LawfulMonad m]

/-- Relabeling preserves the token observation with the interpreter carried by each node. -/
theorem tokenObservation_reindex [DecidableEq N] [DecidableEq N₁]
    (diagram : HandledDiagram m N Δ result) (e : N₁ ≃ N) (environment : N) (fuel : ℕ) :
    (diagram.reindex e).tokenObservation (e.symm environment) fuel =
      diagram.tokenObservation environment fuel := by
  change (outcome (e.symm environment) <$>
    runToken (network := (diagram.network environment).reindex e)
      (fun node => diagram.handlers environment (e node)) fuel
      (initial ((diagram.network environment).reindex e) ())) = _
  rw [initial_reindex, runToken_reindex, Functor.map_map]
  congr 1
  funext state
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    outcome_reindex e (e.symm environment) state

/-- Relabeling preserves FIFO observations when the schedule follows the node bijection. -/
theorem fifoObservation_reindex [DecidableEq N] [DecidableEq N₁]
    (diagram : HandledDiagram m N Δ result) (e : N₁ ≃ N) (environment : N)
    (schedule : List (Activation N)) :
    (diagram.reindex e).fifoObservation (e.symm environment)
        (schedule.map (Activation.reindex e)) = diagram.fifoObservation environment schedule := by
  change (outcome (e.symm environment) <$>
    runFIFO (network := (diagram.network environment).reindex e)
      (fun node => diagram.handlers environment (e node))
      (schedule.map (Activation.reindex e))
      (initial ((diagram.network environment).reindex e) ())) = _
  rw [initial_reindex, runFIFO_reindex, Functor.map_map]
  congr 1
  funext state
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    outcome_reindex e (e.symm environment) state

variable [DecidableEq N₁] [DecidableEq N₂] [DecidableEq K]

/-- Factoring parallel closure preserves the actual effectful token experiment. -/
theorem tokenObservation_close_par_left (left : HandledDiagram m N₁ Δ₁ result)
    (right : HandledDiagram m N₂ Δ₂ result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) (fuel : ℕ) :
    (left.plug (right.parContextLeft context)).tokenObservation (.inr (.inl environment)) fuel =
      ((left.par right).plug context).tokenObservation (.inr environment) fuel := by
  rw [← close_par_left]
  exact tokenObservation_reindex _ (Diagram.parContextLeftEquiv N₁ N₂ K) (.inr environment) fuel

/-- The right parallel residual context preserves the actual effectful token experiment. -/
theorem tokenObservation_close_par_right (left : HandledDiagram m N₁ Δ₁ result)
    (right : HandledDiagram m N₂ Δ₂ result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) (fuel : ℕ) :
    (right.plug (left.parContextRight context)).tokenObservation (.inr (.inl environment)) fuel =
      ((left.par right).plug context).tokenObservation (.inr environment) fuel := by
  rw [← close_par_right]
  exact tokenObservation_reindex _ (Diagram.parContextRightEquiv N₁ N₂ K) (.inr environment) fuel

/-- The left wired residual context preserves the actual effectful token experiment. -/
theorem tokenObservation_close_wire_left
    (left : HandledDiagram m N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledDiagram m N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) (fuel : ℕ) :
    (left.plug (right.wireContextLeft context)).tokenObservation (.inr (.inl environment)) fuel =
      ((left.wire right).plug context).tokenObservation (.inr environment) fuel := by
  rw [← close_wire_left]
  exact tokenObservation_reindex _ (Diagram.parContextLeftEquiv N₁ N₂ K) (.inr environment) fuel

/-- The right wired residual context preserves the actual effectful token experiment. -/
theorem tokenObservation_close_wire_right
    (left : HandledDiagram m N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledDiagram m N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) (fuel : ℕ) :
    (right.plug (left.wireContextRight context)).tokenObservation (.inr (.inl environment)) fuel =
      ((left.wire right).plug context).tokenObservation (.inr environment) fuel := by
  rw [← close_wire_right]
  exact tokenObservation_reindex _ (Diagram.parContextRightEquiv N₁ N₂ K) (.inr environment) fuel

/-- Left par factorization preserves FIFO observations under the transported schedule. -/
theorem fifoObservation_close_par_left (left : HandledDiagram m N₁ Δ₁ result)
    (right : HandledDiagram m N₂ Δ₂ result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) (schedule : List (Activation ((N₁ ⊕ N₂) ⊕ K))) :
    (left.plug (right.parContextLeft context)).fifoObservation (.inr (.inl environment))
        (schedule.map (Activation.reindex (Diagram.parContextLeftEquiv N₁ N₂ K))) =
      ((left.par right).plug context).fifoObservation (.inr environment) schedule := by
  rw [← close_par_left]
  exact fifoObservation_reindex _ (Diagram.parContextLeftEquiv N₁ N₂ K) (.inr environment) schedule

/-- Right par factorization preserves FIFO observations under the transported schedule. -/
theorem fifoObservation_close_par_right (left : HandledDiagram m N₁ Δ₁ result)
    (right : HandledDiagram m N₂ Δ₂ result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) (schedule : List (Activation ((N₁ ⊕ N₂) ⊕ K))) :
    (right.plug (left.parContextRight context)).fifoObservation (.inr (.inl environment))
        (schedule.map (Activation.reindex (Diagram.parContextRightEquiv N₁ N₂ K))) =
      ((left.par right).plug context).fifoObservation (.inr environment) schedule := by
  rw [← close_par_right]
  exact fifoObservation_reindex _ (Diagram.parContextRightEquiv N₁ N₂ K) (.inr environment) schedule

/-- Left wire factorization preserves FIFO observations under the transported schedule. -/
theorem fifoObservation_close_wire_left
    (left : HandledDiagram m N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledDiagram m N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) (schedule : List (Activation ((N₁ ⊕ N₂) ⊕ K))) :
    (left.plug (right.wireContextLeft context)).fifoObservation (.inr (.inl environment))
        (schedule.map (Activation.reindex (Diagram.parContextLeftEquiv N₁ N₂ K))) =
      ((left.wire right).plug context).fifoObservation (.inr environment) schedule := by
  rw [← close_wire_left]
  exact fifoObservation_reindex _ (Diagram.parContextLeftEquiv N₁ N₂ K) (.inr environment) schedule

/-- Right wire factorization preserves FIFO observations under the transported schedule. -/
theorem fifoObservation_close_wire_right
    (left : HandledDiagram m N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledDiagram m N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledDiagram m K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) (schedule : List (Activation ((N₁ ⊕ N₂) ⊕ K))) :
    (right.plug (left.wireContextRight context)).fifoObservation (.inr (.inl environment))
        (schedule.map (Activation.reindex (Diagram.parContextRightEquiv N₁ N₂ K))) =
      ((left.wire right).plug context).fifoObservation (.inr environment) schedule := by
  rw [← close_wire_right]
  exact fifoObservation_reindex _ (Diagram.parContextRightEquiv N₁ N₂ K) (.inr environment) schedule

end HandledDiagram

end Interaction.UC.ReactiveNetwork
