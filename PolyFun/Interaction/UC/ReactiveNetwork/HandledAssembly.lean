/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveNetwork.HandledDiagram
public import PolyFun.Interaction.UC.ReactiveNetwork.Assembly

/-!
# Finite assemblies carrying their effect interpreters

Raw open syntax compiles components and their local effect interpretations together.
The resulting finite assembly selects its single environment only when it is executed.
A structural adapter is an ordinary assembly on the corresponding pair of boundaries;
its applications and relay steps therefore use the same routed runtime as every other node.
-/

public section

universe u

namespace Interaction.UC.ReactiveNetwork

open PFunctor ReactiveProcess

/-- A finite executable fragment with intrinsic local effect interpreters. -/
structure HandledAssembly (m : Type → Type) (boundary : PortBoundary) (result : Type) where
  /-- Static component identities. -/
  Node : Type
  /-- Finite topology, fixed by the assembly. -/
  [fintypeNode : Fintype Node]
  /-- Decidable identities for local-state and mailbox updates. -/
  [decidableEqNode : DecidableEq Node]
  /-- The component machines, typed routes, and interpreters. -/
  diagram : HandledDiagram m Node boundary result

attribute [instance] HandledAssembly.fintypeNode HandledAssembly.decidableEqNode

namespace HandledAssembly

variable {m : Type → Type} {result : Type} {Δ Δ₁ Δ₂ Γ : PortBoundary}

/-- Bundle a finite handled diagram without changing its executable data. -/
@[expose] def ofDiagram {Node : Type} [Fintype Node] [DecidableEq Node]
    (diagram : HandledDiagram m Node Δ result) : HandledAssembly m Δ result := ⟨Node, diagram⟩

/-- Assemble one polynomial machine with its local interpreter. -/
@[expose] def atom {effect : PFunctor.{0, 0}} (process : Process effect Δ Unit result)
    (handler : Handler m effect) : HandledAssembly m Δ result :=
  ofDiagram (HandledDiagram.atom process handler)

/-- Adapt only external traffic, preserving machines and interpreters. -/
@[expose] def map (f : PortBoundary.Hom Δ₁ Δ₂) (assembly : HandledAssembly m Δ₁ result) :
    HandledAssembly m Δ₂ result := ofDiagram (assembly.diagram.map f)

/-- Assemble fragments in parallel with disjoint component identities. -/
@[expose] def par (left : HandledAssembly m Δ₁ result) (right : HandledAssembly m Δ₂ result) :
    HandledAssembly m (PortBoundary.tensor Δ₁ Δ₂) result :=
  ofDiagram (left.diagram.par right.diagram)

/-- Connect the shared boundary of two executable fragments. -/
@[expose] def wire (left : HandledAssembly m (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledAssembly m (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result) :
    HandledAssembly m (PortBoundary.tensor Δ₁ Δ₂) result :=
  ofDiagram (left.diagram.wire right.diagram)

/-- Close two matching executable boundaries without introducing a new component. -/
@[expose] def plug (left : HandledAssembly m Δ result)
    (right : HandledAssembly m (PortBoundary.swap Δ) result) :
    HandledAssembly m PortBoundary.empty result := ofDiagram (left.diagram.plug right.diagram)

/-- A persistent bidirectional relay with no local effects and charged receive/send steps. -/
@[expose] def idWire (Γ : PortBoundary) :
    HandledAssembly m (PortBoundary.tensor (PortBoundary.swap Γ) Γ) result :=
  atom (Assembly.relay Γ) fun operation => operation.elim

/-- The operation-only theory of finite handled assemblies. -/
@[expose] def theory (m : Type → Type) (result : Type) : OpenTheory.{1} where
  Obj Δ := HandledAssembly m Δ result
  map := map
  par := par
  wire := wire
  plug := plug

/-- Interpret raw syntax while retaining each atom's actual local effect interpreter. -/
@[expose] def compile {Atom : PortBoundary → Type u}
    (expression : OpenSyntax.Raw Atom Δ)
    (interpretAtom : ∀ {Δ : PortBoundary}, Atom Δ → HandledAssembly m Δ result) :
    HandledAssembly m Δ result := expression.interpret (theory m result) interpretAtom idWire

/-- The executable residual context for the left parallel component. -/
@[expose] def parContextLeft (right : HandledAssembly m Δ₂ result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    HandledAssembly m (PortBoundary.swap Δ₁) result :=
  ofDiagram (right.diagram.parContextLeft context.diagram)

/-- The executable residual context for the right parallel component. -/
@[expose] def parContextRight (left : HandledAssembly m Δ₁ result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    HandledAssembly m (PortBoundary.swap Δ₂) result :=
  ofDiagram (left.diagram.parContextRight context.diagram)

/-- The executable residual context for the left wired component. -/
@[expose] def wireContextLeft
    (right : HandledAssembly m (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Γ)) result :=
  ofDiagram (right.diagram.wireContextLeft context.diagram)

/-- The executable residual context for the right wired component. -/
@[expose] def wireContextRight (left : HandledAssembly m (PortBoundary.tensor Δ₁ Γ) result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    HandledAssembly m (PortBoundary.swap (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) result :=
  ofDiagram (left.diagram.wireContextRight context.diagram)

variable [Monad m]

/-- Observe an actual finite token execution, with one explicitly selected environment. -/
@[expose] def tokenObservation (assembly : HandledAssembly m Δ result)
    (environment : assembly.Node) (fuel : ℕ) : m (Option (Outcome result)) :=
  assembly.diagram.tokenObservation environment fuel

/-- Observe an actual finite FIFO execution under an explicit schedule. -/
@[expose] def fifoObservation (assembly : HandledAssembly m Δ result)
    (environment : assembly.Node) (schedule : List (Activation assembly.Node)) :
    m (Option (Outcome result)) := assembly.diagram.fifoObservation environment schedule

variable [LawfulMonad m]

/-- Parallel residual contexts preserve the executed token experiment. -/
theorem tokenObservation_close_par_left (left : HandledAssembly m Δ₁ result)
    (right : HandledAssembly m Δ₂ result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : context.Node) (fuel : ℕ) :
    (left.plug (right.parContextLeft context)).tokenObservation (.inr (.inl environment)) fuel =
      ((left.par right).plug context).tokenObservation (.inr environment) fuel :=
  HandledDiagram.tokenObservation_close_par_left _ _ _ environment fuel

/-- Right parallel residual contexts preserve the executed token experiment. -/
theorem tokenObservation_close_par_right (left : HandledAssembly m Δ₁ result)
    (right : HandledAssembly m Δ₂ result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : context.Node) (fuel : ℕ) :
    (right.plug (left.parContextRight context)).tokenObservation (.inr (.inl environment)) fuel =
      ((left.par right).plug context).tokenObservation (.inr environment) fuel :=
  HandledDiagram.tokenObservation_close_par_right _ _ _ environment fuel

/-- Left wired residual contexts preserve the executed token experiment. -/
theorem tokenObservation_close_wire_left
    (left : HandledAssembly m (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledAssembly m (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : context.Node) (fuel : ℕ) :
    (left.plug (right.wireContextLeft context)).tokenObservation (.inr (.inl environment)) fuel =
      ((left.wire right).plug context).tokenObservation (.inr environment) fuel :=
  HandledDiagram.tokenObservation_close_wire_left _ _ _ environment fuel

/-- Right wired residual contexts preserve the executed token experiment. -/
theorem tokenObservation_close_wire_right
    (left : HandledAssembly m (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledAssembly m (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : context.Node) (fuel : ℕ) :
    (right.plug (left.wireContextRight context)).tokenObservation (.inr (.inl environment)) fuel =
      ((left.wire right).plug context).tokenObservation (.inr environment) fuel :=
  HandledDiagram.tokenObservation_close_wire_right _ _ _ environment fuel

/-- Left par factorization preserves FIFO observations under the transported schedule. -/
theorem fifoObservation_close_par_left (left : HandledAssembly m Δ₁ result)
    (right : HandledAssembly m Δ₂ result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : context.Node)
    (schedule : List (Activation ((left.Node ⊕ right.Node) ⊕ context.Node))) :
    (left.plug (right.parContextLeft context)).fifoObservation (.inr (.inl environment))
        (schedule.map (Activation.reindex
          (Diagram.parContextLeftEquiv left.Node right.Node context.Node))) =
      ((left.par right).plug context).fifoObservation (.inr environment) schedule :=
  HandledDiagram.fifoObservation_close_par_left _ _ _ environment schedule

/-- Right par factorization preserves FIFO observations under the transported schedule. -/
theorem fifoObservation_close_par_right (left : HandledAssembly m Δ₁ result)
    (right : HandledAssembly m Δ₂ result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : context.Node)
    (schedule : List (Activation ((left.Node ⊕ right.Node) ⊕ context.Node))) :
    (right.plug (left.parContextRight context)).fifoObservation (.inr (.inl environment))
        (schedule.map (Activation.reindex
          (Diagram.parContextRightEquiv left.Node right.Node context.Node))) =
      ((left.par right).plug context).fifoObservation (.inr environment) schedule :=
  HandledDiagram.fifoObservation_close_par_right _ _ _ environment schedule

/-- Left wire factorization preserves FIFO observations under the transported schedule. -/
theorem fifoObservation_close_wire_left
    (left : HandledAssembly m (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledAssembly m (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : context.Node)
    (schedule : List (Activation ((left.Node ⊕ right.Node) ⊕ context.Node))) :
    (left.plug (right.wireContextLeft context)).fifoObservation (.inr (.inl environment))
        (schedule.map (Activation.reindex
          (Diagram.parContextLeftEquiv left.Node right.Node context.Node))) =
      ((left.wire right).plug context).fifoObservation (.inr environment) schedule :=
  HandledDiagram.fifoObservation_close_wire_left _ _ _ environment schedule

/-- Right wire factorization preserves FIFO observations under the transported schedule. -/
theorem fifoObservation_close_wire_right
    (left : HandledAssembly m (PortBoundary.tensor Δ₁ Γ) result)
    (right : HandledAssembly m (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : HandledAssembly m (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : context.Node)
    (schedule : List (Activation ((left.Node ⊕ right.Node) ⊕ context.Node))) :
    (right.plug (left.wireContextRight context)).fifoObservation (.inr (.inl environment))
        (schedule.map (Activation.reindex
          (Diagram.parContextRightEquiv left.Node right.Node context.Node))) =
      ((left.wire right).plug context).fifoObservation (.inr environment) schedule :=
  HandledDiagram.fifoObservation_close_wire_right _ _ _ environment schedule

end HandledAssembly

end Interaction.UC.ReactiveNetwork
