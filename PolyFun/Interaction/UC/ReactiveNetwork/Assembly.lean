/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveNetwork
public import PolyFun.Interaction.UC.OpenSyntax.Raw
public import Mathlib.Data.Fintype.Sum

/-!
# Finite reactive interpretation of raw open syntax

An assembly bundles the finite identity type of an open routing diagram. Raw syntax compiles
by its existing universal interpretation into map, parallel, and wiring operations. Identity
wires are actual forwarding machines: they receive, then send, and repeat. Their local and
delivery steps are charged by the selected runtime, so no compact-closed equations are asserted
for timed execution.

Compilation retains the concrete polynomial interfaces and private machine state of every atom.
The caller selects the global environment from the assembled nodes when creating a network.
-/

public section

universe u

namespace Interaction.UC.ReactiveNetwork

open PFunctor ReactiveProcess DynSystem

/-- A finite open routing diagram with explicit component identities. -/
structure Assembly (boundary : PortBoundary) (result : Type) where
  /-- Stable identities of the assembled components. -/
  Node : Type
  /-- Enumeration of the static components. -/
  [fintypeNode : Fintype Node]
  /-- Decidable identities for mailbox and private-state updates. -/
  [decidableEqNode : DecidableEq Node]
  /-- The actual component machines and routes. -/
  diagram : Diagram Node boundary result

attribute [instance] Assembly.fintypeNode Assembly.decidableEqNode

namespace Assembly

variable {result : Type} {Δ Δ₁ Δ₂ Γ : PortBoundary}

/-- Bundle a finite routing diagram for open composition. -/
@[expose] def ofDiagram {Node : Type} [Fintype Node] [DecidableEq Node]
    (diagram : Diagram Node Δ result) : Assembly Δ result := ⟨Node, diagram⟩

/-- A single initialized process, with its polynomial effect interface unchanged. -/
@[expose] def atom {effect : PFunctor.{0, 0}} (process : Process effect Δ Unit result) :
    Assembly Δ result := ofDiagram (Diagram.atom process)

/-- Adapt external packet traffic without changing component identities. -/
@[expose] def map (f : PortBoundary.Hom Δ₁ Δ₂) (assembly : Assembly Δ₁ result) :
    Assembly Δ₂ result := ofDiagram (assembly.diagram.map f)

/-- Assemble independent fragments on disjoint identity types. -/
@[expose] def par (left : Assembly Δ₁ result) (right : Assembly Δ₂ result) :
    Assembly (PortBoundary.tensor Δ₁ Δ₂) result := ofDiagram (left.diagram.par right.diagram)

/-- Connect shared ports while retaining the two fragments' component machines. -/
@[expose] def wire (left : Assembly (PortBoundary.tensor Δ₁ Γ) result)
    (right : Assembly (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result) :
    Assembly (PortBoundary.tensor Δ₁ Δ₂) result := ofDiagram (left.diagram.wire right.diagram)

/-- Close matching external interfaces, retaining all component identities. -/
@[expose] def plug (left : Assembly Δ result) (right : Assembly (PortBoundary.swap Δ) result) :
    Assembly PortBoundary.empty result := ofDiagram (left.diagram.plug right.diagram)

/-- A forwarding component has no effect operations of its own. -/
@[expose] def relayEffect : PFunctor.{0, 0} := ⟨Empty, Empty.elim⟩

/-- Cross an identity wire in either direction. -/
@[expose] def relayPacket (Γ : PortBoundary) :
    Interface.Packet (PortBoundary.tensor (PortBoundary.swap Γ) Γ).In →
      Interface.Packet (PortBoundary.tensor (PortBoundary.swap Γ) Γ).Out
  | ⟨.inl port, message⟩ => ⟨.inr port, message⟩
  | ⟨.inr port, message⟩ => ⟨.inl port, message⟩

/-- A persistent forwarding machine, alternating one receive and one send. -/
@[expose] def relay (Γ : PortBoundary) :
    Process relayEffect (PortBoundary.tensor (PortBoundary.swap Γ) Γ) Unit result :=
  DynComputation.ofStep (S := Option (Interface.Packet
      (PortBoundary.tensor (PortBoundary.swap Γ) Γ).Out))
    (fun
      | none => .inr ⟨.receive, fun packet => some (relayPacket Γ packet)⟩
      | some packet => .inr ⟨.send packet, fun _ => none⟩)
    (fun _ => none)

/-- The operational identity wire is a forwarding component with explicitly charged steps. -/
@[expose] def idWire (Γ : PortBoundary) :
    Assembly (PortBoundary.tensor (PortBoundary.swap Γ) Γ) result := atom (relay Γ)

/-- The operation-only open theory of finite routing assemblies. -/
@[expose] def theory (result : Type) : OpenTheory.{1} where
  Obj Δ := Assembly Δ result
  map := map
  par := par
  wire := wire
  plug := plug

/-- Compile raw syntax by the existing open-theory interpretation. No syntax quotient or
timed coherence law is assumed by this operation. -/
@[expose] def compile {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (expression : OpenSyntax.Raw Atom Δ)
    (interpretAtom : ∀ {Δ : PortBoundary}, Atom Δ → Assembly Δ result) : Assembly Δ result :=
  expression.interpret (theory result) interpretAtom idWire

/-- Select the global environment after compiling and wiring all open fragments. -/
@[expose] def network (assembly : Assembly Δ result) (environment : assembly.Node) :
    Network assembly.Node Δ result := assembly.diagram.withEnvironment environment

end Assembly

end Interaction.UC.ReactiveNetwork
