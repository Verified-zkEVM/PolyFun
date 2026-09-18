/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork.Assembly
public import PolyFun.Interaction.Execution.ReactiveNetwork.Serial

/-!
# Executing raw reactive assemblies

The same communicating machines run after raw-syntax compilation, with actual typed routing.
The regressions preserve unfinished prefixes and distinguish a direct connection from a
charged identity relay. Component identities determine control and are selected explicitly.
-/

public section

namespace Interaction.Execution.ReactiveNetwork.AssemblyTests

open Interaction.Open PFunctor ReactiveProcess DynSystem OpenSyntax

@[expose] def port : Interface := ⟨Unit, fun _ => Bool⟩
@[expose] def boundary : PortBoundary := ⟨port, port⟩

@[expose] def environment (value : Bool) : Assembly boundary Bool :=
  Assembly.atom (DynComputation.ofFreeM fun _ =>
    (FreeM.liftBind (.send ⟨(), value⟩) fun _ =>
      .liftBind .receive fun packet => .pure (.returned packet.2) :
        FreeM (signature Assembly.relayEffect boundary) (Outcome Bool)))

@[expose] def echo : Assembly (PortBoundary.swap boundary) Bool :=
  Assembly.atom (DynComputation.ofFreeM fun _ =>
    (FreeM.liftBind .receive fun packet =>
      .liftBind (.send packet) fun _ => .pure (.returned packet.2) :
        FreeM (signature Assembly.relayEffect (PortBoundary.swap boundary)) (Outcome Bool)))

@[expose] def expression (value : Bool) :
    Raw (fun Δ => Assembly Δ Bool) PortBoundary.empty :=
  Raw.plug (.atom (environment value)) (.atom echo)

@[expose] def compiled (value : Bool) : Assembly PortBoundary.empty Bool :=
  Assembly.compile (expression value) fun atom => atom

/-- Raw compilation uses the same routing operations as direct assembly. -/
example (value : Bool) : compiled value = (environment value).plug echo := rfl

@[expose] def network (value : Bool) := (compiled value).network (.inl ())

@[expose] def impl (value : Bool) :
    (node : (compiled value).Node) → Handler (StateT Unit Id) ((network value).effect node) := by
  intro node
  rcases node with node | node <;> exact fun operation => operation.elim

/-- Both directions carry the environment's actual Boolean through the compiled routes. -/
example (value : Bool) :
    outcome (.inl ()) (runToken (m := Id) (impl value) 4 (initial (network value) ())) =
      some (.returned value) := by
  cases value <;> rfl

/-- A strict prefix still has an unfinished environment after raw compilation. -/
example (value : Bool) :
    outcome (.inl ()) (runToken (m := Id) (impl value) 3 (initial (network value) ())) = none := by
  cases value <;> rfl

/-- Serial FIFO pays eight activations for this four-step token exchange. -/
example (value : Bool) :
    (runSerial (m := Id) (impl value) 4 (initial (network value) ())).elapsed = 8 ∧
      outcome (.inl ()) (runSerial (m := Id) (impl value) 4 (initial (network value) ())) =
        some (.returned value) := by
  cases value <;> exact ⟨rfl, rfl⟩

/-- Giving initial control to the waiting receiver prevents the exchange from starting. -/
example (value : Bool) :
    outcome (.inl ()) (runToken (m := Id) (impl value) 4
      { initial (network value) () with focus := .inr () }) = none := by
  cases value <;> rfl

@[expose] def relayedEcho : Assembly (PortBoundary.swap boundary) Bool :=
  ((Assembly.idWire boundary).wire
    (echo.map (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap boundary)).symm.toHom)).map
      (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap boundary)).toHom

@[expose] def relayed (value : Bool) : Assembly PortBoundary.empty Bool :=
  (environment value).plug relayedEcho

@[expose] def relayNetwork (value : Bool) := (relayed value).network (.inl ())

@[expose] def relayImpl (value : Bool) :
    (node : (relayed value).Node) →
      Handler (StateT Unit Id) ((relayNetwork value).effect node) := by
  intro node
  rcases node with node | node | node <;> exact fun operation => operation.elim

/-- The identity relay correctly forwards in both directions when its work is funded. -/
example (value : Bool) :
    outcome (.inl ()) (runToken (m := Id) (relayImpl value) 8 (initial (relayNetwork value) ())) =
      some (.returned value) := by
  cases value <;> rfl

/-- Eliminating a relay without transporting the budget changes the actual observation. -/
theorem relay_changes_bounded_observation (value : Bool) :
    outcome (.inl ()) (runToken (m := Id) (relayImpl value) 4 (initial (relayNetwork value) ())) ≠
      outcome (.inl ()) (runToken (m := Id) (impl value) 4 (initial (network value) ())) := by
  cases value <;> intro h <;> cases h

end Interaction.Execution.ReactiveNetwork.AssemblyTests
