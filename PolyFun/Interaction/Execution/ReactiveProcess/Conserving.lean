/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveProcess
public import PolyFun.PFunctor.Handler
public import PolyFun.Control.Monad.Support

/-!
# Conservation certificates for one reactive process

A `ProcessConserving` certificate is a conservation argument about a single reactive process. It
mentions only the process's own states, its effect handler, a charge `κ` on its states, and
credits on its own ports: `cin` for received packets and `cout` for sent ones. It has one clause per
action of the process's polynomial (`onEffect`, `onReceive`, `onSend`, `onTick`, `onYield`), and no
network, routing, mailbox, or scheduler appears in it.

Placed at the nodes of a network whose credit model gives each node these port credits, a family
of process certificates is a network certificate for both disciplines
(`ProcessConserving.toConserving` in `PolyFun.Interaction.Execution.ReactiveNetwork.Local`).
-/

public section

namespace Interaction.Execution.ReactiveProcess

open PFunctor MonadAttach

attribute [local implicit_reducible] signature Response

/-- **A process's own conservation certificate.** Each action's charge `κ` is paid by the
potential, plus the credit `cin` of a received packet; a send also pays the credit `cout` it
attaches to its packet. -/
structure ProcessConserving {effect : PFunctor.{0, 0}} {Δ : PortBoundary} {result S : Type}
    {m : Type → Type} [Monad m] [MonadAttach m] (P : Process effect Δ Unit result)
    (handler : Handler (StateT S m) effect) (κ : P.State → ℕ)
    (cin : Interface.Packet Δ.In → ℕ) (cout : Interface.Packet Δ.Out → ℕ) where
  /-- The process's potential on its own states. -/
  pot : P.State → ℕ
  /-- An effect is paid by the potential, for every answer the handler can return. -/
  onEffect : ∀ s operation (cont : effect.B operation → P.State) service answer service',
    P.view s = .inr ⟨.effect operation, cont⟩ →
    CanReturn ((handler operation).run service) (answer, service') →
    pot (cont answer) + κ s ≤ pot s
  /-- A receive is paid by the potential and the received packet's credit. -/
  onReceive : ∀ s (cont : Interface.Packet Δ.In → P.State) packet,
    P.view s = .inr ⟨.receive, cont⟩ → pot (cont packet) + κ s ≤ pot s + cin packet
  /-- A send pays its charge and the credit attached to its packet. -/
  onSend : ∀ s packet (cont : Unit → P.State),
    P.view s = .inr ⟨.send packet, cont⟩ → pot (cont ()) + κ s + cout packet ≤ pot s
  /-- A tick is paid by the potential. -/
  onTick : ∀ s (cont : Unit → P.State),
    P.view s = .inr ⟨.tick, cont⟩ → pot (cont ()) + κ s ≤ pot s
  /-- A yield is paid by the potential. -/
  onYield : ∀ s (cont : Unit → P.State),
    P.view s = .inr ⟨.yield, cont⟩ → pot (cont ()) + κ s ≤ pot s

end Interaction.Execution.ReactiveProcess
