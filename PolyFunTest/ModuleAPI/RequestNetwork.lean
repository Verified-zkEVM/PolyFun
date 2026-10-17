/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.RequestNetwork

/-!
# Ordinary-import canaries for request networks

Two clients start ready with no traffic. One complete RPC takes a client activation, a service
delivery and a response delivery; afterwards only the served client has returned, and the
service state records the answered request. The result observation keeps the remaining state.
-/

@[expose] public section

namespace PolyFunTest.ModuleAPI.RequestNetwork

open PFunctor Interaction.Execution

/-- One query whose answer is a natural number. -/
abbrev Counter : PFunctor.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- Ask once and return the answer. -/
def ask : FreeM Counter Nat := .liftBind () fun n => .pure n

/-- Answer with the current counter and increment it. -/
def counter : Handler (StateT Nat Id) Counter := fun _ n => (n, n + 1)

/-- Two ready clients sharing a service whose counter starts at `5`. -/
def start : RequestNetwork.State Bool Counter Nat Nat :=
  RequestNetwork.State.initial (fun _ => ask) 5

example : start.queue = [] ∧ start.nextTicket = 0 ∧ start.transcript = [] := ⟨rfl, rfl, rfl⟩

example (id : Bool) : start.clients id = .ready ask := rfl

/-- The state after one complete RPC from the `true` client. -/
def served : RequestNetwork.State Bool Counter Nat Nat :=
  Id.run (RequestNetwork.run counter [.client true, .deliver, .deliver] start)

example : (served.clients true).result = some 5 := rfl

example : (served.clients false).result = none := rfl

example : served.service = 6 ∧ served.queue = [] ∧ served.nextTicket = 1 := ⟨rfl, rfl, rfl⟩

example {p : PFunctor.{0, 0}} {α : Type} (value : α) :
    RequestNetwork.ClientState.result (.ready (pure value : FreeM p α)) = some value := by
  simp

example {p : PFunctor.{0, 0}} {α : Type} (ticket : Nat) (query : p.A)
    (next : p.B query → FreeM p α) :
    RequestNetwork.ClientState.result (.waiting ticket query next) = none := by
  simp

end PolyFunTest.ModuleAPI.RequestNetwork
