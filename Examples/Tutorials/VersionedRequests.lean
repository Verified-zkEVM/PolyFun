/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.RequestNetwork

/-! # Two clients and a versioned cell

Both clients read version zero before either tries to replace the value. The explicit schedule
then delivers their conditional writes in order: one succeeds and the other is stale. Queue
delivery and client activation are separate. Pausing a schedule retains tickets and in-flight
traffic; these finite checks assert neither fairness nor eventual delivery.
-/

@[expose] public section

namespace PolyFunExamples.VersionedRequests

open PFunctor Interaction.Execution.RequestNetwork

/-- The service state is a value and a monotonically increasing version. -/
structure Cell where
  /-- Every accepted replacement increments this counter. -/
  version : Nat
  /-- Opaque application data. -/
  value : String
  deriving DecidableEq, Repr

/-- Replies differ: a read returns a snapshot; a conditional write returns acceptance. -/
inductive Request where
  | read
  | replace (expected : Nat) (value : String)
  deriving DecidableEq

/-- A dependent polynomial request interface. -/
def Store : PFunctor where
  A := Request
  B
    | .read => Cell
    | .replace .. => Bool

instance : DecidableEq Store.A := inferInstanceAs (DecidableEq Request)

/-- Independently specified service semantics, with rejection leaving the cell unchanged. -/
def transition (cell : Cell) : (request : Request) → Store.B request × Cell
  | .read => (cell, cell)
  | .replace expected value =>
    if cell.version = expected then (true, ⟨cell.version + 1, value⟩) else (false, cell)

/-- StateT is just one interpretation of the pure service transition. -/
def service : Handler (StateM Cell) Store := fun request cell => transition cell request

/-- Each client obtains its own version, then attempts one update. -/
def client (text : String) : FreeM Store Bool := do
  let snapshot ← FreeM.lift (P := Store) .read
  FreeM.lift (P := Store) (.replace snapshot.version text)

/-- Client identities remain separate from the service's fresh request tickets. -/
def initial : State Bool Store Bool Cell :=
  State.initial (fun id => client (if id then "second" else "first")) ⟨0, "original"⟩

/-- Both clients issue one request, then all requests and responses are delivered. -/
def round : List (Activation Bool) :=
  [.client false, .client true, .deliver, .deliver, .deliver, .deliver]

/-- A complete, intentionally chosen interleaving, not an implicit scheduler. -/
def finished : State Bool Store Bool Cell := (run service (round ++ round) initial).run

example : finished.service = ⟨1, "first"⟩ := rfl
example : (finished.clients false).result = some true := rfl
example : (finished.clients true).result = some false := rfl
example : finished.queue.length = 0 ∧ finished.nextTicket = 4 ∧
    finished.transcript.length = 4 := by decide

/-- The first cut retains both outstanding requests and the allocated ticket counter. -/
def pending : State Bool Store Bool Cell :=
  (run service [.client false, .client true] initial).run

example : pending.queue.length = 2 ∧ pending.nextTicket = 2 := by decide
example : (pending.clients false).result = none := rfl

end PolyFunExamples.VersionedRequests
