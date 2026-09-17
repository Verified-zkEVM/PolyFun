/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.RequestNetwork
public import PolyFun.PFunctor.Handler.Instrumentation.Free
public import PolyFun.PFunctor.Bound

/-!
# Bounded adaptive clients over FIFO delivery

A serial schedule allocates three activations per permitted client query. The resulting
runtime state agrees with ordinary oracle interpretation instrumented by the existing trace
handler: it has the same verdict, private service state, and ordered response transcript.
The query bound ranges over every adaptive answer branch. Extra schedule rounds after a
client has returned are harmless, while a shorter schedule may leave that client unfinished.
-/

public section

namespace Interaction.UC.RequestNetwork

open PFunctor

variable {Client α S : Type} {p : PFunctor.{0, 0}}

/-- Allocate a complete request/service/response cycle for each query budget unit. -/
@[expose] def serialSchedule (id : Client) : ℕ → List (Activation Client)
  | 0 => []
  | n + 1 => [.client id, .deliver, .deliver] ++ serialSchedule id n

/-- The schedule charges all three administrative activations of each allocated RPC. -/
@[simp] theorem serialSchedule_length (id : Client) (n : ℕ) :
    (serialSchedule id n).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [serialSchedule, ih, Nat.mul_add]

variable [DecidableEq Client] [DecidableEq p.A]
  {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Interpret a client with the standard response-dependent trace instrumentation. -/
@[expose] def loggedRun (impl : Handler (StateT S m) p) (id : Client)
    (program : FreeM p α) (service : S) :
    m ((α × List (Interface.RoutedPacket p Client)) × S) :=
  (FreeM.liftM (impl.withTraceAppend fun a answer => [⟨id, ⟨a, answer⟩⟩]) program).run.run service

omit [DecidableEq Client] [DecidableEq p.A] [LawfulMonad m] in
/-- Returning produces no response traffic and retains the private service state. -/
@[simp] theorem loggedRun_pure (impl : Handler (StateT S m) p) (id : Client)
    (value : α) (service : S) :
    loggedRun impl id (pure value) service = pure ((value, []), service) := by
  rfl

omit [DecidableEq Client] [DecidableEq p.A] in
/-- Logged oracle interpretation prepends the current response to the continuation's traffic. -/
theorem loggedRun_liftBind (impl : Handler (StateT S m) p) (id : Client)
    (a : p.A) (next : p.B a → FreeM p α) (service : S) :
    loggedRun impl id (.liftBind a next) service = (do
      let (answer, service') ← (impl a).run service
      let (out, service'') ← loggedRun impl id (next answer) service'
      pure ((out.1, ⟨id, ⟨a, answer⟩⟩ :: out.2), service'')) := by
  change ((impl.withTraceAppend _ a >>= fun answer =>
    FreeM.liftM (impl.withTraceAppend _) (next answer)).run).run service = _
  simp [loggedRun]

/-- A returned client and an empty queue remain fixed through all further serial rounds. -/
theorem run_serialSchedule_return (impl : Handler (StateT S m) p) (id : Client)
    (n : ℕ) (state : State Client p α S) (value : α)
    (hclient : state.clients id = .ready (pure value)) (hqueue : state.queue = []) :
    run impl (serialSchedule id n) state = pure state := by
  induction n with
  | zero => rfl
  | succ n ih => simp [serialSchedule, run, step, emit_ready_pure hclient, deliver, hqueue, ih]

/-- A bounded adaptive client completes within its allocated FIFO schedule. The full returned
state agrees with the traced oracle game, including the number of fresh tickets actually used. -/
theorem run_serialSchedule (impl : Handler (StateT S m) p) (id : Client)
    (n : ℕ) (program : FreeM p α) (hbound : FreeM.IsTotalRollBound program n)
    (state : State Client p α S) (hclient : state.clients id = .ready program)
    (hqueue : state.queue = []) :
    run impl (serialSchedule id n) state = (do
      let (out, service) ← loggedRun impl id program state.service
      pure { state with
        clients := Function.update state.clients id (.ready (pure out.1))
        service
        queue := []
        nextTicket := state.nextTicket + out.2.length
        transcript := state.transcript ++ out.2 }) := by
  induction program generalizing n state with
  | pure value =>
      rw [run_serialSchedule_return impl id n state value hclient hqueue]
      simp only [loggedRun_pure, pure_bind, List.length_nil, Nat.add_zero, List.append_nil]
      congr 1
      rw [← hclient, Function.update_eq_self]
      cases state
      simp_all
  | lift_bind a next ih =>
      rw [FreeM.isTotalRollBound_lift_bind_iff] at hbound
      cases n with
      | zero => exact False.elim (Nat.lt_irrefl 0 hbound.1)
      | succ n =>
          rw [serialSchedule, run_append, run_roundtrip impl id state a next hclient hqueue]
          change _ = (do
            let out ← loggedRun impl id (.liftBind a next) state.service
            pure { state with
              clients := Function.update state.clients id (.ready (pure out.1.1))
              service := out.2
              queue := []
              nextTicket := state.nextTicket + out.1.2.length
              transcript := state.transcript ++ out.1.2 })
          rw [loggedRun_liftBind]
          simp only [bind_assoc, pure_bind]
          congr 1
          funext answer
          rcases answer with ⟨answer, service⟩
          rw [ih answer n (by simpa using hbound.2 answer) _ (by simp) rfl]
          simp [List.length_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Function.update_idem]

/-- Start a single adaptive client with no pending traffic or prior transcript. -/
@[expose] def initial (program : FreeM p α) (service : S) : State Unit p α S :=
  ⟨fun _ => .ready program, service, [], 0, []⟩

/-- Read a returned result without treating fuel exhaustion as successful termination. -/
@[expose] def result (id : Client) (state : State Client p α S) : Option α :=
  match state.clients id with
  | .ready (.pure value) => some value
  | _ => none

/-- Observe a bounded run's optional result, response transcript, and private service state. -/
@[expose] def serialObservation (impl : Handler (StateT S m) p)
    (n : ℕ) (program : FreeM p α) (service : S) :
    m ((Option α × List (Interface.RoutedPacket p Unit)) × S) :=
  (fun state => ((result () state, state.transcript), state.service)) <$>
    run impl (serialSchedule () n) (initial program service)

omit [DecidableEq Client] in
/-- The network's complete transcript and result coincide with traced oracle interpretation. -/
theorem serialObservation_eq_loggedRun (impl : Handler (StateT S m) p)
    (n : ℕ) (program : FreeM p α) (hbound : FreeM.IsTotalRollBound program n)
    (service : S) :
    serialObservation impl n program service =
      (fun out => ((some out.1.1, out.1.2), out.2)) <$> loggedRun impl () program service := by
  rw [serialObservation, run_serialSchedule impl () n program hbound _ rfl rfl]
  simp [initial, result, bind_pure_comp, ← FreeM.pure_eq_pure]

omit [DecidableEq Client] [DecidableEq p.A] in
/-- Erasing the standard trace instrumentation recovers the original stateful oracle game. -/
theorem map_loggedRun (impl : Handler (StateT S m) p)
    (id : Client) (program : FreeM p α) (service : S) :
    (fun out => (out.1.1, out.2)) <$> loggedRun impl id program service =
      (FreeM.liftM impl program).run service := by
  have h := congrArg (fun action : StateT S m α => action.run service)
    (Handler.fst_map_run_liftM_withTraceAppend impl
      (fun a answer => ([⟨id, ⟨a, answer⟩⟩] :
        List (Interface.RoutedPacket p Client))) program)
  simpa [loggedRun] using h

omit [DecidableEq Client] in
/-- The result and private state of a completed FIFO run are those of the original oracle game. -/
theorem map_serialObservation (impl : Handler (StateT S m) p)
    (n : ℕ) (program : FreeM p α) (hbound : FreeM.IsTotalRollBound program n)
    (service : S) :
    (fun out => (out.1.1, out.2)) <$> serialObservation impl n program service =
      (fun out => (some out.1, out.2)) <$> (FreeM.liftM impl program).run service := by
  rw [serialObservation_eq_loggedRun impl n program hbound service,
    ← map_loggedRun impl () program service]
  simp only [Functor.map_map]

end Interaction.UC.RequestNetwork
