/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Machine.Defs
public import PolyFun.PFunctor.Dynamical.DynComputation.Observe

/-!
# Decomposing dispatcher execution prefixes

Every dispatcher prefix has a computable view consisting of completed calls and
an optional unfinished call. Each call retains its actual service execution trace;
completed answers reconstruct a typed caller trace. Reassembling the view gives
exactly the original prefix, including entry and return administration. No
termination hypothesis or probabilistic interpretation is needed.
-/

public section

universe u v

namespace PFunctor.MachineHandler

open DynSystem DynSystem.DynComputation

variable {P Q : PFunctor.{u, u}} {S A B : Type u}

variable (h : MachineHandler P Q S) (caller : DynComputation P A B)

/-- A service prefix embeds in the dispatcher while retaining its suspended caller. -/
def liftHandlerTrace {a : P.A} (pending : caller.Pending a)
    {start finish : (h a).State} (trace : (h a).ExecutionTrace start finish) :
    (h.dispatch caller).ExecutionTrace (.handler a start pending) (.handler a finish pending) :=
  match trace with
  | .nil _ => .nil _
  | .query (position := q) (next := next) hv answer tail =>
      .query (machine := h.dispatch caller) (position := Sum.inl q)
        (next := fun b => Phase.handler a (next b) pending)
        (by rw [view_dispatch, dispatchStep, hv]) answer (liftHandlerTrace pending tail)

/-- The dispatcher embedding preserves concatenation of service prefixes. -/
@[simp] theorem liftHandlerTrace_append {a : P.A} (pending : caller.Pending a)
    {start middle finish : (h a).State}
    (left : (h a).ExecutionTrace start middle) (right : (h a).ExecutionTrace middle finish) :
    h.liftHandlerTrace caller pending (left.append right) =
      (h.liftHandlerTrace caller pending left).append
        (h.liftHandlerTrace caller pending right) := by
  induction left with
  | nil => rfl
  | query hv answer tail ih => simp only [ExecutionTrace.append, liftHandlerTrace, ih]

/-- Embedding a service prefix adds no administrative events. -/
theorem length_liftHandlerTrace {a : P.A} (pending : caller.Pending a)
    {start finish : (h a).State} (trace : (h a).ExecutionTrace start finish) :
    (h.liftHandlerTrace caller pending trace).length = trace.length := by
  induction trace with
  | nil => rfl
  | query hv answer tail ih => simp only [liftHandlerTrace, ExecutionTrace.length_query, ih]

variable {W : Type v} [Monoid W]

/-- A service trace keeps exactly its state-aware observations under dispatcher embedding. -/
theorem accumulate_liftHandlerTrace
    (observe : Phase h caller → (q : (Q + y.{u, u}).A) → (Q + y.{u, u}).B q → W)
    {a : P.A} (pending : caller.Pending a) {start finish : (h a).State}
    (trace : (h a).ExecutionTrace start finish) :
    (h.liftHandlerTrace caller pending trace).accumulate
        ((h.dispatch caller).queryEventMap observe) =
      trace.accumulate ((h a).queryEventMap
        (fun state q answer => observe (.handler a state pending) (.inl q) answer)) := by
  induction trace with
  | nil => simp only [liftHandlerTrace, ExecutionTrace.accumulate_nil]
  | query hv answer tail ih =>
      simp only [liftHandlerTrace, ExecutionTrace.accumulate_query, queryEventMap_atOut, ih]


variable {h caller}

/-- Completed calls retain the caller states, exact service traces, and returned
answer/state equations. This is a view of execution, with no new runner. -/
inductive CallHistory (h : MachineHandler P Q S) (caller : DynComputation P A B)
    (start : caller.State) (initial : S) : caller.State → S → Type u where
  /-- No call has completed. -/
  | nil : CallHistory h caller start initial start initial
  /-- Extend the history by one completed service call. -/
  | call {service : S} {a : P.A} {finish : (h a).State} {answer : P.B a} {final : S}
      (pending : caller.Pending a)
      (past : CallHistory h caller start initial pending.val service)
      (body : (h a).ExecutionTrace ((h a).init service) finish)
      (returned : (h a).view finish = .inl (answer, final)) :
      CallHistory h caller start initial (pending.resume answer) final

/-- A dispatcher prefix consists of completed calls and, in a handler phase,
the exact unfinished call. Its index retains the actual residual phase. -/
inductive DispatchPrefix (h : MachineHandler P Q S) (caller : DynComputation P A B)
    (start : caller.State) (initial : S) : Phase h caller → Type u where
  /-- The caller is ready to expose its next query or result. -/
  | caller {state : caller.State} {service : S}
      (past : CallHistory h caller start initial state service) :
      DispatchPrefix h caller start initial (.caller state service)
  /-- A service call has entered and may have made any finite number of queries. -/
  | handler {a : P.A} {state : (h a).State} {pending : caller.Pending a} {service : S}
      (past : CallHistory h caller start initial pending.val service)
      (body : (h a).ExecutionTrace ((h a).init service) state) :
      DispatchPrefix h caller start initial (.handler a state pending)

namespace CallHistory

variable {h : MachineHandler P Q S} {caller : DynComputation P A B}
  {start : caller.State} {initial : S}

/-- Reconstruct the exact dispatcher trace, including call entry and return. -/
def toTrace {state : caller.State} {service : S}
    (past : CallHistory h caller start initial state service) :
    (h.dispatch caller).ExecutionTrace (.caller start initial) (.caller state service) :=
  match past with
  | .nil => .nil _
  | CallHistory.call (service := service) (a := a) pending past body returned =>
      past.toTrace.append (.query (machine := h.dispatch caller) (position := Sum.inr PUnit.unit)
        (next := fun _ => Phase.handler a ((h a).init service) pending)
        (by rw [view_dispatch, dispatchStep_caller_query h caller pending.view_resume]; rfl)
        PUnit.unit ((h.liftHandlerTrace caller pending body).append
          (.query (machine := h.dispatch caller) (position := Sum.inr PUnit.unit)
            (by rw [view_dispatch, dispatchStep, returned]) PUnit.unit (.nil _))))

/-- Completed service answers induce a typed execution prefix of the caller. -/
def callerTrace {state : caller.State} {service : S}
    (past : CallHistory h caller start initial state service) :
    caller.ExecutionTrace start state :=
  match past with
  | .nil => .nil _
  | CallHistory.call pending past _ _ =>
      past.callerTrace.append (.query pending.view_resume _ (.nil _))

/-- Primitive transitions performed inside completed calls. -/
def primitiveSteps {state : caller.State} {service : S}
    (past : CallHistory h caller start initial state service) : Nat :=
  match past with
  | .nil => 0
  | CallHistory.call _ past body _ => past.primitiveSteps + body.length

/-- Every completed call adds its primitive work and two administrative transitions. -/
theorem length_toTrace {state : caller.State} {service : S}
    (past : CallHistory h caller start initial state service) :
    past.toTrace.length = 2 * past.callerTrace.length + past.primitiveSteps := by
  induction past with
  | nil => rfl
  | call pending past body returned ih =>
      simp only [toTrace, callerTrace, primitiveSteps, ExecutionTrace.length_append,
        ExecutionTrace.length_query, ExecutionTrace.length_nil]
      rw [length_liftHandlerTrace, ih]
      omega

/-- The observations of a completed call include entry, its exact body, and return, in order. -/
theorem accumulate_toTrace_call
    (observe : Phase h caller → (q : (Q + y.{u, u}).A) → (Q + y.{u, u}).B q → W)
    {a : P.A} {service : S} {finish : (h a).State} {answer : P.B a} {final : S}
    (pending : caller.Pending a)
    (past : CallHistory h caller start initial pending.val service)
    (body : (h a).ExecutionTrace ((h a).init service) finish)
    (returned : (h a).view finish = .inl (answer, final)) :
    (call pending past body returned).toTrace.accumulate
        ((h.dispatch caller).queryEventMap observe) =
      past.toTrace.accumulate ((h.dispatch caller).queryEventMap observe) *
        (observe (.caller pending.val service) (.inr PUnit.unit) PUnit.unit *
          (body.accumulate ((h a).queryEventMap
            (fun state q answer => observe (.handler a state pending) (.inl q) answer)) *
              observe (.handler a finish pending) (.inr PUnit.unit) PUnit.unit)) := by
  simp only [toTrace, ExecutionTrace.accumulate_append, ExecutionTrace.accumulate_query,
    queryEventMap_atOut, ExecutionTrace.accumulate_nil, mul_one, accumulate_liftHandlerTrace]

end CallHistory

namespace DispatchPrefix

variable {h : MachineHandler P Q S} {caller : DynComputation P A B}
  {start : caller.State} {initial : S}

/-- Reconstruct the exact dispatcher trace, retaining unfinished service work. -/
def toTrace {phase : Phase h caller}
    (prefixView : DispatchPrefix h caller start initial phase) :
    (h.dispatch caller).ExecutionTrace (.caller start initial) phase :=
  match prefixView with
  | .caller past => past.toTrace
  | .handler (a := a) (service := service) (pending := pending) past body =>
      past.toTrace.append (.query (machine := h.dispatch caller) (position := Sum.inr PUnit.unit)
        (next := fun _ => Phase.handler a ((h a).init service) pending)
        (by rw [view_dispatch, dispatchStep_caller_query h caller pending.view_resume]; rfl)
        PUnit.unit (h.liftHandlerTrace caller pending body))

/-- A prefix between calls has exactly the cost of its completed-call history. -/
theorem length_toTrace_caller {state : caller.State} {service : S}
    (past : CallHistory h caller start initial state service) :
    (DispatchPrefix.caller past).toTrace.length =
      2 * past.callerTrace.length + past.primitiveSteps :=
  past.length_toTrace

/-- An unfinished call contributes its entry tick and all primitive work performed so far. -/
theorem length_toTrace_handler {a : P.A} {state : (h a).State} {service : S}
    {pending : caller.Pending a}
    (past : CallHistory h caller start initial pending.val service)
    (body : (h a).ExecutionTrace ((h a).init service) state) :
    (DispatchPrefix.handler past body).toTrace.length =
      2 * past.callerTrace.length + past.primitiveSteps + body.length + 1 := by
  simp only [toTrace, ExecutionTrace.length_append, ExecutionTrace.length_query,
    length_liftHandlerTrace, CallHistory.length_toTrace, Nat.add_assoc]

/-- Unfinished prefixes retain entry and body observations, without inventing a return event. -/
theorem accumulate_toTrace_handler
    (observe : Phase h caller → (q : (Q + y.{u, u}).A) → (Q + y.{u, u}).B q → W)
    {a : P.A} {state : (h a).State} {service : S} {pending : caller.Pending a}
    (past : CallHistory h caller start initial pending.val service)
    (body : (h a).ExecutionTrace ((h a).init service) state) :
    (DispatchPrefix.handler past body).toTrace.accumulate
        ((h.dispatch caller).queryEventMap observe) =
      past.toTrace.accumulate ((h.dispatch caller).queryEventMap observe) *
        (observe (.caller pending.val service) (.inr PUnit.unit) PUnit.unit *
          body.accumulate ((h a).queryEventMap
            (fun state q answer => observe (.handler a state pending) (.inl q) answer))) := by
  simp only [toTrace, ExecutionTrace.accumulate_append, ExecutionTrace.accumulate_query,
    queryEventMap_atOut, accumulate_liftHandlerTrace]

/-- Extend a decomposition by one enabled dispatcher transition, with exact reconstruction. -/
def extend {phase : Phase h caller} {position : (Q + y.{u, u}).A}
    {next : (Q + y.{u, u}).B position → Phase h caller}
    (view_eq : (h.dispatch caller).view phase = .inr ⟨position, next⟩)
    (answer : (Q + y.{u, u}).B position)
    (prefixView : DispatchPrefix h caller start initial phase) :
    {out : DispatchPrefix h caller start initial (next answer) //
      out.toTrace = prefixView.toTrace.append (.query view_eq answer (.nil _))} := by
  cases prefixView with
  | @caller state service past =>
      rcases hv : caller.view state with value | ⟨a, continuation⟩
      · rw [view_dispatch, dispatchStep_caller_pure h caller hv] at view_eq
        cases view_eq
      · have hd := view_eq
        rw [view_dispatch, dispatchStep_caller_query h caller hv] at hd
        cases Sum.inr.inj hd
        cases answer
        refine ⟨.handler past (.nil _), ?_⟩
        simp only [toTrace, liftHandlerTrace]
        rfl
  | @handler a state pending service past body =>
      rcases hv : (h a).view state with value | ⟨q, continuation⟩
      · have hd := view_eq
        rw [view_dispatch, dispatchStep, hv] at hd
        cases Sum.inr.inj hd
        cases answer
        refine ⟨.caller (.call pending past body hv), ?_⟩
        simp only [toTrace, CallHistory.toTrace, ExecutionTrace.append_assoc,
          ExecutionTrace.append]
      · have hd := view_eq
        rw [view_dispatch, dispatchStep, hv] at hd
        cases Sum.inr.inj hd
        refine ⟨.handler past (body.append (.query hv answer (.nil _))), ?_⟩
        simp only [toTrace, liftHandlerTrace_append, liftHandlerTrace,
          ExecutionTrace.append_assoc, ExecutionTrace.append]

/-- Extend a decomposition by an arbitrary adjacent prefix without replaying earlier work. -/
def append {phase finish : Phase h caller}
    (prefixView : DispatchPrefix h caller start initial phase)
    (trace : (h.dispatch caller).ExecutionTrace phase finish) :
    {out : DispatchPrefix h caller start initial finish //
      out.toTrace = prefixView.toTrace.append trace} :=
  match trace with
  | .nil _ => ⟨prefixView, (ExecutionTrace.append_nil prefixView.toTrace).symm⟩
  | .query hv answer tail =>
      let first := extend hv answer prefixView
      let rest := append first.val tail
      ⟨rest.val, by rw [rest.property, first.property,
        ExecutionTrace.append_assoc, ExecutionTrace.append, ExecutionTrace.append]⟩

/-- Compute the call decomposition of any dispatcher prefix starting in a caller phase. -/
def decompose {finish : Phase h caller}
    (trace : (h.dispatch caller).ExecutionTrace (.caller start initial) finish) :
    DispatchPrefix h caller start initial finish :=
  (append (.caller .nil) trace).val

/-- Decomposition preserves the complete typed execution prefix. -/
theorem toTrace_decompose {finish : Phase h caller}
    (trace : (h.dispatch caller).ExecutionTrace (.caller start initial) finish) :
    (decompose trace).toTrace = trace := by
  exact (append (.caller .nil) trace).property

end DispatchPrefix
end PFunctor.MachineHandler
