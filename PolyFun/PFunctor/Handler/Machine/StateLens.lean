/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Machine.Behavior
public import PolyFun.PFunctor.Dynamical.DynComputation.Trace
public import PolyFun.PFunctor.Dynamical.DynComputation.WrapState

/-!
# One-query stateful lenses as machine handlers

The general machine dispatcher and the direct `DynComputation.wrapState` fast
path preserve the same primitive behavior and final shared state. Their weak
bisimulation removes the dispatcher's entry and return administration. The
direct wrapper retains its own one-query clock and quantitative certificates.
-/

public section

universe u

namespace PFunctor.StatefulLens

open DynSystem ITree

variable {P Q : PFunctor.{u, u}} {S A B : Type u}

/-- Dispatching the one-query lens handler and wrapping the caller directly have the
same weak behavior, including shared final state and divergence. Dispatcher entry
and return steps are silent; this theorem does not equate their clocks. -/
theorem dispatch_weakBisim_wrapState (L : StatefulLens P Q S) (caller : DynComputation P A B)
    (input : A) (service : S) :
    WeakBisim (ITree.ofResumptionWithTau
      (((MachineHandler.ofFreeM L.toStateful).dispatch caller).denote (input, service)))
      (((caller.wrapState L).denote (input, service)).toITree) := by
  let h := MachineHandler.ofFreeM L.toStateful
  let R := fun x y => ∃ (state : caller.State) (s : S),
    TauSteps x (h.behavior caller (.caller state s)) ∧
      y = MachineHandler.callerTree (caller.wrapState L) (state, s)
  apply WeakBisim.coinduct R ?_ ⟨caller.init input, service, .refl _, rfl⟩
  rintro x y ⟨state, s, hx, rfl⟩
  rcases hv : caller.view state with b | ⟨a, next⟩
  · rw [h.behavior_caller_pure caller hv s] at hx
    rw [MachineHandler.callerTree_pure _ (caller.view_wrapState_of_return L hv)]
    exact ⟨_, _, hx, .refl _, .pure _ (shape'_pure _) (shape'_pure _)⟩
  · have hquery : (h a).view ((h a).init s) =
        .inr ⟨L.pos (a, s), fun answer => FreeM.pure
          (L.answer (a, s) answer, L.update (a, s) answer)⟩ := by
      exact DynComputation.view_ofFreeM_liftBind _ _ _
    rw [h.behavior_caller_query caller hv s,
      h.behavior_handler_query caller a hquery] at hx
    rw [MachineHandler.callerTree_query _ (caller.view_wrapState_of_query L hv)]
    refine ⟨_, _, hx.trans (.one _ (shape'_step _)), .refl _,
      .query _ _ _ (shape'_query _ _) (shape'_query _ _) ?_⟩
    intro answer
    refine ⟨next (L.answer (a, s) answer), L.update (a, s) answer, ?_, rfl⟩
    have hreturn : (h a).view
        (FreeM.pure (L.answer (a, s) answer, L.update (a, s) answer)) =
          .inl (L.answer (a, s) answer, L.update (a, s) answer) :=
      DynComputation.view_ofFreeM_pure _ _
    rw [h.behavior_handler_pure caller a hreturn,
      DynComputation.Pending.resume_ofView]
    exact .one _ (shape'_step _)

/-- Every finite direct-wrapper prefix has a dispatcher prefix with the same endpoint
and exactly three transitions per query: entry, primitive answer, and return.
No terminal-state assumption is required, so the bound also covers continuing callers. -/
theorem exists_dispatchTrace (L : StatefulLens P Q S) (caller : DynComputation P A B)
    {start finish : caller.State × S}
    (trace : (caller.wrapState L).ExecutionTrace start finish) :
    ∃ out : ((MachineHandler.ofFreeM L.toStateful).dispatch caller).ExecutionTrace
      (.caller start.1 start.2) (.caller finish.1 finish.2),
        out.length = 3 * trace.length := by
  refine DynComputation.ExecutionTrace.rec (machine := caller.wrapState L)
    (motive := fun start finish trace =>
    ∃ out : ((MachineHandler.ofFreeM L.toStateful).dispatch caller).ExecutionTrace
      (.caller start.1 start.2) (.caller finish.1 finish.2),
        out.length = 3 * trace.length) (fun _ => ⟨.nil _, rfl⟩) ?_ trace
  intro state position next finish hv answer tail ih
  obtain ⟨slow, hslow⟩ := ih
  let h := MachineHandler.ofFreeM L.toStateful
  rcases hc : caller.view state.1 with value | ⟨a, continuation⟩
  · rw [caller.view_wrapState_of_return L hc] at hv
    cases hv
  · rw [caller.view_wrapState_of_query L hc] at hv
    cases Sum.inr.inj hv
    let pending := DynComputation.Pending.ofView hc
    have hin : (h.dispatch caller).view (.caller state.1 state.2) =
        .inr ⟨.inr PUnit.unit, fun _ =>
          MachineHandler.Phase.handler a ((h a).init state.2) pending⟩ := by
      rw [h.view_dispatch, h.dispatchStep_caller_query caller hc]
    have hquery : (h a).view ((h a).init state.2) =
        .inr ⟨L.pos (a, state.2), fun answer => FreeM.pure
          (L.answer (a, state.2) answer, L.update (a, state.2) answer)⟩ :=
      DynComputation.view_ofFreeM_liftBind _ _ _
    have hbody : (h.dispatch caller).view
        (.handler a ((h a).init state.2) pending) =
        .inr ⟨.inl (L.pos (a, state.2)), fun answer =>
          MachineHandler.Phase.handler a (FreeM.pure
            (L.answer (a, state.2) answer, L.update (a, state.2) answer)) pending⟩ := by
      rw [h.view_dispatch, h.dispatchStep_handler_query caller a hquery]
    have hreturn : (h a).view
        (FreeM.pure (L.answer (a, state.2) answer, L.update (a, state.2) answer)) =
          .inl (L.answer (a, state.2) answer, L.update (a, state.2) answer) :=
      DynComputation.view_ofFreeM_pure _ _
    have hout : (h.dispatch caller).view
        (.handler a (FreeM.pure
          (L.answer (a, state.2) answer, L.update (a, state.2) answer)) pending) =
        .inr ⟨.inr PUnit.unit, fun _ => MachineHandler.Phase.caller
          (continuation (L.answer (a, state.2) answer)) (L.update (a, state.2) answer)⟩ := by
      rw [h.view_dispatch]
      rw [h.dispatchStep_handler_pure caller a hreturn]
      simp only [pending, DynComputation.Pending.resume_ofView]
    exact ⟨.query hin PUnit.unit (.query hbody answer (.query hout PUnit.unit slow)), by
      change slow.length + 1 + 1 + 1 = 3 * (tail.length + 1)
      omega⟩


end PFunctor.StatefulLens
