/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Machine.Defs
public import PolyFun.ITree.ResumptionWithTau
public import PolyFun.ITree.Free
public import PolyFun.ITree.Interp.Laws
public import PolyFun.ITree.Interp.Stateful
public import PolyFun.Control.Monad.Iter.Instances

/-!
# Stateful machine dispatch and interaction-tree interpretation

The dispatcher's unary administrative events are silent steps. Its observable
behavior agrees with interpreting the caller in the state transformer over
interaction trees. This equivalence preserves divergence and primitive effects;
it does not identify execution budgets or timing observations.
-/

public section

universe u

namespace PFunctor.MachineHandler

open DynSystem ITree

variable {P Q : PFunctor.{u, u}} {S A B : Type u}

/-- A service interpreted in stateful interaction trees through the canonical resumption bridge. -/
@[expose] def toITreeHandler (h : MachineHandler P Q S) : Handler.Stateful (ITree Q) S P :=
  fun a s => (h a).denote s |>.toITree

/-- Observe a dispatcher residual with administrative transitions as silent steps. -/
@[expose] def behavior (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B)
    (phase : Phase h caller) : ITree Q (B × S) :=
  ofResumptionWithTau ((h.dispatch caller).toDynSystem.behavior phase)

/-- The caller's residual behavior as a tau-free interaction tree. -/
@[expose] def callerTree (caller : DynComputation.{u} P A B) (state : caller.State) : ITree P B :=
  Resumption.toITree (caller.toDynSystem.behavior state)

private theorem shape_behavior (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B)
    (phase : Phase h caller) :
    shape' (h.behavior caller phase) = match h.dispatchStep caller phase with
    | .inl b => .mk (.pure b) PEmpty.elim
    | .inr ⟨.inl q, k⟩ => .mk (.query q) (fun a => h.behavior caller (k a))
    | .inr ⟨.inr _, k⟩ => .mk .step (fun a => h.behavior caller (k a)) := by
  rw [behavior, shape'_ofResumptionWithTau,
    DynComputation.dest_behavior_view (h.dispatch caller), view_dispatch]
  rcases h.dispatchStep caller phase with b | ⟨q, k⟩
  · rfl
  · cases q <;> rfl

/-- A caller return is observable without consuming a dispatch step. -/
theorem behavior_caller_pure (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B)
    {state : caller.State} {b : B} (hb : caller.view state = .inl b) (s : S) :
    h.behavior caller (.caller state s) = ITree.pure (b, s) := by
  apply eq_pure_of_dest (c := PEmpty.elim)
  rw [shape_behavior, dispatchStep_caller_pure h caller hb]

/-- Entering a service call consumes one administrative step. -/
theorem behavior_caller_query (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B)
    {state : caller.State} {a : P.A} {next : P.B a → caller.State}
    (ha : caller.view state = .inr ⟨a, next⟩) (s : S) :
    h.behavior caller (.caller state s) =
      step (h.behavior caller (.handler a ((h a).init s) (.ofView ha))) := by
  apply eq_step_of_dest (c := fun _ => h.behavior caller (.handler a ((h a).init s) (.ofView ha)))
  rw [shape_behavior, dispatchStep_caller_query h caller ha]

/-- Returning from a service consumes one administrative step and updates shared state. -/
theorem behavior_handler_pure (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B)
    (a : P.A) {state : (h a).State} {result : P.B a × S}
    (hb : (h a).view state = .inl result) (pending : caller.Pending a) :
    h.behavior caller (.handler a state pending) =
      step (h.behavior caller (.caller (pending.resume result.1) result.2)) := by
  apply eq_step_of_dest
    (c := fun _ => h.behavior caller (.caller (pending.resume result.1) result.2))
  rw [shape_behavior, dispatchStep, hb]

/-- An active service's primitive query retains its dependent continuation. -/
theorem behavior_handler_query (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B)
    (a : P.A) {state : (h a).State} {q : Q.A} {rest : Q.B q → (h a).State}
    (hq : (h a).view state = .inr ⟨q, rest⟩) (pending : caller.Pending a) :
    h.behavior caller (.handler a state pending) =
      query q (fun answer => h.behavior caller (.handler a (rest answer) pending)) := by
  apply eq_query_of_dest
  rw [shape_behavior, dispatchStep, hq]

private theorem callerTree_pure (caller : DynComputation.{u} P A B) {state : caller.State}
    {b : B} (hb : caller.view state = .inl b) : callerTree caller state = ITree.pure b := by
  apply eq_pure_of_dest (c := PEmpty.elim)
  rw [callerTree, Resumption.shape'_toITree, DynComputation.dest_behavior_view, hb]
  rfl

private theorem callerTree_query (caller : DynComputation.{u} P A B) {state : caller.State}
    {a : P.A} {next : P.B a → caller.State}
    (ha : caller.view state = .inr ⟨a, next⟩) :
    callerTree caller state = query a (fun b => callerTree caller (next b)) := by
  apply eq_query_of_dest
  rw [callerTree, Resumption.shape'_toITree, DynComputation.dest_behavior_view, ha]
  rfl

/-- Interpretation of a retained phase, including the return guard of an active call. -/
private def phaseMeaning (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B) :
    Phase h caller → ITree Q (B × S)
  | .caller state s => (interp h.toITreeHandler (callerTree caller state)).run s
  | .handler a state pending => callerTree (h a) state >>= fun result =>
      step ((interp h.toITreeHandler (callerTree caller (pending.resume result.1))).run result.2)

/-- Dispatch from any retained phase agrees with the stateful interaction-tree interpreter. -/
private theorem behavior_weakBisim_phaseMeaning (h : MachineHandler P Q S)
    (caller : DynComputation.{u} P A B) (phase : Phase h caller) :
    WeakBisim (h.behavior caller phase) (h.phaseMeaning caller phase) := by
  let R := fun x y => ∃ p, x = h.behavior caller p ∧ y = h.phaseMeaning caller p
  have handlerMatch (a : P.A) (state : (h a).State) (pending : caller.Pending a) :
      WeakBisimF R (h.behavior caller (.handler a state pending))
        (h.phaseMeaning caller (.handler a state pending)) := by
    rcases hv : (h a).view state with result | ⟨q, rest⟩
    · rw [behavior_handler_pure h caller a hv, phaseMeaning, callerTree_pure _ hv,
        ITree.bind_eq_bind, bind_pure_left]
      exact ⟨_, _, .refl _, .refl _, .tau _ _ (shape'_step _) (shape'_step _)
        ⟨.caller (pending.resume result.1) result.2, rfl, rfl⟩⟩
    · rw [behavior_handler_query h caller a hv, phaseMeaning, callerTree_query _ hv,
        ITree.bind_eq_bind, bind_query]
      exact ⟨_, _, .refl _, .refl _, .query q _ _ (shape'_query _ _) (shape'_query _ _)
        (fun b => ⟨.handler a (rest b) pending, rfl, rfl⟩)⟩
  apply WeakBisim.coinduct R ?_ ⟨phase, rfl, rfl⟩
  rintro x y ⟨p, rfl, rfl⟩
  cases p with
  | handler a state pending => exact handlerMatch a state pending
  | caller state s =>
    rcases hv : caller.view state with b | ⟨a, next⟩
    · rw [behavior_caller_pure h caller hv, phaseMeaning, callerTree_pure _ hv, interp_run_pure]
      exact ⟨_, _, .refl _, .refl _, .pure _ (shape'_pure _) (shape'_pure _)⟩
    · rw [behavior_caller_query h caller hv, phaseMeaning, callerTree_query _ hv,
        interp_run_query]
      obtain ⟨x, y, hx, hy, hm⟩ := handlerMatch a ((h a).init s) (.ofView hv)
      change TauSteps (callerTree (h a) ((h a).init s) >>= fun result =>
        step ((interp h.toITreeHandler
          (callerTree caller ((DynComputation.Pending.ofView hv).resume result.1))).run result.2)) y
        at hy
      simp only [DynComputation.Pending.resume_ofView] at hy
      exact ⟨x, y, (TauSteps.one _ (shape'_step _)).trans hx, hy, hm⟩

/-- Interpreting a finite client agrees with the service's resumption fold. -/
theorem interp_weakBisim_execute (h : MachineHandler P Q S) (client : FreeM P B) (s : S) :
    WeakBisim ((interp h.toITreeHandler client.toITree).run s)
      (h.execute client s).toITree := by
  induction client generalizing s with
  | pure b =>
      rw [FreeM.toITree_pure, interp_run_pure, execute_pure]
      rw [Resumption.pure_eq_pure, Resumption.toITree_pure]
      exact WeakBisim.refl _
  | lift_bind a next ih =>
      change WeakBisim ((interp h.toITreeHandler (FreeM.liftBind a next).toITree).run s)
        (h.execute (.liftBind a next) s).toITree
      rw [FreeM.toITree_liftBind, interp_run_query, execute_liftBind,
        Resumption.bind_eq_bind, Resumption.toITree_bind]
      change WeakBisim (ITree.bind _ _) (ITree.bind _ _)
      exact bind_weakBisim_cont fun result => (ih result.1 result.2).step_left

/-- The composed machine implements stateful interpretation of the caller, up to silent steps. -/
theorem dispatch_weakBisim_interp (h : MachineHandler P Q S)
    (caller : DynComputation.{u} P A B) (input : A) (s : S) :
    WeakBisim (ofResumptionWithTau ((h.dispatch caller).denote (input, s)))
      ((interp h.toITreeHandler ((caller.denote input).toITree)).run s) :=
  h.behavior_weakBisim_phaseMeaning caller (.caller (caller.init input) s)

/-- A compiled finite client has exactly the stateful resumption-fold behavior,
up to administrative silent steps. No uniform depth bound on the client or handler is needed. -/
theorem compile_weakBisim_execute (h : MachineHandler P Q S) (client : A → FreeM P B)
    (input : A) (s : S) :
    WeakBisim (ofResumptionWithTau ((h.compile client).denote (input, s)))
      (h.execute (client input) s).toITree := by
  have h₁ := h.dispatch_weakBisim_interp (.ofFreeM client) input s
  rw [DynComputation.denote_ofFreeM] at h₁
  exact h₁.trans (h.interp_weakBisim_execute (client input) s)

end PFunctor.MachineHandler
