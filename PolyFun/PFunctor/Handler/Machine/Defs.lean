/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Stateful.Combinators
public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable
public import PolyFun.PFunctor.Dynamical.DynComputation.Pending

/-!
# Stateful services implemented by machines

A `MachineHandler` implements each dependent operation by a returning machine.
The service state is shared between calls; the machine's private execution state
is retained while a call is suspended. `dispatch` composes an arbitrary caller
machine with such a service. Entry and return each issue a unary administrative
event, while primitive queries retain their original dependent answer types.

The same dispatcher serves finite `FreeM` clients through `compile`. Chunked
execution uses the ordinary `DynComputation` runners, so resuming a paused
handler neither restarts the call nor replays its earlier primitive effects.
-/

public section

universe u

namespace PFunctor

open DynSystem

/-- A dependent service whose operations are explicit-state returning machines. -/
abbrev MachineHandler (P Q : PFunctor.{u, u}) (S : Type u) :=
  (a : P.A) → DynComputation.{u} Q S (P.B a × S)

namespace MachineHandler

variable {P Q : PFunctor.{u, u}} {S A B : Type u}

/-- Forget private execution state, retaining the service's stateful behavior. -/
@[expose] def toHandler (h : MachineHandler P Q S) : Handler.Stateful (Resumption Q) S P :=
  fun a s => (h a).denote s

/-- Interpret a well-founded client with the service's resumption handler. -/
@[expose] def execute (h : MachineHandler P Q S) (client : FreeM P B) (s : S) :
    Resumption Q (B × S) :=
  h.toHandler.run client s

@[simp] theorem execute_pure (h : MachineHandler P Q S) (b : B) (s : S) :
    h.execute (pure b) s = pure (b, s) := rfl

theorem execute_liftBind (h : MachineHandler P Q S) (a : P.A)
    (next : P.B a → FreeM P B) (s : S) :
    h.execute (.liftBind a next) s =
      (h a).denote s >>= fun out => h.execute (next out.1) out.2 :=
  Handler.Stateful.run_liftBind h.toHandler a next s

theorem execute_bind (h : MachineHandler P Q S) (client : FreeM P A)
    (next : A → FreeM P B) (s : S) :
    h.execute (client >>= next) s =
      h.execute client s >>= fun out => h.execute (next out.1) out.2 :=
  Handler.Stateful.run_bind h.toHandler client next s

/-- Either a caller ready to run or a service call with its suspended continuation. -/
inductive Phase (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B) where
  | caller (state : caller.State) (service : S)
  | handler (operation : P.A) (state : (h operation).State)
      (pending : caller.Pending operation)

/-- One dispatcher transition. Administrative events are the right unary summand. -/
@[expose] def dispatchStep (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B) :
    Phase h caller → (B × S) ⊕ (Q + y.{u, u}).Obj (Phase h caller)
  | .caller state service => match hv : caller.view state with
    | .inl value => .inl (value, service)
    | .inr ⟨a, _next⟩ => .inr ⟨.inr PUnit.unit,
        fun _ => .handler a ((h a).init service) (.ofView hv)⟩
  | .handler a state pending => match (h a).view state with
    | .inl result => .inr ⟨.inr PUnit.unit, fun _ => .caller (pending.resume result.1) result.2⟩
    | .inr ⟨q, rest⟩ => .inr ⟨.inl q, fun answer => .handler a (rest answer) pending⟩

/-- A returned caller needs no transition. -/
@[simp] theorem dispatchStep_caller_pure (h : MachineHandler P Q S)
    (caller : DynComputation.{u} P A B) {state : caller.State} {b : B}
    (hb : caller.view state = .inl b) (s : S) :
    h.dispatchStep caller (.caller state s) = .inl (b, s) := by
  simp only [dispatchStep]
  split
  · rename_i value hv
    have heq := Sum.inl.inj (hv.symm.trans hb)
    subst value
    rfl
  · rename_i operation next hv
    have heq := hv.symm.trans hb
    cases heq

/-- Entering a call retains the caller state and pending-operation evidence. -/
theorem dispatchStep_caller_query (h : MachineHandler P Q S)
    (caller : DynComputation.{u} P A B) {state : caller.State} {a : P.A}
    {next : P.B a → caller.State} (ha : caller.view state = .inr ⟨a, next⟩) (s : S) :
    h.dispatchStep caller (.caller state s) =
      .inr ⟨.inr PUnit.unit, fun _ => .handler a ((h a).init s) (.ofView ha)⟩ := by
  simp only [dispatchStep]
  split
  · rename_i value hv
    have heq := hv.symm.trans ha
    cases heq
  · rename_i operation rest hv
    have heq := Sum.inr.inj (hv.symm.trans ha)
    cases heq
    rfl

/-- A completed service resumes its suspended caller after one administrative transition. -/
theorem dispatchStep_handler_pure (h : MachineHandler P Q S)
    (caller : DynComputation P A B) (a : P.A) {state : (h a).State} {result : P.B a × S}
    (hb : (h a).view state = .inl result) (pending : caller.Pending a) :
    h.dispatchStep caller (.handler a state pending) =
      .inr ⟨.inr PUnit.unit, fun _ => .caller (pending.resume result.1) result.2⟩ := by
  simp only [dispatchStep, hb]

/-- A service query retains its operation and suspended caller across the primitive answer. -/
theorem dispatchStep_handler_query (h : MachineHandler P Q S)
    (caller : DynComputation P A B) (a : P.A) {state : (h a).State}
    {q : Q.A} {rest : Q.B q → (h a).State}
    (hq : (h a).view state = .inr ⟨q, rest⟩) (pending : caller.Pending a) :
    h.dispatchStep caller (.handler a state pending) =
      .inr ⟨.inl q, fun answer => .handler a (rest answer) pending⟩ := by
  simp only [dispatchStep, hq]

/-- Compose a caller and service into one machine, with explicit dispatch steps.
The state projection reduces to `Phase`, so consumers can inspect retained phases. -/
@[expose, implicit_reducible] def dispatch (h : MachineHandler P Q S)
    (caller : DynComputation.{u} P A B) :
    DynComputation.{u} (Q + y.{u, u}) (A × S) (B × S) :=
  .ofStep (h.dispatchStep caller) fun input => .caller (caller.init input.1) input.2

@[simp] theorem view_dispatch (h : MachineHandler P Q S) (caller : DynComputation.{u} P A B)
    (phase : Phase h caller) :
    (h.dispatch caller).view phase = h.dispatchStep caller phase :=
  DynComputation.view_ofStep _ _ _

/-- Compile a family of finite clients using the same dispatcher as arbitrary machines. -/
@[expose, implicit_reducible] def compile (h : MachineHandler P Q S) (client : A → FreeM P B) :
    DynComputation.{u} (Q + y.{u, u}) (A × S) (B × S) :=
  h.dispatch (.ofFreeM client)

/-- A finite stateful handler as a machine service, with residual programs as private state. -/
@[expose] def ofFreeM (h : Handler.Stateful (FreeM Q) S P) : MachineHandler P Q S :=
  fun a => .ofFreeM (h a)

@[simp] theorem toHandler_ofFreeM (h : Handler.Stateful (FreeM Q) S P) (a : P.A) (s : S) :
    (ofFreeM h).toHandler a s = (h a s).toResumption :=
  DynComputation.denote_ofFreeM _ _

/-- Finite service machines agree with the existing stateful free-program fold. -/
theorem execute_ofFreeM (h : Handler.Stateful (FreeM Q) S P)
    (client : FreeM P B) (s : S) :
    (ofFreeM h).execute client s = (h.run client s).toResumption := by
  induction client generalizing s with
  | pure b => rfl
  | lift_bind a next ih =>
      change (ofFreeM h).execute (.liftBind a next) s =
        (h.run (.liftBind a next) s).toResumption
      rw [execute_liftBind, ofFreeM, DynComputation.denote_ofFreeM,
        Handler.Stateful.run_liftBind, ← FreeM.bind_eq_bind, FreeM.toResumption_bind]
      exact congrArg (Resumption.bind _) (funext fun result => ih result.1 result.2)

/-- Finite interface translation reuses stateful-handler reindexing with the same shared state. -/
theorem execute_liftM {R : PFunctor.{u, u}} (h : MachineHandler Q R S)
    (translation : Handler (FreeM Q) P) (client : FreeM P B) (s : S) :
    h.execute (client.liftM translation) s =
      (h.toHandler.reindex translation).run client s :=
  (Handler.Stateful.run_reindex translation h.toHandler client s).symm

/-- A permanently capped service call. A timeout aborts the client through `OptionT`;
resuming a paused machine is the separate `DynComputation.continueChunk` operation. -/
@[expose] def capped (h : MachineHandler P Q S) (cap : (a : P.A) → S → Nat) :
    Handler.Stateful (OptionT (FreeM Q)) S P := fun a s =>
  OptionT.mk ((h a).unroll (cap a s) ((h a).init s))

/-- The optional run of a capped operation is its ordinary finite machine unrolling. -/
@[simp] theorem capped_run (h : MachineHandler P Q S) (cap : (a : P.A) → S → Nat)
    (a : P.A) (s : S) :
    ((h.capped cap a).run s).run = (h a).unroll (cap a s) ((h a).init s) := rfl

end MachineHandler
end PFunctor
