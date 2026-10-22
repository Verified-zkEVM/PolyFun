/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Machine.Defs

/-!
# Admitted, permanently capped machine calls

An admission policy either refuses an operation or supplies its fuel and updated
service state and auxiliary admission state. The update happens before execution,
so a resource debit survives timeout. A timeout observation can retain the private
state in its error or project it back to the service state. `ExceptT` over `StateT` keeps this state
on failure and stops a free client's continuation at the first error.
-/

public section

universe u

namespace PFunctor.MachineHandler

open DynSystem.DynComputation

variable {P Q : PFunctor.{u, u}} {S T ε α : Type u}

/-- Interpret a saved chunk, retaining its admission state and explicit timeout observation. -/
@[expose] def finishAdmitted (h : MachineHandler P Q S)
    (timeout : (a : P.A) → S → (h a).State → ε × S) (a : P.A) (admitted : S × T) :
    Chunk (h a).State (P.B a × S) → Except ε (P.B a) × (S × T)
  | .done out => (.ok out.1, (out.2, admitted.2))
  | .paused residual =>
      let out := timeout a admitted.1 residual
      (.error out.1, (out.2, admitted.2))

/-- The service cannot change auxiliary admission data, even if it times out. -/
@[simp] theorem finishAdmitted_snd_snd (h : MachineHandler P Q S)
    (timeout : (a : P.A) → S → (h a).State → ε × S) (a : P.A) (admitted : S × T)
    (chunk : Chunk (h a).State (P.B a × S)) :
    (h.finishAdmitted timeout a admitted chunk).2.2 = admitted.2 := by
  cases chunk <;> rfl

/-- A refused call asks no primitive query. An admitted call runs its cap once;
errors retain state and abort the enclosing free client's continuation. -/
@[expose] def admitted (h : MachineHandler P Q S)
    (admit : (a : P.A) → (S × T) → Except ε (Nat × (S × T)))
    (timeout : (a : P.A) → S → (h a).State → ε × S) :
    Handler (ExceptT ε (StateT (S × T) (FreeM Q))) P := fun a =>
  ExceptT.mk fun state => match admit a state with
    | .error error => pure (.error error, state)
    | .ok (fuel, updated) =>
      FreeM.map (h.finishAdmitted timeout a updated)
        ((h a).unrollChunk fuel ((h a).init updated.1))

/-- Refusal preserves the incoming state and performs no primitive effects. -/
theorem admitted_run_error (h : MachineHandler P Q S)
    (admit : (a : P.A) → (S × T) → Except ε (Nat × (S × T)))
    (timeout : (a : P.A) → S → (h a).State → ε × S)
    (a : P.A) (state : S × T) (error : ε) (hrefused : admit a state = .error error) :
    ((h.admitted admit timeout a).run).run state = pure (.error error, state) := by
  change (match admit a state with
    | .error error => pure (.error error, state)
    | .ok (fuel, updated) => FreeM.map (h.finishAdmitted timeout a updated)
        ((h a).unrollChunk fuel ((h a).init updated.1)) : FreeM Q (Except ε (P.B a) × (S × T))) = _
  rw [hrefused]

/-- Successful admission initializes the bounded runner from the already updated state. -/
theorem admitted_run_ok (h : MachineHandler P Q S)
    (admit : (a : P.A) → (S × T) → Except ε (Nat × (S × T)))
    (timeout : (a : P.A) → S → (h a).State → ε × S)
    (a : P.A) (state updated : S × T) (fuel : Nat)
    (hadmitted : admit a state = .ok (fuel, updated)) :
    ((h.admitted admit timeout a).run).run state =
      FreeM.map (h.finishAdmitted timeout a updated)
        ((h a).unrollChunk fuel ((h a).init updated.1)) := by
  change (match admit a state with
    | .error error => pure (.error error, state)
    | .ok (fuel, updated) => FreeM.map (h.finishAdmitted timeout a updated)
        ((h a).unrollChunk fuel ((h a).init updated.1)) : FreeM Q (Except ε (P.B a) × (S × T))) = _
  rw [hadmitted]

/-- Refusing a request stops the rest of a finite client before any further effects. -/
theorem liftM_admitted_refused (h : MachineHandler P Q S)
    (admit : (a : P.A) → (S × T) → Except ε (Nat × (S × T)))
    (timeout : (a : P.A) → S → (h a).State → ε × S)
    (a : P.A) (next : P.B a → FreeM P α) (state : S × T) (error : ε)
    (hrefused : admit a state = .error error) :
    ((FreeM.liftM (h.admitted admit timeout) (.liftBind a next)).run).run state =
      pure (.error error, state) := by
  change (((h.admitted admit timeout a) >>=
    fun answer => FreeM.liftM (h.admitted admit timeout) (next answer)).run).run state = _
  rw [ExceptT.run_bind, StateT.run_bind,
    h.admitted_run_error admit timeout a state error hrefused]
  simp

end PFunctor.MachineHandler
