/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Complexity.Foundations.Semantics.Stateful.Composition
public import PolyFun.PFunctor.Bound
public import PolyFun.PFunctor.Dynamical.Responder.Reindex
public import PolyFun.PFunctor.Handler.Free

/-!
# Stateful specifications as responders

complexitylib's `Cslib.Stateful.Spec` is a deterministic state machine with typed operations, and
its clients are free programs over the operation signature `⟨Op, Result⟩`. Forgetting
admissibility, a specification is a PolyFun `PFunctor.Responder` for that signature: a dynamical
system over the internal hom `signature ⊸ y` that answers every operation and moves to the next
state. Its module layer is PolyFun's free-handler category.

## Main definitions

* `Cslib.Stateful.Spec.toResponder`, `Cslib.Stateful.Spec.ofResponder`: the two readings.

## Main results

* `Cslib.Stateful.Spec.ofResponder_toResponder`, `Cslib.Stateful.Spec.toResponder_ofResponder`:
  specifications without admissibility constraints are responders.
* `Cslib.Stateful.eval_eq_runFree`: interpreting a client is running it against the responder.
* `Cslib.Stateful.Module.id_methods`, `Cslib.Stateful.Module.comp_methods`: module identity and
  composition are the free-handler identity and Kleisli composition.
* `Cslib.Stateful.Spec.totalCost_runClient_le_of_isRollBound`: a structural per-operation budget
  bounds the state-independent charge of every history a client selects.
-/

@[expose] public section

universe u v w y

namespace Cslib.Stateful

open PFunctor

namespace Spec

variable (D : Spec.{u, v, w})

/-- A specification's transition as a responder for its operation signature: at each state it
answers every operation and moves to the next state. -/
def toResponder : Responder D.State D.signature :=
  Responder.mk' (fun s o => (D.step s o).2) (fun s o => (D.step s o).1)

@[simp] theorem toResponder_answer (s : D.State) (o : D.Op) :
    D.toResponder.answer s o = (D.step s o).2 := rfl

@[simp] theorem toResponder_next (s : D.State) (o : D.Op) :
    D.toResponder.next s o = (D.step s o).1 := rfl

/-- A responder as a specification without admissibility constraints. -/
def ofResponder {S : Type u} {q : PFunctor.{v, w}} (R : Responder S q) : Spec.{u, v, w} where
  State := S
  Op := q.A
  Result := q.B
  step s o := (R.next s o, R.answer s o)

theorem toResponder_ofResponder {S : Type u} {q : PFunctor.{v, w}} (R : Responder S q) :
    (ofResponder R).toResponder = R := by
  ext <;> rfl

/-- Reading a specification as a responder forgets only its admissibility predicate. -/
theorem ofResponder_toResponder : ofResponder D.toResponder = { D with valid := fun _ _ => True } :=
  rfl

variable {D}

/-- A per-operation structural budget bounds the state-independent charge of the history that a
client selects, in every specification and from every state. -/
theorem totalCost_runClient_le_of_isRollBound (c : D.Op → ℕ) {α : Type y} {p : D.Client α}
    {n : ℕ} (h : FreeM.IsRollBound p n (fun o b => c o ≤ b) (fun o b => b - c o))
    (s : D.State) : D.totalCost (fun _ o => c o) s (D.runClient s p).2.2 ≤ n := by
  induction p using PFunctor.FreeM.induction generalizing s n with
  | pure a => exact Nat.zero_le _
  | lift_bind o k ih =>
    rw [FreeM.isRollBound_lift_bind_iff] at h
    obtain ⟨hc, hk⟩ := h
    have hrest := ih (D.step s o).2 (hk (D.step s o).2) (D.step s o).1
    change c o + D.totalCost _ (D.step s o).1
      (D.runClient (D.step s o).1 (k (D.step s o).2)).2.2 ≤ n
    omega

end Spec

/-- Interpreting a client against a specification is running it against the specification's
responder. -/
theorem eval_eq_runFree {D : Spec.{u, v, w}} {α : Type y} (p : D.Client α) (s : D.State) :
    eval D p s = D.toResponder.runFree p s := by
  induction p using PFunctor.FreeM.induction generalizing s with
  | pure a => rfl
  | lift_bind o k ih => exact ih (D.step s o).2 (D.step s o).1

variable {D E F : Spec.{u, v, w}} {α : Type w}

/-- Module methods are free handlers of the upper signature into programs over the lower one. -/
theorem methods_eq_handler : Methods D E = Handler (FreeM E.signature) D.signature := rfl

theorem link_eq_liftM (methods : Methods D E) (p : D.Client α) :
    link methods p = p.liftM methods := rfl

/-- The identity module issues each operation unchanged: the identity free handler. -/
theorem Module.id_methods : (Module.id D).methods = Handler.id D.signature := rfl

/-- Composing modules composes their method tables in the free-handler Kleisli category. -/
theorem Module.comp_methods (M : Module D E) (N : Module E F) :
    (M.comp N).methods =
      Handler.comp (P := D.signature) (Q := E.signature) (R := F.signature)
        N.methods M.methods :=
  rfl

end Cslib.Stateful
