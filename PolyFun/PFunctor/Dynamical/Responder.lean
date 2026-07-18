/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.InternalHom
public import PolyFun.PFunctor.Handler
public import PolyFun.PFunctor.Dynamical.Basic

/-!
# Responders: stateful answerers as systems over the internal hom

A **responder** for an interface `q` receives `q`-positions (queries) and returns
`q`-directions (answers), updating an internal state as it goes. Following
Spivak–Niu, *Polynomial Functors: A Mathematical Theory of Interaction* (Ex 4.78),
this is exactly a dynamical system over the internal hom `q ⊸ X`: by `ihom_X_A`
the positions of `q ⊸ X` are the sections of `q`, so at each state the responder
*commits* to an answer for every possible query, and a direction of `q ⊸ X` over
a committed section carries only the query actually asked (its `X`-component is
trivial). The dynamical accessors under responder names are

* `Responder.committed : S → Section q` — the answer-section exposed at a state;
* `Responder.answer : S → (a : q.A) → q.B a` — the committed answer to a query;
* `Responder.next : S → q.A → S` — the state update on hearing a query.

A responder is the deterministic challenger side of a game before Kleisli
weighting: wiring it against an adversary along `Lens.eval` closes the system
(`DynSystem.game` / `DynSystem.closedGame`). The `equivStateHandler` bridge
identifies responders with handlers in the state monad `StateT S Id` — Mealy
machines in Kleisli form — of which VCVio's `ProbResponder` (the `WireK` layer)
is the bundled probabilistic `m := SPMF` sibling.
-/

@[expose] public section

universe u v uA uB

namespace PFunctor

/-- A **responder** with states `S` for the interface `q`: a dynamical system over
the internal hom `q ⊸ X` (Spivak–Niu Ex 4.78). By `ihom_X_A` its exposed
positions are the sections of `q` — at each state the responder commits to an
answer for every possible query — and a direction over a committed section is
just a query, so `update` evolves the state by the query heard. -/
abbrev Responder (S : Type u) (q : PFunctor.{uA, uB}) : Type _ :=
  DynSystem S (q ⊸ X.{uA, uB})

namespace Responder

variable {S : Type u} {q : PFunctor.{uA, uB}}

/-- The answer-section a responder commits to at state `s`: its exposed position,
read as a `Section q` through `ihom_X_A`. -/
def committed (R : Responder S q) (s : S) : Section q :=
  DynSystem.expose R s

/-- The answer a responder gives at state `s` to the query `a`: the direction its
committed section selects at `a`. -/
def answer (R : Responder S q) (s : S) (a : q.A) : q.B a :=
  (DynSystem.expose R s).toFunB a PUnit.unit

/-- The responder's next state after hearing the query `a` at state `s`. -/
def next (R : Responder S q) (s : S) (a : q.A) : S :=
  DynSystem.update R s ⟨a, PUnit.unit⟩

/-- Build a responder from an answer map and a next-state map. -/
def mk' (ans : (s : S) → (a : q.A) → q.B a) (nxt : S → q.A → S) : Responder S q :=
  (fun s => sectionLens (ans s)) ⇆ (fun s d => nxt s d.1)

@[simp] theorem answer_mk' (ans : (s : S) → (a : q.A) → q.B a) (nxt : S → q.A → S)
    (s : S) (a : q.A) : (mk' ans nxt).answer s a = ans s a := rfl

@[simp] theorem next_mk' (ans : (s : S) → (a : q.A) → q.B a) (nxt : S → q.A → S)
    (s : S) (a : q.A) : (mk' ans nxt).next s a = nxt s a := rfl

/-- Responders are determined by their pointwise answers and next states.
Unlike `equivStateHandler`, this extensionality principle imposes no equality
between the responder-state and interface-direction universes. -/
@[ext]
theorem ext (R R' : Responder S q)
    (hAnswer : ∀ state query, R.answer state query = R'.answer state query)
    (hNext : ∀ state query, R.next state query = R'.next state query) :
    R = R' := by
  rcases R with ⟨expose, update⟩
  rcases R' with ⟨expose', update'⟩
  have hExpose : expose = expose' := by
    funext state
    apply Lens.ext
    case h₁ =>
      intro query
      exact Subsingleton.elim _ _
    case h₂ =>
      intro query
      funext direction
      cases direction
      exact hAnswer state query
  subst expose'
  congr
  funext state direction
  rcases direction with ⟨query, trivialDirection⟩
  cases trivialDirection
  exact hNext state query

@[simp] theorem expose_mk' (ans : (s : S) → (a : q.A) → q.B a) (nxt : S → q.A → S)
    (s : S) : DynSystem.expose (mk' ans nxt) s = sectionLens (ans s) := rfl

@[simp] theorem committed_mk' (ans : (s : S) → (a : q.A) → q.B a) (nxt : S → q.A → S)
    (s : S) : (mk' ans nxt).committed s = sectionLens (ans s) := rfl

/-- `answer` reads the committed section at the query asked. -/
theorem answer_eq_committed (R : Responder S q) (s : S) (a : q.A) :
    R.answer s a = (R.committed s).toFunB a PUnit.unit := rfl

/-- A responder's raw lens update reads only the query component of a direction —
the `X`-component is trivial. Definitional, by sigma and unit eta. -/
@[simp] theorem update_eq_next (R : Responder S q) (s : S)
    (d : (q ⊸ X).B (DynSystem.expose R s)) :
    DynSystem.update R s d = R.next s d.1 := rfl

/-! ## Stateless responders -/

/-- The stateless responder answering along a fixed section of `q`. -/
def ofSection (σ : Section q) : Responder PUnit.{v + 1} q :=
  Lens.fromX σ

@[simp] theorem committed_ofSection (σ : Section q) (s : PUnit.{v + 1}) :
    (ofSection σ).committed s = σ := rfl

/-- The stateless responder answering along a fixed deterministic handler
(`Handler Id q` is a section of `q` unbundled). -/
def ofHandler (h : Handler Id q) : Responder PUnit.{v + 1} q :=
  mk' (fun _ => h) (fun _ _ => PUnit.unit)

/-- A deterministic handler responds exactly as its section lens does. -/
theorem ofHandler_eq_ofSection (h : Handler Id q) :
    (ofHandler h : Responder PUnit.{v + 1} q) = ofSection (sectionLens h) := rfl

end Responder

/-! ## The Kleisli–Mealy bridge

A responder with states `S` is the same data as a handler in the state monad
`StateT S Id`, i.e. a Mealy machine `(a : q.A) → S → q.B a × S` in Kleisli form.
The direction universe is pinned to the state's (`q : PFunctor.{uA, u}`,
`S : Type u`) so the state monad applies. VCVio's `ProbResponder` is the bundled
probabilistic `m := SPMF` sibling of this bridge. -/

namespace Responder

section KleisliMealy

variable {q : PFunctor.{uA, u}} {S : Type u}

/-- Read a responder as a stateful handler: answer the query from the current
state and thread the next state. -/
def toStateHandler (R : Responder S q) : Handler (StateT S Id) q :=
  fun a s => (R.answer s a, R.next s a)

/-- Bundle a stateful handler as a responder. -/
def ofStateHandler (h : Handler (StateT S Id) q) : Responder S q :=
  mk' (fun s a => (h a s).1) (fun s a => (h a s).2)

/-- The **Kleisli–Mealy bridge**: responders with states `S` for `q` are exactly
the stateful handlers in `StateT S Id`, with both round-trips definitional.
VCVio's `ProbResponder` is the bundled `m := SPMF` sibling of this equivalence. -/
def equivStateHandler : Responder S q ≃ Handler (StateT S Id) q where
  toFun := toStateHandler
  invFun := ofStateHandler
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equivStateHandler_apply (R : Responder S q) :
    equivStateHandler R = R.toStateHandler := rfl

@[simp] theorem equivStateHandler_symm_apply (h : Handler (StateT S Id) q) :
    equivStateHandler.symm h = ofStateHandler h := rfl

end KleisliMealy

end Responder

end PFunctor
