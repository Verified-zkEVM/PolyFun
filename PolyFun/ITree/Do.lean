/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Bisim.Iter

/-! # Productive `while` loops for interaction trees

Lean elaborates `while` in a `do` block as iteration over `Lean.Loop`, selected
through a `ForIn` instance. The generic `ForIn m Lean.Loop Unit` instance uses
core `repeatM`, whose partial recursion need not expose an `ITree` constructor
before continuing the loop.

Opening the `ITree` scope selects the instance in this file instead:

```lean
open scoped ITree

def count : ITree F Nat := do
  let mut n := 0
  while n < 3 do
    n := n + 1
  return n
```

The specialized instance sends `ForInStep.yield` to the continuing branch of
`ITree.iter` and `ForInStep.done` to its terminating branch. Consequently every
continued iteration is guarded by the silent step inserted by `ITree.iter`.
The instance is scoped because it deliberately changes the semantics selected
for `while`; merely importing this module does not activate it.
-/

@[expose] public section

universe uA uB uβ

namespace ITree

/-- Implement Lean's internal `Lean.Loop` protocol using productive
interaction-tree iteration.

`ForInStep.yield next` continues with `next`, while
`ForInStep.done result` terminates with `result`. This is definitionally an
`ITree.iter` call, so the continuing branch receives its usual silent-step
productivity guard. -/
def forInLoop {F : PFunctor.{uA, uB}} {β : Type uβ} (_ : Lean.Loop) (init : β)
    (body : Unit → β → ITree F (ForInStep β)) : ITree F β :=
  iter (fun state => do
    match ← body () state with
    | .done result => pure (.inr result)
    | .yield next => pure (.inl next)) init

/-- Expose the `ITree.iter` selected by `forInLoop`. -/
theorem forInLoop_eq_iter {F : PFunctor.{uA, uB}} {β : Type uβ}
    (loop : Lean.Loop) (init : β) (body : Unit → β → ITree F (ForInStep β)) :
    forInLoop loop init body =
      iter (fun state => do
        match ← body () state with
        | .done result => pure (.inr result)
        | .yield next => pure (.inl next)) init :=
  rfl

/-- Opt-in productive interpretation of `while` notation for `ITree`.

Activate it with `open scoped ITree`. Its high priority makes it win over
Lean's generic `ForIn m Lean.Loop Unit` instance only while the scope is open. -/
scoped instance (priority := high) instForInLoop {F : PFunctor.{uA, uB}} :
    ForIn (ITree F) Lean.Loop Unit where
  forIn := forInLoop

/-! ## Reasoning about the loop

`ITree.iter` is lawful only up to weak bisimulation, and `ITree` carries no
possible-output predicate for a postcondition to range over, so the loop rule is
stated as a bisimulation congruence rather than as a weakest-precondition
instance. What it supplies is the usual licence to *assume* an invariant inside
the body: a body may be replaced by one that is only correct on the states the
loop can actually reach.

The invariant travels inside the relation rather than as a separate hypothesis.
Relating a `ForInStep` to itself *together with* `I` on its `yield` payload is
what makes `iter_weakBisimRel`'s state relation `fun i j => i = j ∧ I i`
inductive: the body hands back exactly the fact the next iteration needs.
-/

/-- Invariant-scoped congruence for `forInLoop`. If `I` holds of the initial state, and at
every state satisfying `I` the two bodies are weakly bisimilar under a relation
that additionally re-establishes `I` on each `yield`, then the two loops are
weakly bisimilar.

This licenses replacing a body by a simplification valid only under `I`. Preservation
of `I` is a hypothesis used to keep the relational argument inductive, not a separate
postcondition established by the conclusion. -/
theorem forInLoop_weakBisim_of_invariant {F : PFunctor.{uA, uB}} {β : Type uβ}
    (I : β → Prop) (loop : Lean.Loop) {init : β} (hinit : I init)
    {body₁ body₂ : Unit → β → ITree F (ForInStep β)}
    (hbody : ∀ b, I b →
      WeakBisimRel (fun s s' => s = s' ∧ ∀ n, s = ForInStep.yield n → I n)
        (body₁ () b) (body₂ () b)) :
    WeakBisim (forInLoop loop init body₁) (forInLoop loop init body₂) := by
  refine iter_weakBisimRel (RI := fun i j => i = j ∧ I i) (RR := Eq) ?_ ⟨rfl, hinit⟩
  rintro i j ⟨rfl, hI⟩
  refine bind_weakBisimRel (hbody i hI) ?_
  rintro s s' ⟨rfl, hs⟩
  cases s with
  | done result => exact WeakBisimRel.pure (.inr rfl)
  | yield next => exact WeakBisimRel.pure (.inl ⟨rfl, hs next rfl⟩)

end ITree
