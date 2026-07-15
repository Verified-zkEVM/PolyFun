/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Basic

/-! # Productive `while` loops for interaction trees

Lean elaborates `while` in a `do` block as iteration over `Lean.Loop`, selected
through a `ForIn` instance. The generic `ForIn m Lean.Loop Unit` instance uses
core `whileM`, whose partial recursion need not expose an `ITree` constructor
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

end ITree
