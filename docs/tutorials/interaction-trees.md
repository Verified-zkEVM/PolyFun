# Interaction trees: state, ticks, and three ways to run

The complete, checked example is
[`Examples/Tutorials/InteractionTrees.lean`](../../Examples/Tutorials/InteractionTrees.lean).
Build it with `lake build PolyFunExamples`, then open it in your Lean editor.

## Write the program

An interaction tree `ITree E α` is a possibly infinite tree of events from the
signature `E` with `α`-leaves and explicit silent steps. Here the signature is
a sum: state events on a natural number (`StateE Nat`, with `get` and
`put`) plus one external event, a tick.

<!-- lean-example: Examples/Tutorials/InteractionTrees.lean#PROGRAM -->
```lean
import PolyFun.ITree.Interp.State
import PolyFun.ITree.Interp.Laws

/-- One external event, a tick, acknowledged with no payload. -/
abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

/-- The program's signature: state events on a natural number, plus ticks. -/
abbrev Sig : PFunctor.{0, 0} := StateE Nat + Tick

/-- Read the counter, tick once, store the incremented value, and return the value read. -/
def bump : ITree Sig Nat := do
  let n ← (query (F := Sig) (.inl .get) ITree.pure : ITree Sig Nat)
  let _ ← query (F := Sig) (.inr ()) ITree.pure
  let _ ← query (F := Sig) (.inl (.put (n + 1))) ITree.pure
  ITree.pure n
```

`query a k` issues the event `a` and continues with `k` on the answer;
`ITree.pure` returns. The `do` block sequences three events. The type ascription on
the first line names the answer type of `get`, which the signature stores as a
dependent fiber.

## Run with the state corecursor

`runState bump s` eliminates the state events directly, threading the state
`s` through the tree. Each state operation becomes one silent `step`, the tick
stays visible as a `query`, and the final state is returned first:
`runState_bump` proves the result is `step (query () fun _ => step (pure (s + 1, s)))`,
by rewriting with the exact computation rules of `interpState`.

## Run through a handler

`interp h t` runs a tree in any iterative monad, answering each event through
a handler `h`. `StateE.stateHandler` answers `get` and `put` in
`StateT Nat (ITree Tick)` and leaves the tick in place. The result is not
syntactically the corecursor's: it returns the pair in the other order and
takes one silent step per node rather than per state operation. The library
proves the two agree up to weak bisimulation and pair order
(`interpState_weakBisim_interp`), and the file states that instance for `bump`.

## Change the handler

The same program interprets into `OptionT (ITree (StateE Nat))` through two
handlers that agree on state events and differ on the tick: `acknowledge`
answers it, `refuse` fails. The last example shows the loop step of `interp`
at a single tick asking the handler, so the refusing interpretation fails at
its first tick. Weak bisimulation is the right notion of equality for these
trees: the [bisimulation guide](../guides/bisimulation.md) explains why silent
steps must be hidden and how `WeakBisim` does it.

## Keep exploring

- [Interaction trees guide](../guides/itree.md) for the design, the
  iteration laws, and interpretation into monads.
- [Computation models](../guides/computation-models.md) for when to use a
  tree, a resumption, or an explicit-state machine.
- [Program logic](../guides/program-logic.md) for reasoning about loops with
  `vcgen`.
