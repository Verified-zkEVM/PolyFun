# A first program: requests and handlers

The complete, checked example is
[`Examples/Tutorials/Requests.lean`](../../Examples/Tutorials/Requests.lean).
Build it with `lake build PolyFunExamples`, then open it in your Lean editor.

## Describe the interface

`Request` is a `PFunctor`. Its first field, `A`, describes the requests you can
make. Its second field, `B`, gives the response type for each request. Here
both are natural numbers. In a richer interface, a request to read a name
could expect a `String`, while a request to confirm an action expects a `Bool`.

An interface specifies what can be asked and the type of the answer. It does
not specify which answer an implementation will choose.

## Write the program

`twoRequests` is a `PFunctor.FreeM Request (Nat × Nat)`: a well-founded request
tree with a pair of natural numbers at each return. `FreeM.lift` asks one
question. In a `do` block, `←` binds the answer, and `return` produces the
result. The explicit `(P := Request)` tells Lean which dependent interface the
request belongs to.

The program asks `3`, receives `first`, then asks `first` and receives
`second`. Both responses are returned. It has no built-in rule for answering
either request.

## Choose an interpretation

`increment` is a `PFunctor.Handler Id Request`. A handler supplies an answer
computation for each request. `Id` means no additional effects: answering `n`
simply gives `n + 1`. `twoRequests.liftM increment` extends that rule to the
whole tree:

```text
request 3 → response 4 → request 4 → response 5 → return (4, 5)
```

The file proves this result with `rfl`, Lean’s proof by definitional equality. The theorem checks
the actual implementation of the program and handler, including the
dependence of the second request on the first response.

## Change the handler

The same file defines `double`, which answers `n` with `2 * n`, and proves
`twoRequests_double`. With this handler the first response is `6`, so the
second request is `6` and the result is `(6, 12)`.

Handlers can also keep state, report failure, or issue requests in another
interface. Those choices are expressed by the target monad: for example,
`StateT σ m`, `ExceptT ε m`, or `FreeM Q`. A probabilistic interpretation adds
probability semantics downstream; the request tree itself has no probabilities.

## Keep exploring

- [Polynomial functors](../guides/pfunctor.md) explains lenses and answer transport.
- [Computation models](../guides/computation-models.md) explains when continuing
  interaction calls for a resumption, ITree, or explicit-state machine.
- [Counter machine](../../Examples/Tutorials/Machines.lean) records state, runs,
  outputs, and a compositional execution law.
- [Indexed programs](indexed-programs.md) restrict which requests are available
  at each phase of a protocol.
- [Interaction trees](interaction-trees.md) run a program with state and ticks
  through the state corecursor and through handlers into other monads.
