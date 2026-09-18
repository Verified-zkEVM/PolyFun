# Machines, handlers, and execution

A program describes requests and their continuations. A machine adds an
explicit representation of the state needed to perform that interaction.
A handler determines how the requests are answered. These choices can be
changed independently when the appropriate correspondence is proved.

## Start with a counter

[Machines.lean](../../Examples/Tutorials/Machines.lean) defines a `MooreMachine`
whose state and output are a running total. Feeding it `[1, 2, 3]` from `0`
ends at `6`. Feeding `[1, 2]` exposes the trace `[0, 1, 3]`. Its append theorem
proves that a second input list can be run from the first list's final state.

| Task | Principal interface | Import |
|---|---|---|
| Describe state exposure and update | `PFunctor.DynSystem` | `PolyFun.PFunctor.Dynamical.Basic` |
| Run a Moore machine on inputs | `MooreMachine.run`, `trace` | `PolyFun.PFunctor.Dynamical.Run` |
| Describe arbitrary prefixes and continuing runs | `DynSystem.Prefix`, `Run` | `PolyFun.PFunctor.Dynamical.Run` |
| Initialize a return-capable machine | `DynSystem.DynComputation` | `PolyFun.PFunctor.Dynamical.DynComputation` |
| Interpret a finite query budget | `DynComputation.runWith`, `ImplementsWithin` | `PolyFun.PFunctor.Dynamical.DynComputation.Bounded` |
| Pause and resume a finite query budget | `Chunk`, `unrollChunk`, `runChunk` | `PolyFun.PFunctor.Dynamical.DynComputation.Resumable` |
| Run successive chunks through Lean IO | `DynComputation.runIO` | `PolyFun.PFunctor.Dynamical.DynComputation.IO` |
| Prove safety or simulation | `SafetySpec`, `IsSimulation` | `PolyFun.PFunctor.Dynamical.Safety`, `PolyFun.PFunctor.Dynamical.Simulation` |

## Two kinds of state

The machine's state records control flow and its implementation's private data.
A `Handler (StateT σ m) P` separately threads runtime state through answered
requests. For example, a machine may track its current phase while a handler
maintains an external store or a log. A correctness theorem must say whether it
preserves just the returned value or also that retained handler state.

## Bounds and continuing behavior

A `DynComputation` may run indefinitely. Its `denote` gives a `Resumption`;
qualitative implementation compares that behavior to the chosen specification.
`ImplementsWithin` additionally provides sufficient query fuel for a free
program. The bounded handler laws then recover the result, including effects
retained by a stateful target monad.

Fuel in this API bounds visible machine queries. It is not a general CPU-time
or allocation bound. Costs of answering a request, evaluating local functions,
and transporting data need their own accounting. See [realizability](realizability.md).

## Resumable execution

`unrollChunk` keeps the exact residual machine state when the query budget
runs out. `Chunk.done` carries the returned value; `Chunk.paused` carries
that state. A terminal observation consumes no fuel, including at budget zero.
`resumeChunk` continues a paused chunk and leaves a completed value alone.
`runChunk` interprets the finite program through `Handler m p`.

The public laws connect this interface to bounded execution:

- `unrollChunk_result` and `runChunk_result` recover the bounded observation
  after forgetting residual state.
- `unrollChunk_add` and `runChunk_add` identify successive budgets with their sum.
- `runChunk_natural` transports interpretation along a monad homomorphism,
  preserving the handler's chosen value and effects.

The syntax keeps state, input, result, position, and direction universes
independent. Its observation law uses the universe-polymorphic `FreeM.map`.
Monadic interpretation aligns the state, result, and response universes;
positions and initialization inputs remain independent.

`runIO` executes successive chunks of 128 queries. It retains machine state
across boundaries and propagates IO failures. It makes no termination or
physical-effect correctness claim. The
[driver regressions](../../PolyFunTest/PFunctor/Dynamical/Resumable.lean)
check dependent responses, zero fuel, exact residuals, 257 IO interactions,
and a handler failure immediately after a chunk boundary.

## Typed execution networks

General network runtimes live in `Interaction.Execution`, above the shared
[interface and boundary vocabulary](../../PolyFun/Interaction/Interface.lean).

| Runtime | What it exposes | Entry point |
|---|---|---|
| Reactive processes | Receive, send, local effects, work ticks, and yielding control | [ReactiveProcess](../../PolyFun/Interaction/Execution/ReactiveProcess.lean) |
| Reactive networks | Typed components, routing, a selected environment, and explicit activation schedules | [ReactiveNetwork](../../PolyFun/Interaction/Execution/ReactiveNetwork.lean) |
| Request/reply networks | Stable clients, FIFO delivery, and tickets matching replies to waiting clients | [RequestNetwork](../../PolyFun/Interaction/Execution/RequestNetwork.lean) |
| Open assembly | Compile open composition syntax into finite executable components | [Assembly](../../PolyFun/Interaction/Execution/ReactiveNetwork/Assembly.lean) |

Finite execution does not assume fairness or guarantee eventual delivery.
Requests and physical effects must also be distinguished: a handler's law is
about its mathematical interpretation, while external IO behavior needs its
own contract. Reactive assembly depends on `Interaction.Open.OpenSyntax`;
the elementary process and routing interfaces do not depend on that syntax.

The [open-systems guide](open-systems.md) explains composition and observation.
The [Parliament application](../../Examples/Parliament/README.md) uses the
resumable driver with both a memory backend and terminal/filesystem IO. Its
[runtime contract](../../Examples/Parliament/Docs/runtime.md) separates certified
history extension from the backend's physical behavior.
