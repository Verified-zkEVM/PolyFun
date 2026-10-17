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
| Pause and resume a finite query budget | `Chunk`, `unrollChunk`, `runChunk`, `startChunk`, `continueChunk` | `PolyFun.PFunctor.Dynamical.DynComputation.Resumable` |
| Run successive chunks through Lean IO | `DynComputation.runIO` | `PolyFun.PFunctor.Dynamical.DynComputation.IO` |
| Prove safety or simulation | `SafetySpec`, `IsSimulation` | `PolyFun.PFunctor.Dynamical.Safety`, `PolyFun.PFunctor.Dynamical.Simulation` |

## Two kinds of state

The machine's state records control flow and its implementation's private data.
A `Handler (StateT σ m) P` separately threads runtime state through answered
requests. For example, a machine may track its current phase while a handler
maintains an external store or a log. A correctness theorem must say whether it
preserves just the returned value or also that retained handler state.

Stateful handlers compose the way effect stacks do
([`Handler/Stateful/Combinators.lean`](../../PolyFun/PFunctor/Handler/Stateful/Combinators.lean)):
`parallel` and `pi` run handlers for the summands of `P + Q` or of an indexed
sum on a product state, `flatten` reassociates a handler over a stateful base
into one product state, `mapBase` interprets a handler's base free monad through
an outer handler, and `extend` / `extendLeft` add a passive auxiliary component
that `fixSnd` projects away. Each has a run law relating `Stateful.run` through
the combinator to the runs of its parts; their common core,
`run_map_eq_of_apply_map_eq`, says that a state projection which commutes with
every single request commutes with every run.

A `StateLens` ([`Handler/StateLens.lean`](../../PolyFun/PFunctor/Handler/StateLens.lean))
is the stateful handler that answers every request with exactly one inner
request; its substitution is `Stateful.run` of its handler (`mapFreeM_eq_run`).
`DynComputation.wrapState` runs a machine against it as one product machine, and
the [realizability guide](realizability.md#stateful-handler-substitution) bounds
the cost of that substitution.

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

For interaction trees, import `PolyFun.ITree.Machine`: `ITree.toDynComputation` uses the
resumption-with-tau representation, and `ITree.withSilentSteps` lifts a visible-event handler
to it. Visible events and silent steps both consume the budget; a silent step never invokes
the visible handler.

The public laws connect this interface to bounded execution:

- `unrollChunk_result` and `runChunk_result` recover the bounded observation
  after forgetting residual state.
- `unrollChunk_add` and `runChunk_add` identify successive budgets with their sum.
- `runChunk_natural` transports interpretation along a monad homomorphism,
  preserving the handler's chosen value and effects.

Use `startChunk handler fuel input` to initialize a machine from its input and interpret the
first chunk, and `continueChunk handler fuel chunk` for the next chunk of either a paused or a
completed result. Neither requires reconstructing the machine's hidden state.
`startChunk_continueChunk` equates consecutive budgets with their sum, including the exact
residual, and `startChunk_zero` shows that zero fuel still observes a terminal state.

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

## Deterministic language transitions

`Control.Transition S R` describes a next-state function returning either a result
or a residual state. `run_add` preserves exact residuals across chunks; `Executes`
is equivalent to successful finite fuel and has a unique result. Here each call
to the transition function consumes one tick, including a terminal transition.

`PolyFun.ITree.Transition` supplies a pure ITree and a `DynComputation` over the
unit interface. The machine stores `R ⊕ S`, so it performs a tick to discover a
terminal result and then observes that result without further fuel.
`runChunk_toMachine` proves agreement at every budget, including zero. This
explicit convention reconciles transition fuel with the existing machine API.
Frontend error results stay results; a paused state is not a proof of divergence.

The [interop guide](interop.md) gives the strict scoped-language example and the
relationship to frontend adequacy and resource certificates.

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

`RequestNetwork.State.initial` starts every client ready, with no traffic and a fresh ticket
counter. `ClientState.result` observes only a returned client and leaves the network's queue
and transcript in place.

`HandledDiagram.initial`, `runToken` and `runFIFO` execute a diagram with its intrinsic
handlers and return complete residual states. Their `runToken_add` and `runFIFO_append` laws
preserve local state, inboxes, pending traffic, outputs and elapsed activations across a split,
for every lawful ambient monad, so a caller can pause after an effect without repeating it.
They delegate to the network runners rather than introducing a second interpreter;
`tokenObservation_eq` and `fifoObservation_eq` identify the terminal observations with these
runners from `initial`. `ReactiveNetwork.State.ext` compares all retained fields.

The [open-systems guide](open-systems.md) explains composition and observation.
The [Parliament application](../../Examples/Parliament/README.md) uses the
resumable driver with both a memory backend and terminal/filesystem IO. Its
[runtime contract](../../Examples/Parliament/Docs/runtime.md) separates certified
history extension from the backend's physical behavior.

The [proved walkthrough](../../Examples/Parliament/Docs/walkthrough.md) connects
certified meeting paths to generic prefixes, proves safety for arbitrary legal
inputs, and relates finite execution to resumption and interaction-tree semantics.
It also uses `Handler.withTraceAppend` and `WriterT.eraseHom` to instrument the
same application and prove that erasing its log preserves the result and memory.

## Composing effects and inspecting alternatives

`Handler.sum` interprets dependent responses from either side of a coproduct. `Lens.inl` and
`Lens.inr` embed a component program; `Handler.liftM_sum_mapLens_inl` and its right-side
counterpart show that interpreting the embedding uses only the corresponding handler.
`Handler.mapTarget_sum` preserves this separation when changing target monads.

For one-or-both interfaces, `Handler.parallelSeq` executes a joint request left first. This is
an explicit interpretation order, not OS parallelism or a commutativity guarantee. Arbitrary
free-handler composition can change which requests synchronize, so unrestricted interchange is
not promised.

`Occurrence.completeWith answer` supplies the selected query's answer and executes its suffix.
`Cursor.forkAtWith` executes a shared prefix once, then supplies two answers and retains both
typed completions. It does not ask the handler for either selected answer. **Both suffixes
still execute their effects independently**: this is not rollback or automatic state
isolation, so speculative callers should fork over a read-only interface.
