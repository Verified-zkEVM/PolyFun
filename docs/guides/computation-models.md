# Choosing a computation model

All these models use typed requests and responses, but they retain different
information. Choose the model that exposes what your theorem needs.

| Need | Model | What the value contains | Main import |
|---|---|---|---|
| Induction over a program and its possible answers | `PFunctor.FreeM P α` | A well-founded tree of requests and returned values | `PolyFun.PFunctor.Free.Basic` |
| Continuing interaction with possible returns | `PFunctor.Resumption P α` | A potentially infinite request/return tree, without silent steps | `PolyFun.PFunctor.Resumption` |
| Recursive effectful programs with internal steps | `ITree P α` | Returns, visible requests, and silent `step` nodes | `PolyFun.ITree.Basic` |
| State transitions that keep interacting | `PFunctor.DynSystem S P` | An exposed request and an answer-dependent state update | `PolyFun.PFunctor.Dynamical.Basic` |
| A machine initialized by an input that may return | `PFunctor.DynSystem.DynComputation P α β` | Hidden state, initialization, and return-or-query behavior | `PolyFun.PFunctor.Dynamical.DynComputation` |
| Requests whose availability depends on state | `IPFunctor.Endo I`, `IFreeM`, `FreeM₂` | Indexed interfaces, state transitions, and indexed results | `PolyFun.IPFunctor.Free.Indexed` |

A well-founded request tree need not have one finite bound on the lengths of
all its branches. A request interface can have infinitely many possible
responses. A handler can also introduce its own effects or nontermination;
well-founded syntax alone does not certify arbitrary external execution.

## Interfaces, programs, and protocol shapes

A polynomial interface `P` specifies requests `P.A` and responses `P.B a`.
`FreeM P α` is a program over that fixed interface. A `Handler m P` chooses
an effectful answer to each request, and `FreeM.liftM` interprets the program.

`Interaction.TypeTree` instead describes a sequence of move types whose later
shape can depend on earlier moves. Its generating polynomial has types as
positions and their inhabitants as directions. Decorations attach roles,
observations, or computations to nodes. A type tree is not a flat event
signature, and its shape alone does not specify a strategy or an execution.
See [interaction](interaction.md).

## Connections and their proof boundaries

| Connection | Available meaning | Source |
|---|---|---|
| `FreeM P α` and `W (P + C α)` | An equivalence with the well-founded return-or-query tree | [Free basics](../../PolyFun/PFunctor/Free/Basic.lean) |
| Free program to resumption | Constructor-preserving embedding; its image is the well-founded fragment | [Embedding](../../PolyFun/PFunctor/Free/Resumption.lean), [well-foundedness](../../PolyFun/PFunctor/Resumption/WellFounded.lean) |
| Resumption to ITree | An embedding introducing no silent steps | [Resumption bridge](../../PolyFun/ITree/Resumption.lean) |
| ITree and resumption over `P + y` | An equivalence recording each silent step as a unary event | [Silent-step bridge](../../PolyFun/ITree/ResumptionWithTau.lean) |
| Free-handler interpretation and ITree interpretation | Correspondence up to weak bisimulation, accounting for interpreter steps | [Free-program bridge](../../PolyFun/ITree/Free.lean) |
| Explicit-state machine to behavior | Unfolding forgets the internal state representation | [Behavior and trajectories](../../PolyFun/PFunctor/Dynamical/Trajectory.lean), [returning computations](../../PolyFun/PFunctor/Dynamical/DynComputation.lean) |
| Machine to free program | `Implements` relates behavior; `ImplementsWithin` supplies a finite query budget for execution laws | [Bounded computations](../../PolyFun/PFunctor/Dynamical/DynComputation/Bounded.lean) |

The corresponding tree presentations are equivalences or embeddings as named
by their declarations, not interchangeable definitional equalities. A structural
bridge states which result, trace, state, or behavior it preserves. Probability
and execution-cost preservation require additional interpretations and evidence.

## Equality and observation

Strong ITree bisimulation coincides with Lean equality. Weak bisimulation is a
separate relation accounting for silent steps; arbitrary silent divergence must
not be erased by an informal appeal to observable behavior. Machine simulations
can relate different internal state types. Open-system observations compare
closed systems through an explicitly chosen relation.

Use the [bisimulation guide](bisimulation.md) to select the actual relation before
stating an equivalence theorem. The [execution guide](execution.md) explains
handler state and fuel, and [realizability](realizability.md) adds admissibility
and resource obligations to a machine implementation.

## Composed stateful services

[`MachineHandler`](../../PolyFun/PFunctor/Handler/Machine/Defs.lean) is a family
`(a : P.A) → DynComputation Q S (P.B a × S)`. It adds no computation syntax:
`toHandler` forgets private machine state and produces the existing
`Handler.Stateful (Resumption Q) S P`, and `execute` uses that handler's free fold.

`dispatch` composes an arbitrary caller machine with the service. Its retained
`Phase` contains either the caller state and shared service state, or an active
operation's private machine state and a `Pending` caller state with evidence
for its operation. Resuming recovers the dependent continuation from that state. Entry and return are unary administrative events; primitive
queries keep their original answer types. `compile` specializes this same
construction to `DynComputation.ofFreeM`. The existing `startChunk` and
`continueChunk` runners preserve these phases across pauses.

[`dispatch_weakBisim_interp`](../../PolyFun/PFunctor/Handler/Machine/Behavior.lean)
identifies dispatch with ITree interpretation in `StateT`. Its finite-client
specialization, `compile_weakBisim_execute`, identifies the composed machine
with the resumption handler fold. Neither requires a uniform client-depth
bound or handler termination. Weak bisimulation hides administrative steps;
it does not preserve fuel counts or timing observations. Service calls,
primitive queries, and administrative transitions are distinct costs.

[Dispatcher prefix decomposition](../../PolyFun/PFunctor/Handler/Machine/Trace.lean)
retains every completed call's exact service trace and any unfinished call.
`DispatchPrefix.decompose` computes this view of an ordinary `ExecutionTrace`;
`toTrace_decompose` proves exact reconstruction. Completed answers also form a
typed caller trace. Each completed call contributes its primitive transitions
and two administrative ticks. An unfinished call contributes its entry tick and
all work performed so far, including when the service has returned but dispatch
has not yet resumed the caller.

The same decomposition preserves ordered monoidal observations. Entry, body and
return remain separate, without a commutativity assumption. The
[quantitative observation bridge](../../PolyFun/Realizability/Quantitative/TraceCost.lean)
identifies the existing realization's cost with this shared observation fold,
then adds initialization and final observation exactly once. Its representations
and code costs come from the supplied `QuantitativeRealization`; structural
query counts alone do not establish a backend runtime bound.

`capped` instead returns an `OptionT (FreeM Q)` implementation of each operation.
A timeout permanently aborts the client. It neither restarts nor renormalizes
that call. This is useful when a consumer requires finite syntax with an
explicit failure outcome; chunking remains the API for retaining unfinished work.

`admitted` uses core `ExceptT` over `StateT` to retain service and admission state
on permanent abort. The [exception-answer adapter](../../PolyFun/PFunctor/Free/Except.lean)
exposes `Except ε (P.B a)` as an ordinary dependent answer type. `FreeM.withExcept`
stops at the first error, and `liftM_withExcept` identifies its fold with the
core transformer interpretation. Consumers can reuse laws for ordinary finite
clients while keeping error tags and final state. The syntax permits independent
answer, error and result universes.

| Consumer requirement | Model and existing bridge |
|---|---|
| Well-founded adaptive client | `FreeM`, `Handler.Stateful.run`, `MachineHandler.compile` |
| Possibly infinite visible behavior | `Resumption`, `toITree`, continuous `denote` |
| Recursion and silent divergence | `ITree`, stateful `interp`, weak bisimulation |
| Executable retained state | `DynComputation`, `dispatch`, resumable runners |
| Continuing interaction and paths | `DynSystem.behavior`, `trajectory`, M/cofree bridges |
| State-indexed legal operations | Indexed free models and their existing sigma erasure |

Indexed models already retain terminal-state information through
`IFreeM.toSigmaFreeM`; a state-indexed protocol consumer can use that bridge
before adding another interpreter. The service construction here is for an
ordinary dependent answer interface. Protocol legality, measurable stochastic
transitions, and cost certificates remain separate obligations.
