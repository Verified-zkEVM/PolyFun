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
