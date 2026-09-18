# From legal inputs to executable effects

Start with the [runnable meeting](../README.md#run-the-example), then read these layers
in order. The full application remains the common example throughout: these semantic
views and instrumented handlers reuse its existing definitions.

## 1. Requests whose responses carry the next state

`JudgmentSig` is a `PFunctor`: a position is a request, and its direction type is a
reply indexed by that exact request. `MeetingP` is an `IPFunctor.Endo` over assembly
states. Its response is an `EnabledInput`, containing a command, successor, events,
and a derivation that the transition is legal. Its source map selects that successor.

`Script` is an indexed free program over this interface. `Script.interpret` uses
`IFreeM.mapM`, retaining a result whose type can depend on the final state. This is
why an arbitrary raw command must go through `checkInput` before becoming a direction.
The ordinary `meetingSystem` uses the same source map as its update operation.

## 2. One execution, two descriptions

[Execution](../Walkthrough/Execution.lean) defines `toPrefix`, translating a
`MeetingPath` into PolyFun's generic `DynSystem.Prefix`. It retains every direction
and has exactly as many steps as the command journal. The proved equations are:

- `toPrefix_last`: the same final assembly state.
- `toPrefix_commands`: the same command sequence, recovered through `commandLabel`.
- `toPrefix_events`: the same events after flattening the labeled receipt batches.

The domain-specific path remains useful for replay and minutes; the generic prefix
makes the same run available to PolyFun's machine theory. There is no second replay
engine and no new generic journal abstraction.

`meetingSafety` packages the machine, a chosen initialized state, and structural
validity as a `SafetySpec`. `prefix_wellFormed` and `meetingSafety_safe` apply to
arbitrary finite choices of certified directions, not only the supplied scenario.
Initialization includes a validity witness, and tests exercise a nonempty accepted
path. This is structural safety of the authored rules, not a proof of substantive
correctness of a human ruling.

## 3. A returning machine and its infinite behavior

The application adds read, judge, persist, publish, and tell effects around the
meeting model. Its `DynComputation.ofStep` representation can either expose one of
those effects or return an exit value. The committed journal stays unchanged while
a candidate is awaiting persistence; successful acknowledgment installs the successor.

[Behavior](../Walkthrough/Behavior.lean) uses the existing machine behavior as a
`Resumption`, then embeds it with `Resumption.toITree`. `behavior_view` identifies the
resumption's destructor with `machineStep`. `behavior_done` observes a returned exit;
`behaviorTree_query` preserves an exposed effect and its dependent response type.
`behaviorTree_tauFree` proves that the embedding inserts no silent transitions.

`chunk_observes_behavior` connects the core resumable driver to this semantics:
forgetting the residual state of an unrolled chunk gives precisely the corresponding
finite truncation of the resumption. Exhausting a budget is an observation boundary,
not a parliamentary adjournment or a claim that the application eventually terminates.
The production runtime continues from the retained state through `runIO`.

## 4. Change the handler, keep the machine

[Handlers](../Walkthrough/Handlers.lean) interprets the same application through
`WriterT (List EffectTag) (StateM Memory)`. `loggedHandler` uses `Handler.withTraceAppend` to delegate every answer to
the existing memory backend and record only the kind of requested effect.

`forgetLog` uses the existing `WriterT.eraseHom` monad homomorphism to discard
this additional log while retaining
the response and the underlying memory changes. `forget_loggedHandler` proves agreement
for one query. The core `runChunk_natural` theorem lifts that fact to every finite
execution: `forget_logged_run` gives exactly the uninstrumented result and backend
state, including residual phases and failures.

For one accepted attendance command followed by `quit`, the log is:

```text
read → persist → tell → read → publish → tell
```

For a failed persistence attempt it is `read → persist → tell`, followed by a failure
exit with unchanged acknowledged history. Persistence errors are response values
inside `StateM`, so the trace added after the response also records a failed
persistence attempt. Both cases run in the regression suite.
The log records requested effects; it does not certify external physical operations.
The real IO handler separately performs terminal interactions, checked writes, and
publication, as described in the [runtime contract](runtime.md).

## Explore the API

This snippet uses only an ordinary import:

```lean
import Examples.Parliament

#check Parliament.Walkthrough.toPrefix_events
#check Parliament.Walkthrough.meetingSafety_safe
#check Parliament.Walkthrough.behaviorTree_query
#check Parliament.Walkthrough.chunk_observes_behavior
#check Parliament.Walkthrough.forget_logged_run
#check PFunctor.DynSystem.DynComputation.runChunk_natural
```

The separate consumer fixture checks these interfaces across a Lake package boundary.
Run `./scripts/validate.sh --lint --test --axioms` to check core laws, the complete
case study, its walkthroughs, and the actual executable together.
