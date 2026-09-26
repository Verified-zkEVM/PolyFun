# Interaction Trees

`PolyFun/ITree/` adapts *Interaction Trees: Representing Recursive and Impure Programs
in Coq* (Xia, Zakowski, He, Hur, Malecha, Pierce, Zdancewic, POPL 2020).

## Why ITrees

Interaction Trees (ITrees) are a coinductive datatype for representing
recursive and impure programs that interact with an environment through a
fixed set of events. Coq's presentation is

```coq
CoInductive itree (E : Type → Type) (R : Type) :=
| Ret (r : R)
| Tau (t : itree E R)
| Vis {X : Type} (e : E X) (k : X → itree E R).
```

In Lean we model the event signature as a *polynomial functor*
`F : PFunctor.{uA, uB}`: its positions are event names and its directions are
answer types. The event-position, event-direction, and return universes are
independent. The raw carrier is the M-type (final coalgebra) of the
operation-first polynomial `ITree.Poly F α := F + C α + y`. `ITree F α` is
a one-field wrapper whose `toM`/`ofM` maps are definitionally inverse. The
shape-indexed `ITree.ViewPoly F α` supplies the ergonomic pure/step/query view.

For `α : Type uR`, the public universe contract is:

```lean
ITree.Shape F α : Type (max uA uR)
ITree.Poly F α  : PFunctor.{max uA uR, uB}
ITree.ViewPoly F α : PFunctor.{max uA uR, uB}
ITree F α       : Type (max uA uB uR)
```

The empty direction type of a pure leaf and the unit direction type of a silent
step are lifted to `uB`; a visible query retains its original direction type.

| Coq | Lean |
|---|---|
| `itree E R` | `ITree F α` |
| `itreeF E R T` | `ITree.Shape F α` |
| `RetF` / `Ret` | `ITree.Shape.pure` / `ITree.pure` |
| `TauF` / `Tau` | `ITree.Shape.step` / `ITree.step` |
| `VisF` / `Vis` | `ITree.Shape.query` / `ITree.query` |

## Where to start

| Task | Entry point |
|---|---|
| Construct and observe a tree | [Basic](../../PolyFun/ITree/Basic.lean), [tutorial](../tutorials/interaction-trees.md) |
| Run a tree in another monad | [Interpretation](../../PolyFun/ITree/Interp/Defs.lean), [state handler](../../PolyFun/ITree/Interp/State.lean) |
| Reason modulo finite silent steps | [Bisimulation definitions](../../PolyFun/ITree/Bisim/Defs.lean), [bisimulation guide](bisimulation.md) |
| Compare different event signatures | [Cross-signature relations](../../PolyFun/ITree/Bisim/CrossSignature.lean) |
| Run guarded loops in `do` notation | [Do](../../PolyFun/ITree/Do.lean) |
| Choose between ITrees and other models | [Computation models](computation-models.md) |

The Lean representation uses Mathlib's M-type. Familiarity with the Coq
library helps with the algebra, but Lean constructors and universe parameters
follow the polynomial event interface described below.

## Mental model

- ITrees are exactly "programs in the signature `F`, including silent
  steps, modulo coinductive equality". They give a single Lean datatype
  that uniformly models pure programs, programs with effects, recursive
  procedures, and partial / non-terminating computations.
- The fixed-point bridge is explicit: `FreeM P α` is `W (P + C α)`;
  `Resumption P α` is `M (P + C α)`; and `ITree P α` is equivalently
  `Resumption (P + y) α`. Thus finite programs embed as the well-founded,
  tau-free fragment, while arbitrary ITrees use the same resumption boundary
  with `y` recording silent steps.
- Lean's core `whileM` has the same continue/terminate protocol as `ITree.iter`
  but uses generic partial recursion and requires an inhabited result type.
  Import `PolyFun.ITree.Do` and write `open scoped ITree` to make `while`
  inside an `ITree` `do` block use the guarded `ITree.iter` implementation.
- A `Handler E F` is the data needed to interpret one signature inside
  another. `simulate` is the recursive interpretation, `Handler.comp`
  composes interpretations, and `Handler.case_` routes coproduct events.
  `mapSpec` is the syntactically pure case (pure event rename via a
  `PFunctor.Lens`).
- Strong bisimulation `Bisim` is set to Lean equality, courtesy
  of the M-type universal property. `WeakBisimRel resultRel` ignores finitely many
  leading silent `step`s and compares returns through `resultRel`; `WeakBisim` is
  the same-type `Eq` specialization used as the ordinary ITree setoid.
- `CrossSignatureWeakBisim eventRel resultRel` generalizes `WeakBisimRel` to
  two different event signatures. `eventRel.event` relates event names and
  `eventRel.reply` dependently relates their replies. The identity event-signature
  relation recovers `WeakBisimRel` exactly, while `EventSignatureRel.ofLens`
  relates every tree to its `mapSpec` image. The current API
  adds only coinduction and congruence principles used by concrete consumers;
  it intentionally does not duplicate the upstream Paco up-to tower.
- State and exception are the current interpreted effect libraries. Other
  event signatures can be supplied as polynomials with their own handlers.
- `ITree.toLTS F α` has states `Option (ITree F α)`, with `none` as the
  terminal state after a return. Its finite traces ignore silent steps and
  observe `Observation.event a reply` and `Observation.ret result`. Thus a
  trace records which reply selected each query continuation and whether the
  observed prefix terminated. The generic `Control.LTS.WeakTrace` semantics
  is preserved by weak simulation, so `WeakBisim`-related trees have equal
  trace sets.
- The state and exception runners are direct productive corecursors. State
  operations become one silent step while threading the current state;
  exceptions terminate as `Except.error`; untouched external events remain
  visible. Their facts files expose exact computation and bind laws.
- Recursive calls separate input, result, external-event, and final-result
  universes. `mutualRec` and `fixRec` retain one local equality: recursive and
  external replies share a universe because the current `PFunctor.sum`
  representation requires it. No other ITree API inherits that constraint.

## Interpreting into a monad

`ITree.interp h t` ([`ITree/Interp/Defs.lean`](../../PolyFun/ITree/Interp/Defs.lean))
runs a tree over `E` in any iterative monad `m`, answering each event through a
handler `h : PFunctor.Handler m E`. It is Coq's `interp`: one `iterM` loop that
returns at a leaf, continues past a silent step, and asks the handler at a
query. Interpreting into another interaction tree is `simulate` by definition
(`interp_eq_simulate`), so the strong computation equations and the weak
bisimulation laws of simulation transfer to it
([`Interp/Sim.lean`](../../PolyFun/ITree/Interp/Sim.lean)); the general form
adds `StateT σ (ITree F)`, `OptionT (ITree F)`, and any other lawful iterative
monad as targets. The loop state forces one universe: `E : PFunctor.{u, u}`,
`α : Type u`, `m : Type u → Type v`; `simulate` keeps its independent universes.

The laws hold up to the target's iteration equivalence
([`Interp/Laws.lean`](../../PolyFun/ITree/Interp/Laws.lean)): `interp_pure`,
`interp_step`, `interp_query`, `interp_lift`, and `interp_bind`. The last is
the one that needs uniformity: the interpreted loop of `t >>= k` is run as a
two-phase loop whose state is a residual of `t` or of some `k a`; uniformity
identifies it with the loop of the sequenced tree, the codiagonal law splits it
into an outer loop over an inner one, and naturality identifies the inner loops
with `interp h t` and `interp h (k a)`. `liftHandler` leaves events in place up
to a monad lift, so a handler for a sum `E + F` that interprets `E` and lifts
`F` keeps the `F` events visible in the target tree.
[`Interp/State.lean`](../../PolyFun/ITree/Interp/State.lean) does this for
state: `StateE.stateHandler` answers `get` and `put` in `StateT σ (ITree E)`
and lifts the remaining events, and `interpState_weakBisimRel_interp` shows it
agrees with the direct corecursor `interpState` up to weak bisimulation and the
order of the returned pair. The corecursor keeps its exact computation rules;
the handler form is the one that composes with other iterative targets.

## Iterative monads

`ITree.iter` is an instance of the `MonadIter` interface in
[`Control/Monad/Iter.lean`](../../PolyFun/Control/Monad/Iter.lean): a monad
with a uniform loop combinator `iterM : (β → m (β ⊕ α)) → β → m α`. Its lawful
version, `LawfulMonadIter`, states the Elgot laws (the four Conway laws and
uniformity) over a monad-specific equivalence; for interaction trees that
equivalence is weak bisimulation, because every loop step inserts a silent
guard. [`Control/Monad/Iter/Instances.lean`](../../PolyFun/Control/Monad/Iter/Instances.lean)
makes `StateT`, `ReaderT`, `ExceptT`, and `OptionT` over an iterative monad
iterative, with `run_iterM` equations by definition, and proves the state and
reader transformers lawful over a lawful base, so `StateT σ (ITree F)` and
`ReaderT ρ (ITree F)` carry the same loop laws as `ITree F`.

## Recovering Coq references

Coq file references in module docstrings and Lean comments use the file
names from the upstream
[`DeepSpec/InteractionTrees`](https://github.com/DeepSpec/InteractionTrees)
repository (`Core/ITreeDefinition.v`, `Core/Subevent.v`,
`Core/KTree.v`, `Events/State.v`, `Events/Exception.v`, ...). Treat those
as the canonical algebraic reference; the bibliography entry is
`Xia-Zakowski-He-Hur-Malecha-Pierce-Zdancewic 2020` in
[`REFERENCES.md`](../../REFERENCES.md).

## Relational transition-system theory

`Control.LTS.toLts` forgets the witness move and connects the polynomial
transition system to cslib. Strong and weak simulation composition, silent and
saturated transition transport, and finite-trace transport use cslib's generic
theorems through the public correspondences. Delay simulation retains its
separate silent-prefix-only semantics.

`Control.LTS.WeakTrace` keeps a visible-label induction API for ITree proofs.
Its cslib interpretation is `MTr` of the saturated system with `List.map some`
on labels. In particular, `WeakTrace.nil_iff` requires equal endpoints; it does
not quotient the empty trace by silent reachability. Trace concatenation and
simulation transport use that interpretation.

## Executable case study

The [Parliament behavior walkthrough](../../Examples/Parliament/Docs/walkthrough.md)
uses `DynComputation` behavior and `Resumption.toITree` to present the live application
as a tau-free interaction tree. It proves query/return observations and relates finite
chunks to resumption truncation; this does not require the meeting to terminate.
