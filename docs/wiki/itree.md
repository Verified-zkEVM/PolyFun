# Interaction Trees

This page is the agent-facing tour of `PolyFun/ITree/`. It tracks the Lean
adaptation of *Interaction Trees: Representing Recursive and Impure Programs
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
independent. ITrees themselves are the M-type (final coalgebra) of the one-step
polynomial functor `Poly F α` whose positions are pure leaves, silent steps, or
visible queries.

For `α : Type uR`, the public universe contract is:

```lean
ITree.Shape F α : Type (max uA uR)
ITree.Poly F α  : PFunctor.{max uA uR, uB}
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

## File index

### Core

| File | Purpose |
|------|---------|
| [`PolyFun/ITree/Basic.lean`](../../PolyFun/ITree/Basic.lean) | `ITree F α` defined as `PFunctor.M (Poly F α)`, `Shape` (one-step view), smart constructors `pure` / `step` / `query`, mixed-universe named `bind`, `iter`, and the homogeneous `Monad` instance. |
| [`PolyFun/ITree/Do.lean`](../../PolyFun/ITree/Do.lean) | Opt-in `open scoped ITree` integration that sends Lean `while` notation through productive `ITree.iter` instead of core partial `whileM`. |
| [`PolyFun/ITree/Construct.lean`](../../PolyFun/ITree/Construct.lean) | Standard combinators: `diverge` (Coq `spin`), `forever`, mixed-universe `map` / `cat`, `ignore`, `burn`. Pure consequences of `bind` / `iter` / `M.corec`. |
| [`PolyFun/ITree/Handler.lean`](../../PolyFun/ITree/Handler.lean) | Universe-polymorphic `Handler E F`: choice of an `F`-program for every `E`-event, with identity, lens promotion, and coproduct routing via `Handler.case_`. |
| [`PolyFun/ITree/Sim/Defs.lean`](../../PolyFun/ITree/Sim/Defs.lean) | Universe-polymorphic `ITree.simulate` (interprets every event via a handler), `Handler.comp`, and `ITree.mapSpec` (pure event-renaming via a `PFunctor.Lens`). Coq `interp` analogue. |
| [`PolyFun/ITree/Sim/Facts.lean`](../../PolyFun/ITree/Sim/Facts.lean) | Universe-polymorphic one-step, identity, relational congruence, bind, iteration, lens-composition, and handler-composition facts. `simulate_comp` identifies sequential and composite interpretation up to weak bisimulation; `Handler.comp_assoc_apply` gives pointwise associativity. |
| [`PolyFun/ITree/Rec.lean`](../../PolyFun/ITree/Rec.lean) | Universe-polymorphic `mutualRec`, `fixRec` recursive procedure-call combinators. `CallE α β : PFunctor.{uα,uβ}` separates call inputs from results; recursive coproducts retain only the equal reply-universe constraint of `PFunctor.sum`. |
| [`PolyFun/ITree/Rec/Facts.lean`](../../PolyFun/ITree/Rec/Facts.lean) | Exact head equations for `interpMrec`, bind compatibility, external-event renaming naturality, and the guarded characteristic equations for `mutualRec` / `fixRec`. |

### Bisimulation

| File | Purpose |
|------|---------|
| [`PolyFun/ITree/Bisim/Defs.lean`](../../PolyFun/ITree/Bisim/Defs.lean) | Universe-polymorphic `ITree.Bisim` (strong / structural equality), relational `ITree.WeakBisimRel RR` (Coq `euttR`), and `ITree.WeakBisim` as its equality specialization (Coq `eutt`). |
| [`PolyFun/ITree/Bisim/Bind.lean`](../../PolyFun/ITree/Bisim/Bind.lean) | Mixed-universe monad/iteration equations, the homogeneous `LawfulMonad` instance, and two-sided relational congruence of `bind` and `map`. |
| [`PolyFun/ITree/Bisim/Equiv.lean`](../../PolyFun/ITree/Bisim/Equiv.lean) | Equivalence properties of bisimulation. |
| [`PolyFun/ITree/Bisim/Iter.lean`](../../PolyFun/ITree/Bisim/Iter.lean) | Relational iteration congruence and the `LawfulMonadIter` instance over `WeakBisim`, including unfolding, naturality, dinaturality, and codiagonal laws. |

### Standard events

| File | Purpose |
|------|---------|
| [`PolyFun/ITree/Events/State.lean`](../../PolyFun/ITree/Events/State.lean) | `StateE σ`, `get` / `put`, and the direct `interpState` / `runState` runner from `ITree (StateE σ + E) α` to `σ → ITree E (σ × α)`. Positions and replies genuinely share `uσ` because `get` returns `σ`; final computation results remain independent. |
| [`PolyFun/ITree/Events/StateFacts.lean`](../../PolyFun/ITree/Events/StateFacts.lean) | Exact computation rules for returns, steps, `get`, `put`, and external queries, plus the state-transformer bind law. |
| [`PolyFun/ITree/Events/Exception.lean`](../../PolyFun/ITree/Events/Exception.lean) | `ExceptE ε : PFunctor.{uε,uB}`, `throw`, and the direct `interpExcept` / `runExcept` runner to `ITree E (Except ε α)`; exception, reply, and final-result universes remain independent. |
| [`PolyFun/ITree/Events/ExceptionFacts.lean`](../../PolyFun/ITree/Events/ExceptionFacts.lean) | Exact computation rules for returns, steps, throws, and external queries, plus the exception-transformer bind law. |

## Mental model

- ITrees are exactly "programs in the signature `F`, including silent
  steps, modulo coinductive equality". They give a single Lean datatype
  that uniformly models pure programs, programs with effects, recursive
  procedures, and partial / non-terminating computations.
- Lean's core `whileM` has the same continue/terminate protocol as `ITree.iter`
  but uses generic partial recursion and requires an inhabited result type.
  Import `PolyFun.ITree.Do` and write `open scoped ITree` to make `while`
  inside an `ITree` `do` block use the guarded `ITree.iter` implementation.
- A `Handler E F` is the data needed to interpret one signature inside
  another. `simulate` is the recursive interpretation, `Handler.comp`
  composes interpretations, and `Handler.case_` routes coproduct events.
  `mapSpec` is the syntactically pure case (pure event rename via a
  `PFunctor.Lens`).
- Strong bisimulation `Bisim` is set to definitional equality, courtesy
  of the M-type universal property. `WeakBisimRel RR` ignores finitely many
  leading silent `step`s and compares returns through `RR`; `WeakBisim` is
  the same-type `Eq` specialization used as the ordinary ITree setoid.
- The state and exception runners are direct productive corecursors. State
  operations become one silent step while threading the current state;
  exceptions terminate as `Except.error`; untouched external events remain
  visible. Their facts files expose exact computation and bind laws.
- Recursive calls separate input, result, external-event, and final-result
  universes. `mutualRec` and `fixRec` retain one local equality: recursive and
  external replies share a universe because the current `PFunctor.sum`
  representation requires it. No other ITree API inherits that constraint.

## Recovering Coq references

Coq file references in module docstrings and Lean comments use the file
names from the upstream
[`DeepSpec/InteractionTrees`](https://github.com/DeepSpec/InteractionTrees)
repository (`Core/ITreeDefinition.v`, `Core/Subevent.v`,
`Core/KTree.v`, `Events/State.v`, `Events/Exception.v`, ...). Treat those
as the canonical algebraic reference; the bibliography entry is
`Xia-Zakowski-He-Hur-Malecha-Pierce-Zdancewic 2020` in
[`REFERENCES.md`](../../REFERENCES.md).
