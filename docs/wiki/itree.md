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
`F : PFunctor.{u, u}` (shapes are event names, positions are answer types)
so the resulting tree lives at a single universe `u`. ITrees themselves
are the M-type (final coalgebra) of the one-step polynomial functor
`Poly F α` whose shapes are pure leaves, silent steps, or visible queries.

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
| [`PolyFun/ITree/Basic.lean`](../../PolyFun/ITree/Basic.lean) | `ITree F α` defined as `PFunctor.M (Poly F α)`, `Shape` (one-step view), smart constructors `pure` / `step` / `query`, `bind`, `iter`, `Monad` instance. |
| [`PolyFun/ITree/Construct.lean`](../../PolyFun/ITree/Construct.lean) | Standard combinators: `diverge` (Coq `spin`), `forever`, `map`, `cat`, `ignore`, `burn`. Pure consequences of `bind` / `iter` / `M.corec`. |
| [`PolyFun/ITree/Handler.lean`](../../PolyFun/ITree/Handler.lean) | `Handler E F`: choice of `F`-program for every `E`-event. Source data of the simulation operator. |
| [`PolyFun/ITree/Sim/Defs.lean`](../../PolyFun/ITree/Sim/Defs.lean) | `ITree.simulate` (interprets every event via a handler), `ITree.mapSpec` (pure event-renaming via a `PFunctor.Lens`). Coq `interp` analogue. |
| [`PolyFun/ITree/Sim/Facts.lean`](../../PolyFun/ITree/Sim/Facts.lean) | Algebraic facts about simulation. |
| [`PolyFun/ITree/Rec.lean`](../../PolyFun/ITree/Rec.lean) | `mutualRec`, `fixRec` recursive procedure-call combinators. The `CallE α β` event signature describes one recursive call expecting `α` and returning `β`. |

### Bisimulation

| File | Purpose |
|------|---------|
| [`PolyFun/ITree/Bisim/Defs.lean`](../../PolyFun/ITree/Bisim/Defs.lean) | `ITree.Bisim` (strong / structural; coincides with definitional equality by the M-type universal property), `ITree.WeakBisim` (Coq `eutt`, modulo finitely many leading `step` nodes). |
| [`PolyFun/ITree/Bisim/Bind.lean`](../../PolyFun/ITree/Bisim/Bind.lean) | Compatibility of bisimulation with `bind`. |
| [`PolyFun/ITree/Bisim/Equiv.lean`](../../PolyFun/ITree/Bisim/Equiv.lean) | Equivalence properties of bisimulation. |

### Standard events

| File | Purpose |
|------|---------|
| [`PolyFun/ITree/Events/State.lean`](../../PolyFun/ITree/Events/State.lean) | `StateE σ`: `get` / `put`. Standard "state monad as ITree" embedding via a `simulate`-based handler interpreting `StateE σ` over `σ`. |
| [`PolyFun/ITree/Events/Exception.lean`](../../PolyFun/ITree/Events/Exception.lean) | `ExceptE ε`: single `throw e` event with answer type `PEmpty` (no resume). Standard exception monad as ITree. |

## Mental model

- ITrees are exactly "programs in the signature `F`, including silent
  steps, modulo coinductive equality". They give a single Lean datatype
  that uniformly models pure programs, programs with effects, recursive
  procedures, and partial / non-terminating computations.
- A `Handler E F` is the data needed to interpret one signature inside
  another. `simulate` is the recursive interpretation. `mapSpec` is the
  syntactically pure case (pure event rename via a `PFunctor.Lens`).
- Strong bisimulation `Bisim` is set to definitional equality, courtesy
  of the M-type universal property. Reach for `WeakBisim` whenever you
  want to ignore finitely many leading silent `step`s, which is the
  typical "ITree equivalence" used in Coq.
- The `Events/{State, Exception}.lean` files are the small canonical
  examples to read first. They are also the recommended pattern for new
  event signatures: define the polynomial, write a `Handler`, prove the
  small algebraic facts you need.

## Recovering Coq references

Coq file references in module docstrings and Lean comments use the file
names from the upstream
[`DeepSpec/InteractionTrees`](https://github.com/DeepSpec/InteractionTrees)
repository (`Core/ITreeDefinition.v`, `Core/Subevent.v`,
`Core/KTree.v`, `Events/State.v`, `Events/Exception.v`, ...). Treat those
as the canonical algebraic reference; the bibliography entry is
`Xia-Zakowski-He-Hur-Malecha-Pierce-Zdancewic 2020` in
[`REFERENCES.md`](../../REFERENCES.md).
