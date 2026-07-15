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
| [`PolyFun/ITree/Construct.lean`](../../PolyFun/ITree/Construct.lean) | Standard combinators: `diverge` (Coq `spin`), `forever`, mixed-universe `map` / `cat`, `ignore`, `burn`. Pure consequences of `bind` / `iter` / `M.corec`. |
| [`PolyFun/ITree/Handler.lean`](../../PolyFun/ITree/Handler.lean) | Universe-polymorphic `Handler E F`: choice of an `F`-program for every `E`-event, with identity, lens promotion, and coproduct routing via `Handler.case_`. |
| [`PolyFun/ITree/Sim/Defs.lean`](../../PolyFun/ITree/Sim/Defs.lean) | Universe-polymorphic `ITree.simulate` (interprets every event via a handler), `Handler.comp`, and `ITree.mapSpec` (pure event-renaming via a `PFunctor.Lens`). Coq `interp` analogue. |
| [`PolyFun/ITree/Sim/Facts.lean`](../../PolyFun/ITree/Sim/Facts.lean) | One-step, identity, bind, iteration, lens-composition, and handler-composition facts. Its current weak simulation statements retain homogeneous source/target signatures; independent strong equations retain full universe separation. |
| [`PolyFun/ITree/Rec.lean`](../../PolyFun/ITree/Rec.lean) | `mutualRec`, `fixRec` recursive procedure-call combinators. The `CallE α β` event signature describes one recursive call expecting `α` and returning `β`. |

### Bisimulation

| File | Purpose |
|------|---------|
| [`PolyFun/ITree/Bisim/Defs.lean`](../../PolyFun/ITree/Bisim/Defs.lean) | Universe-polymorphic `ITree.Bisim` (strong / structural equality), relational `ITree.WeakBisimRel RR` (Coq `euttR`), and `ITree.WeakBisim` as its equality specialization (Coq `eutt`). |
| [`PolyFun/ITree/Bisim/Bind.lean`](../../PolyFun/ITree/Bisim/Bind.lean) | Mixed-universe monad/iteration equations plus two-sided relational congruence of `bind` and `map`. |
| [`PolyFun/ITree/Bisim/Equiv.lean`](../../PolyFun/ITree/Bisim/Equiv.lean) | Equivalence properties of bisimulation. |

### Standard events

| File | Purpose |
|------|---------|
| [`PolyFun/ITree/Events/State.lean`](../../PolyFun/ITree/Events/State.lean) | `StateE σ` signature and the `get` / `put` smart constructors. |
| [`PolyFun/ITree/Events/Exception.lean`](../../PolyFun/ITree/Events/Exception.lean) | `ExceptE ε` signature and the `throw` smart constructor; the answer type is `PEmpty`, so execution cannot resume. |

## Mental model

- ITrees are exactly "programs in the signature `F`, including silent
  steps, modulo coinductive equality". They give a single Lean datatype
  that uniformly models pure programs, programs with effects, recursive
  procedures, and partial / non-terminating computations.
- A `Handler E F` is the data needed to interpret one signature inside
  another. `simulate` is the recursive interpretation, `Handler.comp`
  composes interpretations, and `Handler.case_` routes coproduct events.
  `mapSpec` is the syntactically pure case (pure event rename via a
  `PFunctor.Lens`).
- Strong bisimulation `Bisim` is set to definitional equality, courtesy
  of the M-type universal property. `WeakBisimRel RR` ignores finitely many
  leading silent `step`s and compares returns through `RR`; `WeakBisim` is
  the same-type `Eq` specialization used as the ordinary ITree setoid.
- The `Events/{State, Exception}.lean` files are small canonical patterns for
  signatures and smart constructors. Handlers for such signatures can be
  routed, composed, and executed through the generic APIs above.

## Recovering Coq references

Coq file references in module docstrings and Lean comments use the file
names from the upstream
[`DeepSpec/InteractionTrees`](https://github.com/DeepSpec/InteractionTrees)
repository (`Core/ITreeDefinition.v`, `Core/Subevent.v`,
`Core/KTree.v`, `Events/State.v`, `Events/Exception.v`, ...). Treat those
as the canonical algebraic reference; the bibliography entry is
`Xia-Zakowski-He-Hur-Malecha-Pierce-Zdancewic 2020` in
[`REFERENCES.md`](../../REFERENCES.md).
