# Indexed Polynomial Functors (`IPFunctor`)

This page is the agent-facing tour of `PolyFun/IPFunctor/`. It is descriptive,
not load-bearing: the source files are the canonical reference. Cite Lean source
by file path plus declaration name when accuracy matters.

## Why indexed polynomial functors

An **indexed polynomial functor** `IPFunctor I` (sometimes called *state-dependent*
or *stateful*) generalizes a `PFunctor` by gating its head shapes and child
types on an ambient state `s : I`:

- `A : I → Type*` — the set of shapes available at state `s`;
- `B : (s : I) → A s → Type*` — the child family;
- `st : (s : I) → (a : A s) → B s a → I` — the state transition triggered by
  picking shape `a` and receiving response `b`.

This is what you reach for when the *allowed* interaction depends on a phase
or session type: multi-phase games whose oracles change after a challenge call,
or two parties handing off control during execution.

When `I` has only one element, `IPFunctor I` collapses to an ordinary
`PFunctor` via `IPFunctor.toPFunctor`. So `IPFunctor` is a strict generalization,
not a replacement.

References:
[`REFERENCES.md`](../../REFERENCES.md). Hancock-Setzer 2000,
Altenkirch-Ghani-Hancock-McBride-Morris 2015 (*Indexed Containers*) — the
indexed/dependent containers literature is the natural home for the state-typed
free monads here. Atkey 2009 (*Parameterised Notions of Computation*) — the
indexed-monad shape that `IPFunctor.FreeM₂` instantiates.

## File index

| File | Purpose |
|------|---------|
| [`PolyFun/IPFunctor/Basic.lean`](../../PolyFun/IPFunctor/Basic.lean) | `IPFunctor I` structure, `Obj`, `CoeFun`, `Zero`, `One`, `toPFunctor`. |
| [`PolyFun/IPFunctor/Free/Basic.lean`](../../PolyFun/IPFunctor/Free/Basic.lean) | `IPFunctor.FreeM P : I → Type v → Type _` — the single-index indexed free monad. `IPFunctor.FreeM.pure`, `roll`, `IPFunctor.FreeM.lift`, `IPFunctor.FreeM.liftA`, `IPFunctor.FreeM.bind` (state-polymorphic continuation), `Functor` / `LawfulFunctor`, `IPFunctor.FreeM.inductionOn`, `IPFunctor.FreeM.construct`, `IPFunctor.FreeM.mapM`, `IPFunctor.FreeM.erase` (forgetful to `PFunctor.FreeM` under `[Unique I]`). |
| [`PolyFun/IPFunctor/Free/Indexed.lean`](../../PolyFun/IPFunctor/Free/Indexed.lean) | `IPFunctor.FreeM₂ P : I → I → Type v → Type _` — the two-index variant tracking pre- and post-state. `IPFunctor.FreeM₂.bind` chains indices positionally; carries `IndexedMonad` and `LawfulIndexedMonad` instances. Forgetful coercion `IPFunctor.FreeM₂.toFreeM`. |
| [`PolyFun/IPFunctor/Notation.lean`](../../PolyFun/IPFunctor/Notation.lean) | Lean 4.29 `@[doElem_elab]` overrides making ordinary `do { let x ← e; … }` elaborate to `IPFunctor.FreeM.bind`-trees. Custom diagnostics for state mismatches and non-polymorphic remainders. Opt in with `set_option backward.do.legacy false`. |
| [`PolyFun/IPFunctor/Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean) | `do`-notation for `IPFunctor.FreeM₂`. Statically-tracked intermediate states; chains of any length compose. Adds the `Pure (IPFunctor.FreeM₂ P s s)` instance. |
| [`PolyFun/IPFunctor/Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) | `do`-notation for `IPFunctor.FreeM` with a `DeterministicTransitions P` class. Specializes `IPFunctor.FreeM.liftA`-style steps to a concrete post-state, lifting the universal-quantification constraint of the base `Notation.lean`. |
| [`PolyFun/IPFunctor/Examples.lean`](../../PolyFun/IPFunctor/Examples.lean) | Worked examples: a two-phase protocol compiled three ways (`IPFunctor.FreeM₂`, deterministic `IPFunctor.FreeM`, Σ-bundled erase via `IPFunctor.FreeM.toSigmaFreeM`), plus a `PFunctor.FreeM.equivW_of_isEmpty` round-trip. Companion to [`ipfunctor-do-notation.md`](ipfunctor-do-notation.md). |
| [`PolyFun/Control/Monad/Indexed.lean`](../../PolyFun/Control/Monad/Indexed.lean) | Atkey indexed-monad class (`IndexedMonad`, `LawfulIndexedMonad`) and the trivial-`Unit` instance. |

## Mental model

### `IPFunctor I`

Read the four fields as: "from state `s`, the agent may select a shape `A s`;
each shape carries a child set `B s a` of legal responses; once the response
`b` is fixed, the state advances to `st s a b`." The state encodes whatever
piece of protocol context determines *which* shapes are next available.

### `IPFunctor.FreeM P s α` (single-index)

A well-founded tree starting at state `s` with `α`-leaves. Different branches
can end at *different* leaf states, because `roll`'s state-transition `P.st`
may produce different results for different responses.

Because the leaf state can vary, `IPFunctor.FreeM P s α` is **not** a `Monad`:
`IPFunctor.FreeM.bind` takes a state-polymorphic continuation
`(s' : I) → α → IPFunctor.FreeM P s' β`. Use this type when post-state is
data-dependent.

```lean
protected def bind :
    {s : I} → IPFunctor.FreeM P s α
      → ((s' : I) → α → IPFunctor.FreeM P s' β) → IPFunctor.FreeM P s β
```

The induction principle (`IPFunctor.FreeM.inductionOn`) takes a state-indexed
motive `C : ∀ s, IPFunctor.FreeM P s α → Prop` — necessary because `roll`'s
continuation lands at a different state from its parent.

### `IPFunctor.FreeM₂ P s t α` (two-index)

An `IPFunctor.FreeM` whose *all* leaves are at the same post-state `t`.
Strictly more restrictive than `IPFunctor.FreeM`, but in return:

- `IPFunctor.FreeM₂.bind` is a genuine indexed bind:
  `IPFunctor.FreeM₂ P s t α → (α → IPFunctor.FreeM₂ P t u β) → IPFunctor.FreeM₂ P s u β`.
- `IPFunctor.FreeM₂` carries a `LawfulIndexedMonad I (IPFunctor.FreeM₂ P)`
  instance, so it can be used via the Atkey `ipure` / `ibind` interface.

Use this type when you want static guarantees about the post-state of a
computation (session-typed protocols are the canonical example).

### `IPFunctor.FreeM` ↔ `IPFunctor.FreeM₂` ↔ `PFunctor.FreeM`

| | `IPFunctor.FreeM P s α` | `IPFunctor.FreeM₂ P s t α` | `PFunctor.FreeM Q α` |
|---|---|---|---|
| Tracks pre-state | yes | yes | no |
| Tracks post-state | per leaf (data-dependent) | uniformly (static) | n/a |
| Is a `Monad` | no | no (but is `IndexedMonad`) | yes |
| Suitable for `do`-notation | no | via `ipure` / `ibind` | yes |

Forgetful maps:

- `IPFunctor.FreeM₂.toFreeM : IPFunctor.FreeM₂ P s t α → IPFunctor.FreeM P s α`
  — always available; drops the uniform post-state.
- `IPFunctor.FreeM.erase : IPFunctor.FreeM P s α → P.toPFunctor.FreeM α` —
  available only when `[Unique I]`; drops the entire indexing.
- `IPFunctor.FreeM.toSigmaFreeM : IPFunctor.FreeM P s α → P.sigmaPFunctor.FreeM α`
  — available for *any* index type; Σ-bundles the originating state into each
  position, so the result sits over `P.sigmaPFunctor` (positions of type
  `Σ s : I, P.A s`) rather than the flat `P.toPFunctor`. Use this when the
  index type is not a `Unique` but you still want to hand the tree to
  `PFunctor`-shaped APIs. Worked example in
  [`Examples.lean`](../../PolyFun/IPFunctor/Examples.lean).

The reverse directions do not in general exist: `IPFunctor.FreeM P s α` may
have non-uniform leaf states (so no single `t` for `IPFunctor.FreeM₂`), and
re-attaching non-trivial state information to a `PFunctor.FreeM` requires
choosing a fixed `s`.

## `mapM` and the universe constraint

For both `IPFunctor.FreeM` and `IPFunctor.FreeM₂`, `mapM` interprets into an
ordinary `Monad m`. Because the responses `P.B s a` live in `Type uB`, the
target monad must operate at that same universe: `m : Type uB → Type w`, and
the value type `α : Type uB`. This mirrors `PFunctor.FreeM.mapM` and is
enforced by the `variable` block at the top of each `mapM` section.

`IPFunctor.FreeM₂.mapM` deliberately targets a plain `Monad`, not an
`IndexedMonad`, because `P.st s a b` is data-dependent on `b` and so cannot
be threaded through `ibind`'s static-index signature. If you need
state-tracking on the target side, lift the responses into a state-monad and
read the state back.

## Limitations

- `IPFunctor.FreeM₂` does not support a general
  `lift : P.Obj α s → IPFunctor.FreeM₂ P s t α`, because `lift`'s post-state
  varies with the response (`P.st s a b`) while `IPFunctor.FreeM₂` requires
  a statically chosen `t`. Where this matters, work in `IPFunctor.FreeM` and
  convert when post-state becomes known.
- `IPFunctor.FreeM.erase` is gated on `[Unique I]` because the equivalence
  between `IPFunctor I` and `PFunctor` only collapses at that point. An
  `[Inhabited I]` variant is conceivable (picking a designated state) but is
  not provided. For arbitrary index types, the Σ-bundled
  `IPFunctor.FreeM.toSigmaFreeM` lifts that restriction at the cost of a
  richer position type — see the *Forgetful maps* list above.

## `do`-notation flavors

Three parallel `do`-notation files plug into Lean 4.29's extensible
do-elaborator. See
[`ipfunctor-do-notation.md`](ipfunctor-do-notation.md) for a worked
walkthrough with a small two-phase-protocol example.

All three require `set_option backward.do.legacy false` and check
the expected monad type before activating, so other monads in the same file
are unaffected.

| File | Monad | Continuation type | When to use |
|---|---|---|---|
| [`Notation.lean`](../../PolyFun/IPFunctor/Notation.lean) | `IPFunctor.FreeM P s α` | `(s' : I) → α → IPFunctor.FreeM P s' β` (universal) | Tail of the block is state-polymorphic (`pure`/`return`, polymorphic helpers). Custom diagnostics call out state mismatches and non-polymorphic remainders. |
| [`Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean) | `IPFunctor.FreeM₂ P s t α` | `α → IPFunctor.FreeM₂ P t u β` (statically tracked) | Chains of any length where every step's tree converges to a single post-state. Also adds the `Pure (IPFunctor.FreeM₂ P s s)` instance. |
| [`Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) | `IPFunctor.FreeM P s α` with `[DeterministicTransitions P]` | `P.B s a → IPFunctor.FreeM P (next s a) β` (specialized) | Stay on single-index `IPFunctor.FreeM` for downstream compatibility; specialize `IPFunctor.FreeM.liftA`-style steps via the determinism class. |

## What lives where downstream

`IPFunctor` is generic substrate, like `PFunctor`. Downstream usage that
benefits from state-gated interaction (multi-phase oracle protocols, session
types) should sit on top, not inline these constructors. Cryptographic
content remains in [`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io)
per the project policy in [`CLAUDE.md`](../../CLAUDE.md).
