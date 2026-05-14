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
indexed-monad shape that `FreeM₂` instantiates.

## File index

| File | Purpose |
|------|---------|
| [`PolyFun/IPFunctor/Basic.lean`](../../PolyFun/IPFunctor/Basic.lean) | `IPFunctor I` structure, `Obj`, `CoeFun`, `Zero`, `One`, `toPFunctor`. |
| [`PolyFun/IPFunctor/Free/Basic.lean`](../../PolyFun/IPFunctor/Free/Basic.lean) | `FreeM P : I → Type v → Type _` — the single-index indexed free monad. `pure`, `roll`, `lift`, `liftA`, `bind` (state-polymorphic continuation), `Functor` / `LawfulFunctor`, `inductionOn`, `construct`, `mapM`, `erase` (forgetful to `PFunctor.FreeM` under `[Unique I]`). |
| [`PolyFun/IPFunctor/Free/Indexed.lean`](../../PolyFun/IPFunctor/Free/Indexed.lean) | `FreeM₂ P : I → I → Type v → Type _` — the two-index variant tracking pre- and post-state. `bind` chains indices positionally; carries `IndexedMonad` and `LawfulIndexedMonad` instances. Forgetful coercion `FreeM₂.toFreeM`. |
| [`PolyFun/IPFunctor/Notation.lean`](../../PolyFun/IPFunctor/Notation.lean) | Lean 4.29 `@[doElem_elab]` overrides making ordinary `do { let x ← e; … }` elaborate to `FreeM.bind`-trees. Custom diagnostics for state mismatches and non-polymorphic remainders. Opt in with `set_option backward.do.legacy false`. |
| [`PolyFun/IPFunctor/Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean) | `do`-notation for `FreeM₂`. Statically-tracked intermediate states; chains of any length compose. Adds the `Pure (FreeM₂ P s s)` instance. |
| [`PolyFun/IPFunctor/Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) | `do`-notation for `FreeM` with a `DeterministicTransitions P` class. Specializes `liftA`-style steps to a concrete post-state, lifting the universal-quantification constraint of the base `Notation.lean`. |
| [`PolyFun/Control/Monad/Indexed.lean`](../../PolyFun/Control/Monad/Indexed.lean) | Atkey indexed-monad class (`IndexedMonad`, `LawfulIndexedMonad`) and the trivial-`Unit` instance. |

## Mental model

### `IPFunctor I`

Read the four fields as: "from state `s`, the agent may select a shape `A s`;
each shape carries a child set `B s a` of legal responses; once the response
`b` is fixed, the state advances to `st s a b`." The state encodes whatever
piece of protocol context determines *which* shapes are next available.

### `FreeM P s α` (single-index)

A well-founded tree starting at state `s` with `α`-leaves. Different branches
can end at *different* leaf states, because `roll`'s state-transition `P.st`
may produce different results for different responses.

Because the leaf state can vary, `FreeM P s α` is **not** a `Monad`: `bind`
takes a state-polymorphic continuation `(s' : I) → α → FreeM P s' β`. Use this
type when post-state is data-dependent.

```lean
protected def bind : {s : I} → FreeM P s α → ((s' : I) → α → FreeM P s' β) → FreeM P s β
```

The induction principle (`FreeM.inductionOn`) takes a state-indexed motive
`C : ∀ s, FreeM P s α → Prop` — necessary because `roll`'s continuation lands
at a different state from its parent.

### `FreeM₂ P s t α` (two-index)

A `FreeM` whose *all* leaves are at the same post-state `t`. Strictly more
restrictive than `FreeM`, but in return:

- `bind` is a genuine indexed bind: `FreeM₂ P s t α → (α → FreeM₂ P t u β) → FreeM₂ P s u β`.
- `FreeM₂` carries a `LawfulIndexedMonad I (FreeM₂ P)` instance, so it can be
  used via the Atkey `ipure` / `ibind` interface.

Use this type when you want static guarantees about the post-state of a
computation (session-typed protocols are the canonical example).

### `FreeM` ↔ `FreeM₂` ↔ `PFunctor.FreeM`

| | `FreeM P s α` | `FreeM₂ P s t α` | `PFunctor.FreeM Q α` |
|---|---|---|---|
| Tracks pre-state | yes | yes | no |
| Tracks post-state | per leaf (data-dependent) | uniformly (static) | n/a |
| Is a `Monad` | no | no (but is `IndexedMonad`) | yes |
| Suitable for `do`-notation | no | via `ipure` / `ibind` | yes |

Forgetful maps:

- `FreeM₂.toFreeM : FreeM₂ P s t α → FreeM P s α` — always available; drops
  the uniform post-state.
- `IPFunctor.FreeM.erase : FreeM P s α → P.toPFunctor.FreeM α` — available
  only when `[Unique I]`; drops the entire indexing.

The reverse directions do not in general exist: `FreeM P s α` may have
non-uniform leaf states (so no single `t` for `FreeM₂`), and re-attaching
non-trivial state information to a `PFunctor.FreeM` requires choosing a
fixed `s`.

## `mapM` and the universe constraint

For both `FreeM` and `FreeM₂`, `mapM` interprets into an ordinary `Monad m`.
Because the responses `P.B s a` live in `Type uB`, the target monad must
operate at that same universe: `m : Type uB → Type w`, and the value type
`α : Type uB`. This mirrors `PFunctor.FreeM.mapM` and is enforced by the
`variable` block at the top of each `mapM` section.

`FreeM₂.mapM` deliberately targets a plain `Monad`, not an `IndexedMonad`,
because `P.st s a b` is data-dependent on `b` and so cannot be threaded
through `ibind`'s static-index signature. If you need state-tracking on the
target side, lift the responses into a state-monad and read the state back.

## Limitations

- `FreeM₂` does not support a general `lift : P.Obj α s → FreeM₂ P s t α`,
  because `lift`'s post-state varies with the response (`P.st s a b`) while
  `FreeM₂` requires a statically chosen `t`. Where this matters, work in
  `FreeM` and convert when post-state becomes known.
- `erase` is gated on `[Unique I]` because the equivalence between
  `IPFunctor I` and `PFunctor` only collapses at that point. An `[Inhabited I]`
  variant is conceivable (picking a designated state) but is not provided.

## `do`-notation flavors

Three parallel `do`-notation files plug into Lean 4.29's extensible
do-elaborator. All require `set_option backward.do.legacy false` and check
the expected monad type before activating, so other monads in the same file
are unaffected.

| File | Monad | Continuation type | When to use |
|---|---|---|---|
| [`Notation.lean`](../../PolyFun/IPFunctor/Notation.lean) | `FreeM P s α` | `(s' : I) → α → FreeM P s' β` (universal) | Tail of the block is state-polymorphic (`pure`/`return`, polymorphic helpers). Custom diagnostics call out state mismatches and non-polymorphic remainders. |
| [`Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean) | `FreeM₂ P s t α` | `α → FreeM₂ P t u β` (statically tracked) | Chains of any length where every step's tree converges to a single post-state. Also adds the `Pure (FreeM₂ P s s)` instance. |
| [`Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) | `FreeM P s α` with `[DeterministicTransitions P]` | `P.B s a → FreeM P (next s a) β` (specialized) | Stay on single-index `FreeM` for downstream compatibility; specialize `liftA`-style steps via the determinism class. |

## What lives where downstream

`IPFunctor` is generic substrate, like `PFunctor`. Downstream usage that
benefits from state-gated interaction (multi-phase oracle protocols, session
types) should sit on top, not inline these constructors. Cryptographic
content remains in [`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io)
per the project policy in [`CLAUDE.md`](../../CLAUDE.md).
