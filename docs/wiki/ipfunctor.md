# Indexed Polynomial Functors (`IPFunctor`)

This page is the agent-facing tour of `PolyFun/IPFunctor/`. It is descriptive,
not load-bearing: the source files are the canonical reference. Cite Lean source
by file path plus declaration name when accuracy matters.

## Why indexed polynomial functors

A **two-index polynomial functor** `IPFunctor I J` is the container form of a
functor between indexed family categories `(I → Type) → (J → Type)`,
corresponding to the polynomial diagram

```
I ←—— E ——▶ B ——▶ J
```

Equivalently, the data is

- `A : J → Type*` — the head shapes available at each output index `j : J`;
- `B : (j : J) → A j → Type*` — the child family for each shape;
- `src : (j : J) → (a : A j) → B j a → I` — the *source* index in `I` from
  which each child is drawn.

The associated object action is

```
P.Obj X j = Σ a : P.A j, (b : P.B j a) → X (P.src j a b)
```

so a child at position `(j, a, b)` lives in the fiber `X (P.src j a b)`.

The **endomorphic specialization** `IPFunctor.Endo I := IPFunctor I I` is the
case where input and output indices coincide. Free monads, indexed monads, and
`do`-notation only make sense in the endomorphic case (a free monad arises from
an endofunctor, not an arbitrary functor between family categories).

When `J` has only one element, `IPFunctor I J` further collapses to a `PFunctor`
via `IPFunctor.toPFunctor` (after fixing `J` to its default element).

References:
[`REFERENCES.md`](../../REFERENCES.md). Hancock-Setzer 2000,
Altenkirch-Ghani-Hancock-McBride-Morris 2015 (*Indexed Containers*) — the
indexed/dependent containers literature is the natural home for the state-typed
free monads here. Atkey 2009 (*Parameterised Notions of Computation*) — the
indexed-monad shape that `IPFunctor.FreeM₂` instantiates.

## File index

| File | Purpose |
|------|---------|
| [`PolyFun/IPFunctor/Basic.lean`](../../PolyFun/IPFunctor/Basic.lean) | `IPFunctor I J` structure (fields `A`, `B`, `src`), `Endo I := IPFunctor I I` abbrev, `Obj`, fiberwise `map` and functor laws, `CoeFun`, `Zero`, `One`, `toPFunctor`, `sigmaPFunctor`, composition `Q ◃ P`, `DeterministicTransitions`. |
| [`PolyFun/IPFunctor/M.lean`](../../PolyFun/IPFunctor/M.lean) | `IPFunctor.IM P i`, the indexed final coalgebra for `P : Endo I`: audit-visible sigma-erased representation with root/all-edge coherence, constructor/destructor equivalence, corecursor equations, uniqueness, and a cast-free indexed bisimulation principle. |
| [`PolyFun/IPFunctor/Free/Family.lean`](../../PolyFun/IPFunctor/Free/Family.lean) | **Primitive `IPFunctor.IFreeM P X : I → Type`** for `P : Endo I` and `X : I → Type` (state-indexed return family). Family-polymorphic `bind`, `imap`, `inductionOn`, `construct`, `mapM`, `toSigmaFreeM`, injectivity / equation lemmas. |
| [`PolyFun/IPFunctor/Free/Basic.lean`](../../PolyFun/IPFunctor/Free/Basic.lean) | `IPFunctor.FreeM P s α := IFreeM P (fun _ => α) s` — the constant-family specialization. Constructors `pure` / `liftBind` (as `@[match_pattern]` aliases over `IFreeM`), `lift` (shape) / `liftObj` (object), `bind` (state-polymorphic), `Functor` / `LawfulFunctor`, `inductionOn`, `construct`, `mapM`, `erase` (forgetful to `PFunctor.FreeM` under `[Unique I]`), `toSigmaFreeM`. |
| [`PolyFun/IPFunctor/Free/Indexed.lean`](../../PolyFun/IPFunctor/Free/Indexed.lean) | `IPFunctor.FreeM₂ P s t α := IFreeM P (fun u => PSigma (fun _ : u = t => α)) s` — the terminal-state-marker specialization. `bind` chains indices positionally; carries `IndexedMonad` / `LawfulIndexedMonad` instances. Forgetful coercion `toFreeM`. |
| [`PolyFun/IPFunctor/Lens/Basic.lean`](../../PolyFun/IPFunctor/Lens/Basic.lean) | `IPFunctor.Lens P Q` — Cartesian lens between indexed polynomials with the source-index preservation law `src_eq`. Identity, composition, `Lens.Equiv`. |
| [`PolyFun/IPFunctor/Chart/Basic.lean`](../../PolyFun/IPFunctor/Chart/Basic.lean) | `IPFunctor.Chart P Q` — covariant chart (dual to lens) with `src_eq` in the chart direction. Identity, composition, `Chart.Equiv`. |
| [`PolyFun/IPFunctor/Equiv/Basic.lean`](../../PolyFun/IPFunctor/Equiv/Basic.lean) | `IPFunctor.Equiv P Q` (`≃ₚ`) — structural equivalence with fiberwise `A` / `B` equivalences plus `src_eq`. |
| [`PolyFun/IPFunctor/Notation.lean`](../../PolyFun/IPFunctor/Notation.lean) | Lean 4.29 `@[doElem_elab]` overrides making ordinary `do { let x ← e; … }` elaborate to `IPFunctor.FreeM.bind`-trees. Custom diagnostics for state mismatches and non-polymorphic remainders. Opt in with `set_option backward.do.legacy false`. |
| [`PolyFun/IPFunctor/Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean) | `do`-notation for `IPFunctor.FreeM₂`. Statically-tracked intermediate states; chains of any length compose. Adds the `Pure (IPFunctor.FreeM₂ P s s)` instance. |
| [`PolyFun/IPFunctor/Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) | `do`-notation for `IPFunctor.FreeM` with a `DeterministicTransitions P` class. Specializes `IPFunctor.FreeM.lift`-style steps to a concrete source index. |
| [`PolyFunTest/IPFunctor/Examples.lean`](../../PolyFunTest/IPFunctor/Examples.lean) | Worked examples: a two-phase protocol compiled three ways (`IPFunctor.FreeM₂`, deterministic `IPFunctor.FreeM`, Σ-bundled erase via `toSigmaFreeM`), plus a `PFunctor.FreeM.equivW_of_isEmpty` round-trip. |
| [`PolyFun/Control/Monad/Indexed.lean`](../../PolyFun/Control/Monad/Indexed.lean) | Atkey indexed-monad class (`IndexedMonad`, `LawfulIndexedMonad`) and the trivial-`Unit` instance. |

## Mental model

### `IPFunctor I J` (general, two-index)

Read the four fields as: "at output index `j`, the agent may select a shape
`A j`; each shape carries a response set `B j a`; once response `b` is fixed,
the child sits in the fiber `X (src j a b)` over its source index in `I`."
The general two-index version captures functors between family categories;
composition `Q ◃ P : IPFunctor I K` of `P : IPFunctor I J` and
`Q : IPFunctor J K` realises functor composition. Free constructions are
*not* defined on the general object — they require an endofunctor.

### `IPFunctor.Endo I` (endomorphic, where free monads live)

`Endo I = IPFunctor I I` is the case where input and output indices coincide.
Conceptually, "from state `s`, the agent may select shape `A s`; each shape
carries response set `B s a`; once response `b` is fixed, the state advances
to `src s a b`." This is the only case where `IFreeM` / `FreeM` / `FreeM₂`,
`IndexedMonad`, and `do`-notation make sense.

### `IPFunctor.IM P i` (indexed final coalgebra)

`IM P i` is the coinductive counterpart of `IFreeM`: a potentially infinite
`P`-tree rooted at index `i`, where every child is forced into the fiber named
by `P.src`. Its implementation is an ordinary M-tree over `P.sigmaPFunctor`
plus a proposition-valued coherence invariant at every finite vertex. The
client-facing final-coalgebra API is `dest` / `mk` / `corec`, with defining
equation, uniqueness, and `corec dest = id`.

### `IPFunctor.IFreeM P X s` (primitive: state-indexed return family)

A well-founded tree starting at state `s` with `X s`-leaves (the leaf type
depends on the leaf state). Different branches can end at *different* leaf
states because `liftBind`'s source map `src` may produce different results for
different responses, and a leaf's payload type may depend on the state it
sits in.

This is the **primitive** indexed free construction. The bind shape

```lean
protected def bind :
    {s : I} → IFreeM P X s → (∀ s', X s' → IFreeM P Y s') → IFreeM P Y s
```

takes a family-polymorphic continuation: a function from each leaf state `s'`
and the leaf payload `X s'` to a continuation tree returning `Y`-leaves.

Specializing the return family `X` recovers the two distinguished cases:

- Constant family `X = fun _ => α` → `IPFunctor.FreeM P s α`
- Terminal-state marker `X = fun u => PSigma (fun _ : u = t => α)` →
  `IPFunctor.FreeM₂ P s t α`

### `IPFunctor.FreeM P s α` (constant family)

A tree where all leaves carry values of the same type `α`, but the *leaf
state* can vary across branches. **Not** a `Monad` — its bind takes a
state-polymorphic continuation `(s' : I) → α → IPFunctor.FreeM P s' β`,
which corresponds exactly to `IFreeM.bind` at the constant family.

The induction principle (`IPFunctor.FreeM.inductionOn`) takes a state-indexed
motive `C : ∀ s, IPFunctor.FreeM P s α → Prop` — necessary because `liftBind`'s
continuation lands at a different state from its parent.

### `IPFunctor.FreeM₂ P s t α` (terminal-state marker)

A tree where *all* leaves are at the same post-state `t`. The leaf payload
type encodes this as `PSigma (fun _ : u = t => α)` — a leaf at state `u`
carries both a proof that `u = t` and a value of type `α`. The type forces
every leaf to sit at `t`.

Strictly more restrictive than `FreeM`, but in return:

- `IPFunctor.FreeM₂.bind` is a genuine indexed bind:
  `FreeM₂ P s t α → (α → FreeM₂ P t u β) → FreeM₂ P s u β`. Implemented
  by `IFreeM.bind` with an `h ▸ g a` transport across the equality witness.
- `IPFunctor.FreeM₂` carries a `LawfulIndexedMonad I (IPFunctor.FreeM₂ P)`
  instance, so it can be used via the Atkey `ipure` / `ibind` interface.

Use `FreeM₂` when you want static guarantees about the post-state of a
computation (session-typed protocols are the canonical example).

### Comparison

| | `IFreeM P X s` | `FreeM P s α` | `FreeM₂ P s t α` | `PFunctor.FreeM Q α` |
|---|---|---|---|---|
| Primitive vs derived | primitive | constant-family specialization | equality-tagged specialization | non-indexed analogue |
| Leaf type | `X s` (varies per leaf state) | `α` (constant) | `α` (gated by `u = t`) | `α` (constant, no index) |
| Tracks pre-state | yes | yes | yes | no |
| Tracks post-state | per leaf (data-dependent) | per leaf (data-dependent) | uniformly (static) | n/a |
| Is a `Monad` | no | no | no (but is `IndexedMonad`) | yes |
| Suitable for `do`-notation | no | via custom elaborator | via `ipure` / `ibind` | yes |
| `bind` continuation shape | `∀ s', X s' → IFreeM P Y s'` | `(s' : I) → α → FreeM P s' β` | `α → FreeM₂ P t u β` | `α → PFunctor.FreeM Q β` |

### Forgetful maps

- `IPFunctor.FreeM₂.toFreeM : FreeM₂ P s t α → FreeM P s α` — always available;
  drops the equality witness from each leaf payload.
- `IPFunctor.FreeM.erase : FreeM P s α → P.toPFunctor.FreeM α` — available only
  when `[Unique I]`; drops the entire indexing.
- `IPFunctor.FreeM.toSigmaFreeM : FreeM P s α → P.sigmaPFunctor.FreeM α` —
  available for *any* index type; Σ-bundles the originating state into each
  position, so the result sits over `P.sigmaPFunctor` (positions of type
  `Σ s : I, P.A s`) rather than the flat `P.toPFunctor`. Use this when the
  index type is not a `Unique` but you still want to hand the tree to
  `PFunctor`-shaped APIs. Worked example in
  [`Examples.lean`](../../PolyFunTest/IPFunctor/Examples.lean).

The reverse directions do not in general exist: `FreeM P s α` may have
non-uniform leaf states (so no single `t` for `FreeM₂`), and re-attaching
non-trivial state information to a `PFunctor.FreeM` requires choosing a
fixed `s`.

## Morphisms: lenses, charts, structural equivalences

Lenses, charts, and structural equivalences live in the parallel files
`Lens/Basic.lean`, `Chart/Basic.lean`, and `Equiv/Basic.lean`. All three are
defined on the *general* two-index `IPFunctor I J` — they do not require
endomorphism.

The key addition over the non-indexed
[`PFunctor.Lens`](../../PolyFun/PFunctor/Lens/Basic.lean) is the **source-index
preservation law** `src_eq`, which says the source index in `I` of a pulled-
back (or pushed-forward) response agrees with that of its image. The law is
equality of *index values*, not of types — so most concrete morphisms discharge
it by `rfl`. Object maps along a lens / chart, however, may need to transport
children through `src_eq` because they live in fibers over `src ...`.

Only the core structure (identity, composition, `Equiv`) is provided today;
the monoidal / distributive layer mirrored from `PFunctor.Lens` is a future
addition.

## Composition

For `P : IPFunctor I J` and `Q : IPFunctor J K`, the composition `Q ◃ P` is
an `IPFunctor I K` realising the functor composition `Q ∘ P`. Positions at
output index `k` are `Q`-shapes paired with, for each `Q`-response, a
`P`-shape at the source index; responses are pairs `(b_Q, b_P)`; sources
chase through the inner `P.src`. See `IPFunctor.comp` in
[`Basic.lean`](../../PolyFun/IPFunctor/Basic.lean).

Composition is *not* defined on the endomorphic `Endo I` alone — it crucially
needs distinct input and output indices to type-check in general.

## `mapM` and the universe constraint

For both `IPFunctor.FreeM` and `IPFunctor.FreeM₂`, `mapM` interprets into an
ordinary `Monad m`. Because the responses `P.B s a` live in `Type uB`, the
target monad must operate at that same universe: `m : Type uB → Type w`, and
the value type `α : Type uB`. This mirrors `PFunctor.FreeM.liftM` and is
enforced by the `variable` block at the top of each `mapM` section.

`IPFunctor.IFreeM.mapM` additionally takes an explicit leaf interpretation
`k : (s : I) → X s → m α` because the family `X` is state-indexed: the caller
specifies what to do with each leaf payload. `FreeM.mapM` and `FreeM₂.mapM`
specialize `k` (to `Pure.pure` and to discarding the equality witness,
respectively).

`IPFunctor.FreeM₂.mapM` deliberately targets a plain `Monad`, not an
`IndexedMonad`, because `P.src s a b` is data-dependent on `b` and so cannot
be threaded through `ibind`'s static-index signature. If you need
state-tracking on the target side, lift the responses into a state-monad and
read the state back.

## Limitations

- `IPFunctor.FreeM₂` does not support a general
  `liftObj : P.Obj (fun _ => α) s → FreeM₂ P s t α`, because `liftObj`'s post-state
  varies with the response (`P.src s a b`) while `FreeM₂` requires a
  statically chosen `t`. Where this matters, work in `FreeM` and convert when
  post-state becomes known.
- `IPFunctor.FreeM.erase` is gated on `[Unique I]` because the equivalence
  between `Endo I` and `PFunctor` only collapses at that point. An
  `[Inhabited I]` variant is conceivable (picking a designated state) but is
  not provided. For arbitrary index types, the Σ-bundled
  `IPFunctor.FreeM.toSigmaFreeM` lifts that restriction at the cost of a
  richer position type — see the *Forgetful maps* list above.
- `IPFunctor.Lens` / `Chart` / `Equiv` only carry the core structure today.
  The monoidal-product, distributive, and Σ / Π combinators present in
  `PFunctor.Lens` are not yet mirrored; add on demand.
- Several `PFunctor`-layer files have no indexed analogue yet —
  `PFunctor/{Bound, Category, Cofree, M, Trace}.lean`,
  `PFunctor/Lens/{Cartesian, State}.lean`, and the displayed-free family
  `PFunctor/Free/{Displayed, Displayed/*, Path, Replicate}.lean`. The
  indexed side currently exposes only `Free/{Family, Basic, Indexed}.lean`
  and `Lens/Basic.lean`. Mirror on demand as downstream consumers require.

## `do`-notation flavors

Three parallel `do`-notation files plug into Lean 4.29's extensible
do-elaborator. See
[`ipfunctor-do-notation.md`](ipfunctor-do-notation.md) for a worked
walkthrough with a small two-phase-protocol example.

All three require `set_option backward.do.legacy false` and check
the expected monad type before activating, so other monads in the same file
are unaffected.

The elaborator detectors use `Meta.withTransparency .reducible <| whnf m`
so the `IPFunctor.FreeM` / `IPFunctor.FreeM₂` head — defined as a plain
(non-`@[reducible]`) `def` aliasing the primitive `IPFunctor.IFreeM` — survives
without being unfolded. The aliased constructors `FreeM.pure` / `FreeM.liftBind`
and `FreeM₂.pure` / `FreeM₂.liftBind` are `@[match_pattern]` but also plain `def`,
so the deterministic elaborator's head check on `FreeM.liftBind` continues to fire.

| File | Monad | Continuation type | When to use |
|---|---|---|---|
| [`Notation.lean`](../../PolyFun/IPFunctor/Notation.lean) | `IPFunctor.FreeM P s α` | `(s' : I) → α → IPFunctor.FreeM P s' β` (universal) | Tail of the block is state-polymorphic (`pure`/`return`, polymorphic helpers). Custom diagnostics call out state mismatches and non-polymorphic remainders. |
| [`Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean) | `IPFunctor.FreeM₂ P s t α` | `α → IPFunctor.FreeM₂ P t u β` (statically tracked) | Chains of any length where every step's tree converges to a single post-state. Also adds the `Pure (IPFunctor.FreeM₂ P s s)` instance. |
| [`Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) | `IPFunctor.FreeM P s α` with `[DeterministicTransitions P]` | `P.B s a → IPFunctor.FreeM P (next s a) β` (specialized) | Stay on single-index `IPFunctor.FreeM` for downstream compatibility; specialize `IPFunctor.FreeM.lift`-style steps via the determinism class. |

## What lives where downstream

`IPFunctor` is generic substrate, like `PFunctor`. Downstream usage that
benefits from state-gated interaction (multi-phase oracle protocols, session
types) should sit on top, not inline these constructors. Cryptographic
content remains in [`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio)
per the project policy in [`CLAUDE.md`](../../CLAUDE.md).
