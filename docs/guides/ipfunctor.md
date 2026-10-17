# Indexed Polynomial Functors (`IPFunctor`)

Use indexed polynomials when the available requests or their response types
depend on a protocol state. Start with the [indexed program tutorial](../tutorials/indexed-programs.md)
for code, or the definitions below for the container interpretation.

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

With `[Unique J]`, `IPFunctor.toPFunctor` (definitionally `fiberPFunctor`)
selects the unique output fiber and forgets its source-index map. The conversion
does not require `[Unique I]`. That assumption belongs to
`IPFunctor.toPFunctor_injective`, which proves that the conversion loses no
information when both index types are unique. Free-tree erasure still requires
`[Unique I]` to identify the source indices of continuations.

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
| [`PolyFun/IPFunctor/Free/Fold.lean`](../../PolyFun/IPFunctor/Free/Fold.lean) | `IPFunctor.FoldAlgebra P D` and the whole-tree fold `IFreeM.fold`, with `fold_rel`, `fold_fusion`, and `fold_unique`. |
| [`PolyFun/IPFunctor/Free/Reindex.lean`](../../PolyFun/IPFunctor/Free/Reindex.lean) | `IPFunctor.Reindexing P Q f` across index types and `IFreeM.reindex`, with identity, composition, transport, and interpretation laws. `Lens.toReindexing` views an indexed lens as a reindexing along `id`. |
| [`PolyFun/IPFunctor/Free/Traversal.lean`](../../PolyFun/IPFunctor/Free/Traversal.lean) | `IPFunctor.Traversal P Q State` and `IFreeM.traverse`, carrying a state into each child and replacing leaves by trees; composition, identity, and interpretation laws. `Reindexing.toTraversal` relates traversals to reindexing. |
| [`PolyFun/IPFunctor/Lens/Basic.lean`](../../PolyFun/IPFunctor/Lens/Basic.lean) | `IPFunctor.Lens P Q` — Cartesian lens between indexed polynomials with the source-index preservation law `src_eq`. Identity, composition, `Lens.Equiv`. |
| [`PolyFun/IPFunctor/Chart/Basic.lean`](../../PolyFun/IPFunctor/Chart/Basic.lean) | `IPFunctor.Chart P Q` — covariant chart (dual to lens) with `src_eq` in the chart direction. Identity, composition, `Chart.Equiv`. |
| [`PolyFun/IPFunctor/Equiv/Basic.lean`](../../PolyFun/IPFunctor/Equiv/Basic.lean) | `IPFunctor.Equiv P Q` (`≃ₚ`) — structural equivalence with fiberwise `A` / `B` equivalences plus `src_eq`. |
| [`PolyFun/IPFunctor/Notation.lean`](../../PolyFun/IPFunctor/Notation.lean) | `@[doElem_elab]` overrides for the pinned Lean toolchain, making ordinary `do { let x ← e; … }` elaborate to `IPFunctor.FreeM.bind`-trees. Custom diagnostics for state mismatches and non-polymorphic remainders. |
| [`PolyFun/IPFunctor/Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean) | `do`-notation for `IPFunctor.FreeM₂`. Statically-tracked intermediate states; chains of any length compose. Adds the `Pure (IPFunctor.FreeM₂ P s s)` instance. |
| [`PolyFun/IPFunctor/Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) | `do`-notation for `IPFunctor.FreeM` with a `DeterministicTransitions P` class. Specializes `IPFunctor.FreeM.lift`-style steps to a concrete source index. |
| [Indexed tutorial](../../Examples/Tutorials/IndexedPrograms.lean) | A two-phase protocol using `FreeM₂`, deterministic `FreeM`, and sigma erasure. [Regression tests](../../PolyFunTest/IPFunctor/Examples.lean) check information loss and the empty-result round-trip. |
| [`PolyFun/Control/Monad/Indexed.lean`](../../PolyFun/Control/Monad/Indexed.lean) | Atkey indexed-monad class (`IndexedMonad`, `LawfulIndexedMonad`) and the trivial-`Unit` instance. |

## Mental model

### `IPFunctor I J` (general, two-index)

Read the three fields as: "at output index `j`, the agent may select a shape
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

Structural equivalences convert canonically to both `Lens.Equiv` and
`Chart.Equiv`, including identity, composition, inverse, and round-trip laws.
The monoidal / distributive layer mirrored from `PFunctor.Lens` remains a
future addition.

## Composition

For `P : IPFunctor I J` and `Q : IPFunctor J K`, the composition `Q ◃ P` is
an `IPFunctor I K` realising the functor composition `Q ∘ P`. Positions at
output index `k` are `Q`-shapes paired with, for each `Q`-response, a
`P`-shape at the source index; responses are pairs `(b_Q, b_P)`; sources
chase through the inner `P.src`. See `IPFunctor.comp` in
[`Basic.lean`](../../PolyFun/IPFunctor/Basic.lean).

Composition is *not* defined on the endomorphic `Endo I` alone — it crucially
needs distinct input and output indices to type-check in general.

## Folds, reindexing, and traversals

`IPFunctor.FoldAlgebra P D` interprets one constructor from the meanings of its
children, each at the child's own index; `IFreeM.fold` interprets a whole finite
tree with a leaf map and such an algebra. Unlike an effect handler, an algebra
need not choose a single response, and function-valued carriers can delay the
evaluation of children, including children under a language's binders.
`fold_rel`, `fold_fusion`, and `fold_unique` separate constructor reasoning from
whole-tree induction. The algebra is named `FoldAlgebra` so that `open IPFunctor`
leaves Mathlib's `Algebra` unshadowed.

`IPFunctor.Reindexing P Q f` translates the constructors of `P : Endo I` into
those of `Q : Endo J` along a change of index `f : I → J`, together with argument
positions; its `source` equation says that translated children sit at translated
indices. `IFreeM.reindex` applies it with an explicit leaf map. `reindex_id`,
`reindex_comp`, and `reindex_cast` give its identity, composition, and transport
laws, and `fold_reindex` relates interpretation before and after a reindexing.
An indexed [lens](#morphisms-lenses-charts-structural-equivalences) between
endomorphic polynomials is a reindexing along `id` (`Lens.toReindexing`, with
`src_eq` as its source equation); `reindex_toReindexing_comp` fuses reindexing
along successive lenses into reindexing along their composite.

`IPFunctor.Traversal P Q State` carries a state `State i j` into each child and
may change it under each constructor, as a renaming, type instantiation, or
substitution does when it enters a binder. `IFreeM.traverse` replaces leaves by
whole trees. `traverse_comp` fuses traversals through `Traversal.comp`;
`traverse_identity` accepts any equality witness between its source and target
judgments and returns the transported tree. `fold_traverse` and
`fold_traverse_rel` reduce interpretation after a traversal to a fold carrying the
state, and constructor-local compatibility to all trees. `Reindexing.toTraversal`
is the traversal whose state `PLift (f i = j)` records the translated judgment;
with pure leaves, `traverse_toTraversal` identifies traversal along it with
`reindex` followed by transport to the recorded target, and the identity
reindexing gives `Traversal.identity` (`Reindexing.toTraversal_id`).
[Ordinary-import checks](../../PolyFunTest/ModuleAPI/IndexedFold.lean) exercise
these operations on a two-sorted expression signature.

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
  `PFunctor/{Bound, Category, Cofree, Trace}.lean`,
  `PFunctor/Lens/{Cartesian, State}.lean`, and the displayed-free family
  `PFunctor/Free/{Displayed, Displayed/*, Path, Replicate}.lean`. The
  indexed side currently has `Basic.lean`, `M.lean`,
  `Free/{Family, Basic, Indexed, Fold, Reindex, Traversal}.lean`, and the core
  `Lens`, `Chart`, and `Equiv` modules. Mirror on demand as downstream consumers
  require.

## `do`-notation flavors

Three parallel `do`-notation files plug into Lean's extensible
do-elaborator. See the
[indexed-programs tutorial](../tutorials/indexed-programs.md) for a worked
walkthrough with a small two-phase-protocol example.

The extensible elaborator is the pinned toolchain's default, so no option is
required. All three check the expected monad type before activating, leaving
other monads in the same file unaffected. Setting `backward.do.legacy true`
selects core's non-extensible `do` elaborator, which disables these extensions.

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
per the project policy in [`CLAUDE.md`](../../AGENTS.md).

## Object action

`IPFunctor.Obj` exposes `mk`, `fst`, `snd`, `rec`, `eta`, and `ext`, following
Mathlib's polynomial-object interface. Its child projection has the dependent
type `(b : P.B j x.fst) → X (P.src j x.fst b)`. Consumers should use these
operations and `map_fst` / `map_snd` rather than unfolding the Sigma encoding.

## Binding signatures and native IR

`IPFunctor.ScopedSignature` describes operations by their result sort, argument
positions, and the sorts bound in each argument. Its `Term` is an `IFreeM`:
variables are typed leaves, and constructor nodes contain their children.
This makes the polynomial structure the syntax representation itself.

`Term.rename` and `Term.subst` lift their maps through each argument's binder
list. The identity, composition, and single-variable substitution laws live in
`Scoped.Renaming` and `Scoped.Substitution`. `Scoped.Interpretation` folds into
functions of environments and proves `denote_rename`, `denote_subst`, and
`denote_substOne` once for every constructor algebra. Algebras receive argument
meanings as functions of new bound values, so entering a binder does not
execute its body.

For a different semantic carrier, `IPFunctor.Algebra` and `IFreeM.fold` provide
an indexed constructor fold. `fold_rel`, `fold_fusion`, and `fold_unique` separate
constructor reasoning from whole-tree induction. In particular, a lazy language
can fold into **continuous** environment functions; it need not erase continuity
to use the simpler native interpretation API.

`ScopedSignature.Hom` changes sorts, operations, and argument positions together.
Its equations require translated child sorts and binder lists to agree.
`Term.map` uses `IFreeM.reindex`; `fold_reindex` relates interpretation before and
after this change. Sort maps may identify different sorts: variable positions
remain distinct. This supports type instantiation of a suitable signature, but
does not itself supply a language's type-quantifier syntax or constraints.

The [scoped-program tutorial](../../Examples/Tutorials/ScopedPrograms.lean)
contains arithmetic, functions, lexical lets, and a bounded loop whose body is
stored once. Its let-elimination proof uses generic fold fusion and substitution
correctness. [Ordinary-import checks](../../PolyFunTest/ModuleAPI/Scoped.lean)
exercise capture avoidance and noninjective sort translation.

## Binders that change parameter contexts

[`ScopedFamily W S`](../../PolyFun/IPFunctor/Scoped/Family.lean) lets each child
enter its own parameter context `w : W`, reindex old value sorts `S w`, and
bind new values. A judgment contains the parameter context, the local value
context, and the result sort. Terms remain `IFreeM` trees. This supports type
or numeric quantifiers without representing syntax as a callback that builds a
different term for each instantiation.

[`ScopedFamily.Hom`](../../PolyFun/IPFunctor/Scoped/FamilyMap.lean) describes a
parameter transformation by constructor-local equations. It checks how the
parameter map lifts at every child, including compatibility with old variable
sorts, new binder lists, and result sorts. `Term.map` assembles these equations
into an [`IPFunctor.Traversal`](../../PolyFun/IPFunctor/Free/Traversal.lean).
`Term.map_node` exposes the lifted child maps and their context transports;
`Term.map_rename` proves that mapping parameters commutes with value renaming.
`Hom.comp` composes the constructor translations and their lifted parameter
maps. `Term.map_map` identifies successive maps with this composite after
normalizing the ambient context's two `List.map` applications.
`Hom.identity` transports between equal parameter contexts; `Term.map_identity`
normalizes an identity map in one context, and `Term.map_identity_heq` handles
distinct but provably equal parameter contexts.
`IFreeM.traverse_comp` fuses traversals; `IFreeM.traverse_identity` accepts any
equality witness between its source and target judgments and returns the
transported tree. `Term.fold_map_rel` lifts local semantic
compatibility to all family terms. A language must still prove that compatibility
for its own constructor algebra. `Term.cast` normalizes contexts and result sorts.
Its self-transport simplifier accepts arbitrary equality proofs, while
`Term.cast_heq` compares terms across potentially different contexts and sorts.

[`Scoped.Transport`](../../PolyFun/IPFunctor/Scoped/Transport.lean) reindexes
variables by their original positions. No injectivity assumption is required:
two parameters can instantiate to the same type without merging their bindings.
Value renaming has identity and composition laws. The
[`family substitution API`](../../PolyFun/IPFunctor/Scoped/FamilySubstitution.lean)
requires a language action for reindexing substitution images when entering a
new parameter context. `ReindexAction.Lawful` states variable preservation and
compatibility with value renaming and substitution. The public laws include
`subst_id`, `subst_rename`, `rename_subst`, and `subst_subst`; individual theorems
require only the compatibility they use. `substOne` and `substOne_subst_lift`
support beta reduction and closing a term below a fresh binder. A language must
establish these action laws; they do not follow from arbitrary `ReindexAction`
data. Semantic substitution additionally requires interpretation preservation.

[`FamilyMapSubstitution`](../../PolyFun/IPFunctor/Scoped/FamilyMapSubstitution.lean)
relates these operations. `Hom.PreservesReindex` asks for a commuting square
between a translation and the source/target parameter actions at each child.
Its `preservesSubstitution` theorem handles positional lookup and binder lifting;
`Term.map_subst` then commutes the translation with simultaneous substitution.
This does not assume injectivity of sort maps or preservation of an interpretation.
`Substitution.cast` accepts arbitrary context equalities, and its `cast_heq`
simplifier also covers contexts that are only propositionally equal.

The [constant-family adapter](../../PolyFun/IPFunctor/Scoped/ConstantFamily.lean)
provides both proved round trips to the existing `ScopedSignature` API.
[`FamilySize`](../../PolyFun/IPFunctor/Scoped/FamilySize.lean) counts nodes when
every constructor has finitely many children. The count excludes head payloads
and measures neither execution cost nor the size of a semantic value.

[`ScopedDomain.Env`](../../PolyFun/IPFunctor/Scoped/Domain.lean) interprets local
contexts in bundled [`PointedDomain`](../../PolyFun/Control/Domain/Pointed.lean)
carriers. Extension, append, and sort reindexing are continuous maps.
`Env.fixGroup` ties a finite heterogeneous group with one least fixed point;
its unfolding and leastness laws apply to the whole environment. Environment
renaming commutes with extension, append, and sort transport. Consecutive sort
transports compose. `fixGroup_rename` handles ambient value renaming, and
`fixGroup_fusion` transports recursion through a strict continuous map that
commutes with whole-group unfolding. Language specific errors and quantifier
stages remain outside this generic layer.

The [polymorphic tutorial](../../Examples/Tutorials/ScopedFamily.lean) constructs
a finite identity under a type binder and proves erasure preservation for every
parameter renaming using `fold_map_rel`. It also demonstrates an ambient value
remaining free below a type binder and a value binder. It has no Cryptol or cryptography
dependency. [Public API checks](../../PolyFunTest/ModuleAPI/ScopedFamily.lean)
and the separate documentation consumer exercise the same theorems through
ordinary imports.
