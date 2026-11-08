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
| [`PolyFun/IPFunctor/Basic.lean`](../../PolyFun/IPFunctor/Basic.lean) | `IPFunctor I J` structure (fields `A`, `B`, `src`), `Endo I := IPFunctor I I` abbrev, `Obj`, fiberwise `map` and functor laws, `CoeFun`, `Zero`, `One`, `toPFunctor`, `sigmaPFunctor`, coproducts `sum` / `sumULift`, composition `Q ◃ P`, `DeterministicTransitions`. |
| [`PolyFun/IPFunctor/M.lean`](../../PolyFun/IPFunctor/M.lean) | `IPFunctor.IM P i`, the indexed final coalgebra for `P : Endo I`: audit-visible sigma-erased representation with root/all-edge coherence, constructor/destructor equivalence, corecursor equations, uniqueness, and a cast-free indexed bisimulation principle. |
| [`PolyFun/IPFunctor/Free/Family.lean`](../../PolyFun/IPFunctor/Free/Family.lean) | **Primitive `IPFunctor.IFreeM P X : I → Type`** for `P : Endo I` and `X : I → Type` (state-indexed return family). Family-polymorphic `bind` and `imap` with independent leaf universes, the bind and map laws, `inductionOn`, `construct`, `mapM`, `toSigmaFreeM`, injectivity / equation lemmas. |
| [`PolyFun/IPFunctor/Free/Basic.lean`](../../PolyFun/IPFunctor/Free/Basic.lean) | `IPFunctor.FreeM P s α := IFreeM P (fun _ => α) s` — the constant-family specialization. Constructors `pure` / `liftBind` (as `@[match_pattern]` aliases over `IFreeM`), `lift` (shape) / `liftObj` (object), `bind` (state-polymorphic), `Functor` / `LawfulFunctor`, `inductionOn`, `construct`, `mapM`, `erase` (forgetful to `PFunctor.FreeM` under `[Unique I]`), `toSigmaFreeM`. |
| [`PolyFun/IPFunctor/Free/Indexed.lean`](../../PolyFun/IPFunctor/Free/Indexed.lean) | `IPFunctor.FreeM₂ P s t α := IFreeM P (fun u => PSigma (fun _ : u = t => α)) s` — the terminal-state-marker specialization. `bind` chains indices positionally; carries `IndexedMonad` / `LawfulIndexedMonad` instances. Forgetful coercion `toFreeM`. |
| [`PolyFun/IPFunctor/Free/Bound.lean`](../../PolyFun/IPFunctor/Free/Bound.lean) | Roll bounds on `IFreeM` whose check and cost read the state (`IsRollBound`), the subtractive charge bound `IsChargeBound` and the total bound `IsTotalRollBound`; budgets add under `bind` across leaf universes; defined by `PFunctor.FreeM.IsRollBound` through `toSigmaFreeM`; `FreeM` / `FreeM₂` abbreviations for dot notation. |
| [`PolyFun/IPFunctor/Free/Bound/Traversal.lean`](../../PolyFun/IPFunctor/Free/Bound/Traversal.lean) | Roll and charge bounds under `IFreeM.traverse`: preservation along a state-dependent budget relation, reflection for surjective response maps, and the charge forms `IsChargeBound.traverse`, `IsChargeBound.of_traverse`, `isChargeBound_traverse_iff`. |
| [`PolyFun/IPFunctor/Free/Bound/Loops.lean`](../../PolyFun/IPFunctor/Free/Bound/Loops.lean) | Bounds for `List.foldlM` and Batteries' dependent `Fin.dfoldlM` over `FreeM₂ P s s`, through any monad structure whose `pure` and `bind` are those of `FreeM₂` (`FreeM₂.IsDiagonalMonad`): combined roll bounds, summed and uniform charge bounds, and preservation of a predicate on every shape; the same bounds for the tuple sequencer `FreeM₂.seqPi`. |
| [`PolyFun/IPFunctor/Free/Tuple.lean`](../../PolyFun/IPFunctor/Free/Tuple.lean) | `FreeM₂.seqPi`, sequencing a dependent tuple of programs `(i : Fin k) → FreeM₂ P s s (β i)` into one returning `(i : Fin k) → β i`, with the definitional equations `seqPi_zero` / `seqPi_succ` and `seqPi_unique`. |
| [`PolyFun/IPFunctor/Free/Lens.lean`](../../PolyFun/IPFunctor/Free/Lens.lean) | `IFreeM.mapLens`: transport of a tree along a lens, cast-free along the coproduct injections, injective along them, and its action on roll bounds. |
| [`PolyFun/IPFunctor/Free/Fold.lean`](../../PolyFun/IPFunctor/Free/Fold.lean) | `IPFunctor.FoldAlgebra P D` and the whole-tree fold `IFreeM.fold`, with `fold_rel`, `fold_fusion`, `fold_unique`, and `fold_bind`. |
| [`PolyFun/IPFunctor/Free/Reindex.lean`](../../PolyFun/IPFunctor/Free/Reindex.lean) | `IPFunctor.Reindexing P Q f` across index types and `IFreeM.reindex`, with identity, composition, transport, and interpretation laws. `Lens.toReindexing` views an indexed lens as a reindexing along `id`. |
| [`PolyFun/IPFunctor/Free/Traversal.lean`](../../PolyFun/IPFunctor/Free/Traversal.lean) | `IPFunctor.Traversal P Q State` and `IFreeM.traverse`, carrying a state into each child and replacing leaves by trees; composition, identity, and interpretation laws. `Reindexing.toTraversal` relates traversals to reindexing. |
| [`PolyFun/IPFunctor/Lens/Basic.lean`](../../PolyFun/IPFunctor/Lens/Basic.lean) | `IPFunctor.Lens P Q` — Cartesian lens between indexed polynomials with the source-index preservation law `src_eq`. Identity, composition, coproduct injections `inl` / `inr` / `inlULift` / `inrULift` and copairing `sumPair`, `Lens.Equiv`. |
| [`PolyFun/IPFunctor/Chart/Basic.lean`](../../PolyFun/IPFunctor/Chart/Basic.lean) | `IPFunctor.Chart P Q` — covariant chart (dual to lens) with `src_eq` in the chart direction. Identity, composition, `Chart.Equiv`. |
| [`PolyFun/IPFunctor/Equiv/Basic.lean`](../../PolyFun/IPFunctor/Equiv/Basic.lean) | `IPFunctor.Equiv P Q` (`≃ₚ`) — structural equivalence with fiberwise `A` / `B` equivalences plus `src_eq`. |
| [`PolyFun/IPFunctor/Notation.lean`](../../PolyFun/IPFunctor/Notation.lean) | `@[doElem_elab]` overrides for the pinned Lean toolchain, making ordinary `do { let x ← e; … }` elaborate to `IPFunctor.FreeM.bind`-trees. Custom diagnostics for state mismatches and non-polymorphic remainders. |
| [`PolyFun/IPFunctor/Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean) | `do`-notation for `IPFunctor.FreeM₂`. Statically-tracked intermediate states; chains of any length compose. Adds the `Pure (IPFunctor.FreeM₂ P s s)` instance. |
| [`PolyFun/IPFunctor/Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) | `do`-notation for `IPFunctor.FreeM` with a `DeterministicTransitions P` class. Specializes `IPFunctor.FreeM.lift`-style steps to a concrete source index. |
| [Indexed tutorial](../../Examples/Tutorials/IndexedPrograms.lean) | A two-phase protocol using `FreeM₂`, deterministic `FreeM`, and sigma erasure. [Regression tests](../../PolyFunTest/IPFunctor/Examples.lean) check information loss and the empty-result round-trip. |
| [`PolyFun/Control/Monad/Indexed.lean`](../../PolyFun/Control/Monad/Indexed.lean) | Atkey indexed-monad class (`IndexedMonad`, `LawfulIndexedMonad`) and the trivial-`Unit` instance. |
| [`PolyFun/Control/Monad/Graded.lean`](../../PolyFun/Control/Monad/Graded.lean) | Graded monads over a monoid (`GradedMonad`, `LawfulGradedMonad`), the trivial `Unit` grading, and the indexed monad of a grading over a group (`GradedMonad.toIndexedMonad`). Free programs within a charge budget are an instance (`FreeM.Budgeted`, [interaction cost](cost.md#measured-and-budgeted-programs)). |

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
protected def bind {Y : I → Type w} :
    {s : I} → IFreeM P X s → (∀ s', X s' → IFreeM P Y s') → IFreeM P Y s
```

takes a family-polymorphic continuation: a function from each leaf state `s'`
and the leaf payload `X s'` to a continuation tree returning `Y`-leaves.
The leaf family `X : I → Type v` and the continuation's family `Y` live in
independent universes, so a bind can, for example, turn Boolean leaves into
type-valued leaves. `bind_pure_right` and `bind_assoc` hold across independent
leaf universes, and `imap` is the bind whose continuation returns a leaf
(`imap_eq_bind`). `FreeM.bind` keeps one value universe. `FreeM₂.bind` and
`FreeM₂.map` allow independent input and output value universes, but `FreeM₂`
`do`-notation still elaborates every step at the block's value universe.

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
  The input value type `α` and the output value type `β` may live in different
  universes, and so do the laws `bind_pure_right`, `bind_assoc` and
  `map_eq_bind_pure` (`x.map f = x.bind fun a => pure (f a)`).
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

### Roll bounds

`IPFunctor.IFreeM.IsRollBound x budget canRoll cost` is the indexed analogue of
[`PFunctor.FreeM.IsRollBound`](../../PolyFun/PFunctor/Bound.lean): along every
branch, a `liftBind` at shape `a : P.A s` must pass `canRoll s a b` and moves the
budget to `cost s a b`. The check and the cost see the state, so a budget can
charge a request differently in different protocol phases. The bound is the
plain bound of the Σ-bundled erasure, whose positions carry the state
(`isRollBound_toSigmaFreeM_iff`).

- `IsChargeBound x c n` — the charges `c s a` along every branch add up to at
  most `n`. This is the subtractive budget that
  `PFunctor.FreeM.isRollBound_iff_wpFold_charge` reads as a worst-case charge.
- `IsTotalRollBound x n` — at most `n` rolls along every branch; the unit
  charge bound by `Iff.rfl`.

Both budgets add under `IFreeM.bind` (`isChargeBound_bind`,
`isTotalRollBound_bind`), also when the continuation changes the universe of the
leaf family. A per-port query budget is a charge that is one at calls of that
port and zero elsewhere. `FreeM.IsRollBound` and `FreeM₂.IsRollBound`, with
their charge and total specializations, are abbreviations that give dot notation
on those types.

The bounds unfold one constructor at a time by `Iff.rfl`, so the constructor
form `⟨hcan, fun y => …⟩` proves them directly. Over a concrete polynomial
declared by a plain `def`, a `liftBind` tree is well typed only after the
polynomial unfolds, so `rw` and `simp` with the `liftBind` lemmas fail at their
implicit transparency. Declare such a polynomial with `abbrev`, or use the
constructor form; [`BoundTests.lean`](../../PolyFunTest/IPFunctor/BoundTests.lean)
does the latter for a register-machine signature with oracle ports.

### Command substitution and combined budgets

[`Free/Substitution.lean`](../../PolyFun/IPFunctor/Free/Substitution.lean)
defines `CommandSubstitution P Q`: at each state `s` and shape `a : P.A s`,
provide a `Q`-tree whose leaf at `t` carries
`{b : P.B s a // P.src s a b = t}`. The equality ensures that the continuation
for response `b` starts at the replacement tree's terminal state.
`x.substitute h` extends this assignment through the existing `fold` and `bind`.
It keeps pure leaves, including their state-dependent types, and binds each
replacement to the recursively translated continuations.

`substitute_pure` and `substitute_liftBind` are simp equations;
`substitute_bind` preserves sequencing across independent leaf universes.
For a lens `l`, `Lens.toSubstitution` supplies its single-node trees, and
`substitute_toSubstitution` identifies their extension with `mapLens l`.

[`Bound/Substitution.lean`](../../PolyFun/IPFunctor/Free/Bound/Substitution.lean)
provides `IsChargeBound.substitute`: if `x.IsChargeBound c n` and every
`h s a` has target charge bound `c s a`, then `x.substitute h` has target
charge bound `n`. `IsChargeBound.substitute_mul` allows each replacement to
cost at most `k * c s a` and concludes a bound of `k * n`, including `k = 0`.

In `Free/Bound.lean`, `IsChargeBound.mul` scales a charge and its budget
together. In `Bound/Substitution.lean`, `isChargeBound_sum` combines bounds for
every member of a finite family: charges `c i` bounded by budgets `b i` give the summed charge
`fun s a => ∑ i, c i s a` bounded by `∑ i, b i`. These are simultaneous
bounds on every path, so the sum is valid even when different paths attain
different component maxima. An empty family gives the zero charge bound.

The [substitution regressions](../../PolyFunTest/IPFunctor/Substitution.lean)
exercise changing states, dependent leaves, multi-node replacements, label
budgets, and rejection of an insufficient target budget.

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
Of the monoidal / distributive layer of `PFunctor.Lens`, only the coproduct
injections and copairing are mirrored (see *Coproducts* below).

## Composition

For `P : IPFunctor I J` and `Q : IPFunctor J K`, the composition `Q ◃ P` is
an `IPFunctor I K` realising the functor composition `Q ∘ P`. Positions at
output index `k` are `Q`-shapes paired with, for each `Q`-response, a
`P`-shape at the source index; responses are pairs `(b_Q, b_P)`; sources
chase through the inner `P.src`. See `IPFunctor.comp` in
[`Basic.lean`](../../PolyFun/IPFunctor/Basic.lean).

Composition is *not* defined on the endomorphic `Endo I` alone — it crucially
needs distinct input and output indices to type-check in general.

## Coproducts

`IPFunctor.sum P Q` offers at each output index `j` the shapes of both
summands, `P.A j ⊕ Q.A j`, and a shape keeps the responses and source indices
of its summand. As with the sum `P + Q` (`PFunctor.add`), the response and
source maps are `Sum` recursors, so on `Sum.inl a` they reduce to those of `a` by `rfl`; the summands
share one response universe. `IPFunctor.sumULift P Q` allows independent
response universes by lifting each summand's responses to their maximum, so a
command signature whose kinds have responses in different universes is the
lifted coproduct of one polynomial per kind.

`Lens.inl` / `Lens.inr` and `Lens.inlULift` / `Lens.inrULift` are the
injections, and `Lens.sumPair` is the copairing (`sumPair_comp_inl`,
`sumPair_comp_inr`). `IFreeM.mapLens l` (in
[`Free/Lens.lean`](../../PolyFun/IPFunctor/Free/Lens.lean)) relabels the
shapes of a tree along `l`, reads its responses back, and transports each
continuation along `src_eq`. Along an injection that law is `rfl`, so
`mapLens Lens.inl` commutes with `liftBind` without a cast
(`mapLens_inl_liftBind`) and is injective (`mapLens_inl_injective`). Roll
bounds whose check and cost are read through `l.toFunA` transport along any
lens (`IsRollBound.mapLens`), and along `Lens.inl` the bound of the embedded
tree is the bound of the original with the left-summand checks
(`isRollBound_mapLens_inl_iff`).

## Folds, reindexing, and traversals

`IPFunctor.FoldAlgebra P D` interprets one constructor from the meanings of its
children, each at the child's own index; `IFreeM.fold` interprets a whole finite
tree with a leaf map and such an algebra. Unlike an effect handler, an algebra
need not choose a single response, and function-valued carriers can delay the
evaluation of children, including children under a language's binders.
`fold_rel`, `fold_fusion`, and `fold_unique` separate constructor reasoning from
whole-tree induction. `fold_bind` folds a bind by folding each continuation at its
leaf, with the two leaf families and the carrier in independent universes. The algebra is
named `FoldAlgebra` so that `open IPFunctor` leaves Mathlib's `Algebra` unshadowed.

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

Resource bounds follow `IFreeM.IsRollBound.reindex`: checks and costs are
read through the translated operation. `isRollBound_reindex_iff` additionally
requires every source answer to be represented by a target answer. Without
that surjectivity condition, reindexing can discard an expensive branch.
The coproduct injection equivalences specialize this shared theorem.

A traversal chooses each target constructor from the traversal state, which changes
along every branch, so its target checks cannot be read through a fixed index map.
[`Bound/Traversal.lean`](../../PolyFun/IPFunctor/Free/Bound/Traversal.lean) relates
source and target budgets by a relation that may read the state.
`IsRollBound.traverse` needs related budgets to stay related through every translated
constructor and every translated leaf to be bounded at the related target budget;
`IsRollBound.of_traverse` reflects bounds when every response map is surjective, with
no condition on leaves. The weaker `IsRollBound.of_traverse_of_exists` only requires
one compatible preimage per source response at related budgets where the translated
roll is allowed. Use it when the budget relation excludes some traversal states or
only selected preimages preserve the relation.
For charges, `IsChargeBound.traverse` adds the common leaf
budget `m` (zero for pure leaves) when each translated constructor costs at most its
source, `IsChargeBound.of_traverse` needs the reverse inequality and surjectivity, and
`isChargeBound_traverse_iff` combines them for equal charges.

### Loops

`FreeM₂ P s s` has no fixed `Monad` instance, and developments may wrap it with their
own. [`Bound/Loops.lean`](../../PolyFun/IPFunctor/Free/Bound/Loops.lean) takes any monad
structure whose `pure` and `bind` are those of `FreeM₂` (`FreeM₂.IsDiagonalMonad`,
proved by `⟨fun _ => rfl, fun _ _ => rfl⟩` for the evident instance). Along
`List.foldlM` and Batteries' dependent `Fin.dfoldlM`, `isRollBound_foldlM` and
`isRollBound_dfoldlM` combine step budgets with the side conditions of
`FreeM₂.isRollBound_bind`. Charge bounds add (`isChargeBound_foldlM`,
`isChargeBound_dfoldlM`) or multiply a uniform step budget by the number of steps
(`…_of_forall`), and the `…_unit` forms preserve a predicate on every rolled shape.
The [regressions](../../PolyFunTest/IPFunctor/TraversalLoopBounds.lean) apply these
laws through a definitional wrapper with its own `Monad` instance.

The dependent-fold laws apply to `Fin.dfoldlM` itself. A dependent tuple is sequenced
by [`FreeM₂.seqPi`](../../PolyFun/IPFunctor/Free/Tuple.lean), which returns at once on
the empty tuple (`seqPi_zero`) and otherwise binds the head, then the sequenced tail,
and returns their `Fin.cons` (`seqPi_succ`); both equations hold by `rfl`. A tuple-prefix
implementation using `Fin.dfoldlM` assembles the tuple inside each step; relating it
to these equations requires bind laws and tuple identities. Direct recursion keeps
the equations definitional without choosing a diagonal monad instance. `seqPi_unique`
identifies any operation with these two equations with `seqPi`, so a sequencer defined
elsewhere through such a monad structure inherits `isRollBound_seqPi`,
`isChargeBound_seqPi` (a sum of position budgets), `isChargeBound_seqPi_of_forall`, and
`isRollBound_seqPi_unit`.
The family `β : Fin k → Type v` has one result universe, independent of the state,
shape and response universes. Universe levels cannot vary with a value-level index;
lift entries to a common universe when their original types lie in different ones.

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
- `IPFunctor.Chart` and `Equiv` only carry the core structure today, and
  `IPFunctor.Lens` adds only the coproduct injections and copairing. The
  monoidal-product, distributive, parallel-sum, and Σ / Π combinators present in
  `PFunctor.Lens`, and the lens functoriality of `IFreeM.mapLens`, are not yet
  mirrored; add on demand.
- Several `PFunctor`-layer files have no indexed analogue yet —
  `PFunctor/{Category, Cofree, Trace}.lean`,
  `PFunctor/Lens/{Cartesian, State}.lean`, and the displayed-free family
  `PFunctor/Free/{Displayed, Displayed/*, Path, Replicate}.lean`. The
  indexed side currently has `Basic.lean`, `M.lean`,
  `Free/{Family, Basic, Indexed, Bound, Fold, Reindex, Traversal, Lens}.lean`, and the core
  `Lens`, `Chart`, and `Equiv` modules. Mirror on demand as downstream consumers require.
- The indexed roll bounds have no counterpart of `PFunctor.FreeM.ProgramProgress`
  or of the charge fold in `PFunctor/Free/WP/Charge.lean`. Reach the latter
  through `isRollBound_toSigmaFreeM_iff`.

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

An environment `Env V Γ := ∀ a, ScopedVar Γ a → V a` gives a value for each
binding position, and its sort argument is explicit. A `Renaming Γ Δ` is an
environment of variables, and a `Substitution Γ Δ` is an environment of terms.
Therefore `Env.cons`, `Env.append` and `Env.rename` act on all three, and
`Env.rename ρ τ` composes renamings. `Term.rename` and `Term.subst` lift their
environments through each argument's binder list. The identity, composition, and
single-variable substitution laws live in `Scoped.Renaming` and
`Scoped.Substitution`. `Scoped.Interpretation` folds into functions of environments
and proves `denote_rename`, `denote_subst`, and `denote_substOne` once for every
constructor algebra. Algebras receive argument meanings as functions of new bound
values, so entering a binder does not execute its body.

[`Scoped.DomainInterpretation`](../../PolyFun/IPFunctor/Scoped/DomainInterpretation.lean)
interprets a binding signature continuously. A `DomainInterpretation σ V` receives each
argument as a continuous function of only the variables that argument binds, over an
unbundled family of omega-complete partial orders `V`. `Term.denoteDomain` folds it into
continuous functions of the environment. It satisfies `denoteDomain_rename`,
`denoteDomain_subst` and `denoteDomain_substOne` for every such algebra. Because arguments
arrive as continuous functions, a constructor can also take a least fixed point of one.
`Term.denoteDomain_related` is the fundamental lemma. Let a continuous algebra and an
ordinary `Interpretation` relate their results whenever their arguments are related, by a
relation `R : ∀ a, V a → W a → Prop`. Then every term has related meanings in environments
related by `Env.LiftRel R`. The
[lazy-language tutorial](../../Examples/Tutorials/ScopedDomains.lean) relates a lazy meaning
with recursion to a call-by-value evaluator this way.

A constructor that returns a function should return `Env.abstraction` of its body's meaning, in
an `ofFun` clause, as the tutorial's `lam` does. `Env.abstraction f` is `Env.bindOne f` with its
proof of continuity stated at its own function. The form matters when the kernel checks an
equation between nested abstractions, such as one whose right side writes each continuous map
`ofFun G (id (α := ωScottContinuous G) k)`. In measurements of Lean's kernel, whose comparison
order no specification fixes, it compares two maps `ofFun F h` by the types of their proofs and
then by their functions. When each proof is stated at its function, the second comparison repeats
the first and the kernel reuses it, so the check takes time linear in the nesting depth. A
composite with `Env.bindOne` unfolds to a structure instead, and the time grows exponentially with
the depth. [`KernelBudget`](../../PolyFunTest/IPFunctor/Scoped/KernelBudget.lean) checks eight
nested abstractions of the tutorial with the kernel's budget lowered to `maxHeartbeats 200`. They
need between 5 and 10, and between 4000 and 5000 through `Env.bindOne`.

Names in the scoped layer follow one rule. A plain name is an ordinary interpretation and its
fold: `Interpretation` and `Term.denote`, and for stacked families `Model.Interp`, `Model.alg`
and `Model.denote`. `Domain` marks the continuous counterpart, semantics in omega-complete
partial orders: `DomainInterpretation`, `Term.denoteDomain`, `substitutionEnvDomain`,
`Model.DomainInterp`, `Model.domainAlg` and `Model.denoteDomain`. The suffix `Continuous` marks
instead the bundled `→𝒄` form of an existing function, such as `Env.renameContinuous`.
`DomainInterpretation` is the binding-signature analogue of `PFunctor.Resumption.ContinuousAlgebra`,
whose fold over resumptions is called `denote`.

Here an algebra is always a signature algebra, which interprets each constructor given its
arguments' meanings. `Interpretation` and `DomainInterpretation` are algebras of a binding
signature, and the tutorials' `algebra` definitions are instances of them. `Model.alg` and
`Model.domainAlg` are the `IPFunctor.FoldAlgebra`s that a stacked model's interpretation induces
on the syntax polynomial, the input of `IFreeM.fold`. The ordered monad algebras of the program
logic, such as `MAlgOrdered`, are a different notion: they interpret the computations of a monad.

[`Scoped.Certificate`](../../PolyFun/IPFunctor/Scoped/Certificate.lean) turns the fundamental
lemma into a `Control.Semantics.CertifiedMeaning`. `Term.certifiedMeaning` certifies a term
with one free variable, its input, against a native implementation. It needs two more facts.
The representation relates each encoded input to a native representative (`represents`), and a
representative determines its encoded output (`determines`). Totality says that the evaluator
returns the representative of the implementation's result (`total`). When the evaluator returns
it only on some inputs, `Term.correspondsOn_denoteDomain` gives a `CorrespondsOn` there.
`Term.liftFun_denoteDomain` states the fundamental lemma as `Relator.LiftFun`, the premise of
`CertifiedMeaning.ofLiftFun`, so a language with function sorts can certify a closed function
term through its relation at function sorts. The lazy-language tutorial certifies a program
against `(· + 2)` and composes it with a decoder into `DomainResult Empty ℕ`.

[`Scoped.Adequacy`](../../PolyFun/IPFunctor/Scoped/Adequacy.lean) relates a continuous meaning to
closed syntax, the generic part of an adequacy proof. A relation
`R : ∀ a, V a → σ.Term [] a → Prop` can describe an operational semantics, for example "the term
evaluates to a value term related to the semantic value". Suppose that each constructor's result
is related to the closed node whenever each argument's meaning is related to the argument closed
by related terms (`DomainInterpretation.RelatedSyntax`). Then
`Term.denoteDomain_relatedSyntax` relates every term's meaning in an environment to the term
closed by a related substitution, and each closed term is related to its own meaning. Each
argument is closed with `Term.instantiate`, which below one binder is `substOne`
(`instantiate_single`). The lazy-language tutorial proves computational adequacy for a
call-by-name evaluator this way. A closed numeric term means `n` exactly when it evaluates to the
numeral `n`, and a closed term means bottom exactly when it does not evaluate.

For a different semantic carrier, `IPFunctor.FoldAlgebra` and `IFreeM.fold` provide
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
exercise capture avoidance, noninjective sort translation, and the environment laws
shared by renamings and substitutions.

## Binders that change parameter contexts

[`ScopedFamily W S`](../../PolyFun/IPFunctor/Scoped/Family.lean) lets each child
enter its own parameter context `w : W`, reindex old value sorts `S w`, and
bind new values. A judgment contains the parameter context, the local value
context, and the result sort. Terms remain `IFreeM` trees. This supports type
or numeric quantifiers without representing syntax as a callback that builds a
different term for each instantiation.

The field `ambient` says how a child sees the ambient value context. A child that stays in
its parent's parameter context can `keep` that context. Its ambient context is then `Γ`
itself, definitionally, so ambient variables keep their sorts and a denotation passes its
environment unchanged. A child that changes parameter context moves each ambient sort along
a `map`. `ScopedFamily.reindex σ op p` is the resulting sort map. At a child,
`Ambient.context`, `Ambient.var`, `Ambient.env` and `Ambient.mapRenaming` replace `List.map`,
`ScopedVar.map`, `Env.reindex` and `Renaming.map`. Each of their laws reduces to the
`List.map` law at `map`.

[`ScopedFamily.Hom`](../../PolyFun/IPFunctor/Scoped/FamilyMap.lean) describes a
parameter transformation by constructor-local equations. It checks how the
parameter map lifts at every child, including compatibility with old variable
sorts, new binder lists, and result sorts. `Term.map` assembles these equations
into an [`IPFunctor.Traversal`](../../PolyFun/IPFunctor/Free/Traversal.lean).
`Term.map_node` exposes the lifted child maps and their context transports;
`Term.map_rename` proves that mapping parameters commutes with value renaming.
`Hom.comp` composes the constructor translations and their lifted parameter
maps. `Term.map_map` identifies successive maps with this composite after
normalizing the mapped context's two `List.map` applications.
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

[`Scoped.Transport`](../../PolyFun/IPFunctor/Scoped/Transport.lean) defines
`Env.reindex f`, which moves an environment of `Γ` to `Γ.map f` by its original
binding positions. No injectivity assumption is required: two parameters can
instantiate to the same type without merging their bindings. `Renaming.map` and
`Substitution.map` are instances of `Env.reindex`, and `Substitution.reindex` is an instance
of `Ambient.env`.
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
provides both proved round trips to the existing `ScopedSignature` API. Every child keeps
its ambient context, so the two polynomials agree definitionally.
[`FamilySize`](../../PolyFun/IPFunctor/Scoped/FamilySize.lean) counts nodes when
every constructor has finitely many children. The count excludes head payloads
and measures neither execution cost nor the size of a semantic value.

[`Scoped.Domain`](../../PolyFun/IPFunctor/Scoped/Domain.lean) orders environments
pointwise when every value type is an omega-complete partial order, such as a family
of `DomainResult` computations. Extension, append, renaming and `Env.map` are
continuous maps. `ωScottContinuous_cons` and `ωScottContinuous_single` let
`fun_prop` prove continuity through extension. `Env.bindOne` turns the meaning of an
argument that binds one variable into a continuous function of that variable.
`Env.abstraction` is the same map, written so that the kernel compares nested abstractions in
linear time.
`Env.map` applies a family of continuous maps along a sort map. `Env.transport` is
its instance for an equation of bundled
[`PointedDomain`](../../PolyFun/Control/Domain/Pointed.lean) carriers. With bottom
at every sort, `Env.fixGroup` ties a finite heterogeneous group with one least fixed
point; its unfolding and leastness laws apply to the whole environment. Environment
renaming commutes with extension, append, and `Env.map`. Consecutive maps compose at
each original binding position. `fixGroup_rename` handles ambient value renaming,
and `fixGroup_fusion` transports recursion through a strict continuous map that
commutes with whole-group unfolding.

[`Scoped.EnvRelation`](../../PolyFun/IPFunctor/Scoped/EnvRelation.lean) defines
`Env.Forall₂`, which relates two environments by binding position for any family of
relations and assumes no order on the values. `Env.LiftRel` is the form for two environments
of one context and a relation indexed by one sort. It is preserved by extension, append
and assembly, and by positional reindexing on either side (`Forall₂.reindex_left` and
`Forall₂.reindex_right`). `Env.Pointwise` is its instance for heterogeneous equality.
[`Scoped.DomainRelation`](../../PolyFun/IPFunctor/Scoped/DomainRelation.lean) derives
preservation by `Env.map` from the reindexing laws. Its `fixGroup_forall₂` carries a relation that is
admissible at corresponding sorts through a recursive group. Language-specific
errors and quantifier stages remain outside this generic layer.

The [polymorphic tutorial](../../Examples/Tutorials/ScopedFamily.lean) constructs
a finite identity under a type binder and proves erasure preservation for every
parameter renaming using `fold_map_rel`. It also demonstrates an ambient value
remaining free below a type binder and a value binder. Its `reindexAction` is the
identity at children that keep their context and parameter renaming below a type
binder, and it satisfies the whole substitution algebra. It has no Cryptol or cryptography
dependency. [Public API checks](../../PolyFunTest/ModuleAPI/ScopedFamily.lean)
and the separate documentation consumer exercise the same theorems through
ordinary imports. The public API checks also substitute a lambda below both binder
kinds, compare the exact term, and apply `subst_subst` and `substOne_subst_lift`
with `reindexAction_lawful`.

## Two-level binding families

[`ScopedSignature.Stacked τ k₀ H`](../../PolyFun/IPFunctor/Scoped/Stacked.lean) describes a
value-level language whose parameter contexts are the contexts of a type-level signature `τ`.
Its sorts are type-level terms of one kind `k₀`. A head is a shape from `H` together with
annotations: type-level terms, one per slot, each under its own type binders. A checked head
`Stacked.Op Θ s` stores its annotations and the proof that they compute the result sort `s`. It
also stores the side condition `WF`, which can carry the evidence of a coercion between two
types. The language gives the value binders, child sorts and result sort of each shape as
functions of the annotations, with one substitution equation for each.

From these equations, `toFamily`, `paramHom` (type-parameter substitution as a
`ScopedFamily.Hom`), `reindexAction` and `reindexAction_lawful` are derived once. So
`Stacked.subst_subst`, `Stacked.map_subst` and `Stacked.substOne_subst_lift` hold for every
stacked family. A child that binds no type parameter keeps its parent's value context
(`Stacked.enter [] = .keep`). A child below type binders weakens each ambient sort by
`Substitution.weakenMany`, which agrees with `Term.weaken` below one binder. `Stacked.node`
builds a node whose result sort is computed from its head, so the check is definitional.

Two-child type formers do not commute with substitution definitionally: their children are
selected by a match on the child index. Where a substituted type meets a type written
independently, as after an instantiation, a language uses a coercion head. Its side condition
`WF` carries the evidence that the two types agree in the sense the language chooses.

The [vectors tutorial](../../Examples/Tutorials/ScopedVectors.lean) builds size-indexed vectors
this way. Applications take terms in the ambient context with no coercion. A coercion's side
condition compares the shapes of the two evaluated types, with their lengths erased, at every
assignment. Its evidence is therefore `rfl` for any two vector types with one entry shape, such
as `[m + n]nat` and `[n + m]nat`, but also `[1]nat` and `[1000]nat`; no size arithmetic is
checked.

[`Scoped.StackedInterpretation`](../../PolyFun/IPFunctor/Scoped/StackedInterpretation.lean)
interprets a stacked family through evaluated heads. A `Stacked.Model` gives the type-level
interpretation `tyAlg`, value-level typing rules on evaluated annotations (`bindersV`, `sortV`,
`resultV`) and a value-level side condition `WFV`, with one coherence equation per rule in the
type-level meanings. The names follow the signature level: `Model.Interp V` is an ordinary
interpretation and `Model.denote` its fold, while `Model.DomainInterp D` is a continuous one,
over an unbundled family of omega-complete partial orders, and `Model.denoteDomain` its fold.
Both see a head only through its evaluated annotations and receive each child as a function
of the child's type arguments and fresh value binders. Two theorems need no proof for any
individual head:

- `Model.denoteDomain_map` and `denoteDomain_map_closed`: substituting type parameters in the
  syntax and then taking the meaning agrees with taking the meaning at the evaluated
  assignment;
- `Model.denoteDomain_related`: if a continuous and an ordinary interpretation are related by
  `DomainInterp.Related R` at every evaluated head, then every term has related meanings at
  every type assignment, in environments related by `Env.LiftRel`.

A coercion's carrier equation is stated in `WFV`, and the coercion's interpretation casts
there with `ContinuousHom.ofEq`; the relation of `denoteDomain_related` needs no other
invariance. `denote_stackedNode` and `denoteDomain_stackedNode` state one step of a meaning.
A large meaning is better computed by rewriting with them than by one `rfl` through several
instantiations.

The stacked meanings have no value-level renaming or substitution laws, which
`Term.denoteDomain` has at the signature level, and the ordinary fold `Model.denote` has no
counterpart of `denoteDomain_map`.

Spell value contexts in theorems about meanings as `τ.Term Θ k₀`, the spelling the generic
lemmas use. The vectors tutorial's `repSeven_three` states `denoteDomain_map_closed` for
`repSeven`, an application of a coerced instantiation. Defined with its value context written
through the tutorial's abbreviation, as `[] : List (TyTerm [.size] .scheme)`, the same
statement exceeds the default heartbeats: the elaborator unfolds both meanings instead of first
identifying the two spellings of the context. With the generic spelling it checks at once.
Smaller terms check with either spelling, because the cost is that of evaluating the meanings.

The [vectors tutorial](../../Examples/Tutorials/ScopedVectors.lean) relates a lazy call-by-name
meaning to a total evaluator with `denoteDomain_related`, and instantiates a size with
`denoteDomain_map_closed`.

`Stacked.Model.certifiedMeaning` certifies a term with one free value variable at a type
assignment, under the premises of `Term.certifiedMeaning`. A total evaluator can be its own
implementation, so its totality premise holds by definition. The vectors tutorial encodes numbers
and vectors of data faithfully and so certifies every term with one data input at every size
assignment (`certifiedEvaluator`).

## Importing typed syntax

`Scoped/Import` lets a frontend for an external language add typed terms of a binding signature
or a stacked family through the kernel, and have the kernel accept each one against its source.
The frontend decodes its source into a mirror type, elaborates each declaration in meta code into
a `Tree`, and names an erasure `erase : Term → Mirror`, an exposed fold. For each declaration `d`,
`importDecls` adds:

- `d`, the quoted term, as an exposed definition, whose type the kernel checks;
- `d.accepted : erase d = src`, by `Eq.refl` (the default) or by evaluating a `Decidable`
  instance, which the kernel decides;
- the frontend's equation lemmas, each by `Eq.refl`, with right sides written without syntax.

[`Import/Quote.lean`](../../PolyFun/IPFunctor/Scoped/Import/Quote.lean) turns a `Tree` into a
term. A node carries a `Head` of the frontend's table, usually `Head.const` of a smart
constructor. The quoter keeps scopes and writes variables, with every implicit argument
explicit. A child that enters type binders replaces the parameters and weakens the ambient sorts,
as `Stacked.enter` does. `Syntax.ofSignature` and `Syntax.ofStacked` cover both levels of a
stacked family, so annotations and terms use one quoter. The elaborator never compares
value-level types, so a mistake in a head table is a kernel type mismatch.

[`Import/Submit.lean`](../../PolyFun/IPFunctor/Scoped/Import/Submit.lean) is the only place that
adds declarations. In the import machinery and its tests, `check-modules.sh` rejects any other file
that names `addDecl`, `addDeclCore`, `addDeclWithoutChecking`, `addAndCompile`, `mkAuxLemma`,
`mkAuxTheorem`, `mkAuxDefinition` or `mkAuxDefinitionFor`. The match is textual, so a declaration
added by another route, such as elaborating a command, is outside it.
`submit` runs the kernel check synchronously, with `debug.skipKernelTC` off, within a positive
`Budget` of heartbeats, at most the ambient `maxHeartbeats` when that is positive, and compiles a
definition that should be compiled in the same synchronous step. When the kernel rejects a
declaration, `addDecl` keeps its statement as an axiom, even when the error is caught or
swallowed by `#guard_msgs`. `atomically`, the machinery's only handler, restores the environment
and rethrows, also after a heartbeat or recursion-depth limit, which an ordinary `try` does not
catch. A failed import therefore stops at the declaration, and the environment returns to its
state before that declaration: a kernel rejection, a compilation error, a frontend error or a
resource limit leaves none of the declaration's definitions, compiled code or fallback axioms,
while the declarations before it stay. Messages logged before the failure remain.
[`Import/Driver.lean`](../../PolyFun/IPFunctor/Scoped/Import/Driver.lean) runs a frontend in
commit mode, or in check mode, which adds and compiles nothing and reports the kernel's verdict on
each step. Rejection tests use check mode.

**Trust.** The kernel checks that each imported term has the type the frontend declares and that
each theorem is proved. It does not check that these statements say what the import should
establish: the frontend chooses them, and they are trusted. The trusted part of a frontend is
its declared type of each term, the two sides of each acceptance theorem and the statements of
its equation lemmas; the decoder from the external file to the mirror; the mirror's `ToExpr`
instances, which write the source as a term; and the exposed erasure. The source side of an
acceptance theorem must come from the decoded file, not from the term. Only the `Tree` quoted into
the term is untrusted: a mistake in it is a kernel type mismatch or a failed acceptance theorem.

Never set `debug.skipKernelTC` where imported declarations are accepted. With it set,
`addDecl` admits a declaration unchecked, and the declaration depends on no axiom, so neither
`#print axioms` nor the axiom sweep can see it. `submit` overrides the option for its own checks.
The kernel's heartbeats bound allocations, not time, so a budget is a deterministic regression
guard rather than a time limit; report times with `Config.report`.

Kernel acceptance unfolds only exposed bodies: the erasure, and for acceptance by `decide` the
mirror's derived decidable equality. Meta code that builds mirror values needs `public meta
import` of the mirror's module. Lake does not track the JSON files a frontend reads; declare them
with an `input_file` or `input_dir` target in the library's `needs` when they change between
builds.

The [toy JSON frontend](../../PolyFunTest/IPFunctor/Scoped/Import/Toy.lean) imports the
[vectors tutorial](../../Examples/Tutorials/ScopedVectors.lean)'s language, inserting a coercion
after each size instantiation. Its [fixtures](../../PolyFunTest/IPFunctor/Scoped/Import/ToyImport.lean)
cover acceptance by both proofs, an equation lemma, a wrong scheme and a mismatched source
rejected in check mode, a budget the kernel exhausts, and two failures in commit mode, a kernel
rejection and a declaration that the kernel accepts and the code generator cannot compile. Neither
leaves a declaration or an axiom behind. The validation wrapper's axiom sweep includes both
modules.
