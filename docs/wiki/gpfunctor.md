# Graded Polynomial Functors (`PolyFun/GPFunctor/`)

This page covers the graded polynomial functor layer: `GPFunctor G`, its free
graded monad `GFreeM`, the `GradedMonad` / `LawfulGradedMonad` classes in
`PolyFun/Control/Monad/Graded.lean`, the grade-transport (`gcast`) discipline,
morphisms with grade preservation, and the connections to the `PFunctor` and
`IPFunctor` layers. The worked-examples companion is
[`PolyFun/GPFunctor/Examples.lean`](../../PolyFun/GPFunctor/Examples.lean).

## Why Graded Polynomial Functors

A **graded monad** over a monoid `G` is a family `M : G → Type → Type` with

```text
gpure : α → M 1 α
gbind : M g α → (α → M h β) → M (g * h) β
```

The grade tracks a quantity that accumulates multiplicatively under
sequencing — cost, effect footprint, trace length. The polynomial-functor
side of this story is a container whose *shapes carry grades*:

```lean
structure GPFunctor (G : Type uG) extends PFunctor.{uA, uB} where
  grade : A → G
```

Grading is **per shape**: the grade depends only on the position `a : A`,
never on the response `b : B a`. This matches the graded-theories literature
(each operation of a graded signature carries one grade) and contrasts with
`IPFunctor`, whose source map `src` does depend on the response.

No algebraic structure is required on `G` by the structure itself, mirroring
how `IPFunctor` puts no structure on its index types. `[Mul G]` / `[One G]` /
`[Monoid G]` appear only on the constructions that need them.

## File Index

| File | Contents |
| --- | --- |
| `PolyFun/Control/Monad/Graded.lean` | `gcast` transport helper and lemma suite; `GradedMonad`, `LawfulGradedMonad`; `GradedMonadHom`; trivial `PUnit` grading of any monad; `GradedMonad.toIndexedMonad` (graded → indexed over a group) and its lawfulness |
| `PolyFun/GPFunctor/Basic.lean` | `GPFunctor` structure; `Zero` / `One` / `monomial` / `X` / `ofPFunctor`; homogeneous-component `Obj` and its decomposition `sigmaObjEquiv`; `mapGrade`; `toIPFunctor` + `DeterministicTransitions` instance |
| `PolyFun/GPFunctor/Free/Basic.lean` | the free graded monad `GFreeM`; bind / lift / map; `GradedMonad` and `LawfulGradedMonad` instances; interpretations `mapGM` (into any graded monad) and `mapM` (into a plain monad); freeness (`mapGMHom`, `GradedMonadHom.eq_mapGM`); grade erasure `erase` and its section `ofFreeM` (an equivalence over `PUnit`, `equivFreeM`) |
| `PolyFun/GPFunctor/Free/Indexed.lean` | the translation `toFreeM₂` into `IPFunctor.FreeM₂ P.toIPFunctor 1 g` and its `bind` / `mapM` compatibility; injectivity over a left-cancellative monoid; the equivalence `equivFreeM₂` over a group |
| `PolyFun/GPFunctor/Free/Lens.lean` | transport `GFreeM.mapLens` along graded lenses; functoriality, `bind`-compatibility, and naturality in `erase` / `toFreeM₂`; handler pullback `mapGM_mapLens` |
| `PolyFun/GPFunctor/Free/MapGrade.lean` | grade reindexing `GFreeM.mapGrade` along a `MonoidHom`; functoriality, `bind`-compatibility up to `map_mul`, invisibility to `erase`, commutation with `mapLens` |
| `PolyFun/GPFunctor/Free/Path.lean` | path-product soundness: `pathProd` and `GFreeM.pathProd_erase` |
| `PolyFun/GPFunctor/Lens/Basic.lean` | graded lenses with `grade_eq`; `toIPLens`, `toPLens` (both functorial); `Lens.mapGrade`, `Lens.ofPLens`; induced equivalences `Lens.Equiv.toIPEquiv` / `toPEquiv` |
| `PolyFun/GPFunctor/Chart/Basic.lean` | graded charts with `grade_eq`; `toIPChart`, `toPChart` (both functorial); `Chart.mapGrade`, `Chart.ofPChart`; induced equivalences |
| `PolyFun/GPFunctor/Equiv/Basic.lean` | structural equivalences `≃ᵍ` with `grade_eq`; `toIPEquiv` |
| `PolyFun/GPFunctor/Examples.lean` | worked examples over `Multiplicative ℕ` (cost grading) and `Multiplicative ℤ` (the group case) |
| `PolyFun/IPFunctor/Free/Lens.lean` | the indexed side of lens transport: `IFreeM.castPre` / `IFreeM.mapLens` and the `FreeM` / `FreeM₂` specializations |

## The Free Graded Monad `GFreeM`

```lean
inductive GFreeM [Monoid G] (P : GPFunctor G) : G → Type v → Type _
  | pure {α} (x : α) : GFreeM P 1 α
  | roll {α} {g : G} (a : P.A) (r : (b : P.B a) → GFreeM P g α) :
      GFreeM P (P.grade a * g) α
```

`GFreeM P g α` is a tree over the underlying container of total grade `g`:
leaves are at the trivial grade, and a node contributes its shape's grade on
top of the (uniform) remaining grade of its branches.

### Uniform sibling grades are what freeness means

`roll` requires every branch to carry the *same* remaining grade. This is not
a convenience restriction — it is the shape of a graded algebra for `P`,
whose operations are `(P.B a → A g) → A (P.grade a * g)` with a single `g`
across branches (mirroring `gbind`, whose continuation `α → M h β` has a
single grade `h`). `GFreeM` is the initial such algebra, witnessed by the
**cast-free** interpretation into any graded monad:

```lean
GFreeM.mapGM : ((a : P.A) → m (P.grade a) (P.B a)) → GFreeM P g α → m g α
```

The alternative "path-product" reading — trees in which every root-to-leaf
*product* of grades equals `g` — is the two-index indexed free monad
`IPFunctor.FreeM₂ P.toIPFunctor 1 g α`. Over a non-cancellative monoid that
object is strictly larger: with `x * y = x * z` and `y ≠ z`, a grade-`x` node
may have branches whose own products are `y` and `z`; and a childless node
inhabits the path-product object at *every* grade. Neither tree interprets
into a general graded monad, which is why `GFreeM` is a direct inductive and
the path-product encoding is reached only by the translation
`GFreeM.toFreeM₂` (see below). The gap is governed exactly by
cancellativity: the translation is injective over a left-cancellative monoid
(`toFreeM₂_injective`) and an equivalence over a group (`equivFreeM₂`).

Freeness is also literal: `mapGM` into a lawful graded monad bundles as a
`GradedMonadHom` (`GFreeM.mapGMHom`), and *any* graded monad morphism out of
`GFreeM P` is determined by its action on the lifted shapes
(`GradedMonadHom.eq_mapGM`, requiring no lawfulness of the target).

### Comparison

| | `PFunctor.FreeM P α` | `GFreeM P g α` | `IPFunctor.FreeM₂ P s t α` |
| --- | --- | --- | --- |
| index discipline | none | total grade `g` (multiplicative) | pre/post states `s`, `t` (positional) |
| `pure` | any | at `1` | at diagonal `s = t` |
| bind law transport | none (exact) | `gcast` along monoid identities | none (exact) |
| canonical class | `LawfulMonad` | `LawfulGradedMonad` | `LawfulIndexedMonad` |
| interpretation | `mapM` | `mapGM` / `mapM` | `mapM` |

## The `gcast` Transport Discipline

For a generic monoid, `1 * h`, `g * 1`, and `(g₁ * g₂) * g₃` do not reduce,
so the graded monad laws cannot be exact equalities. All transport is
funneled through one helper:

```lean
def gcast (e : g = h) (x : M g α) : M h α := e ▸ x
```

The laws keep the compound term on the left and the cast on the right:

```lean
gbind (gpure a) f  = gcast (one_mul h).symm (f a)
gbind x gpure      = gcast (mul_one g).symm x
gbind (gbind x f) k = gcast (mul_assoc g₁ g₂ g₃).symm (gbind x fun a => gbind (f a) k)
```

The simp normal form floats casts to the root (`roll_gcast`,
`bind_gcast_left`, `bind_gcast_right`, `gbind_gcast_left`,
`gbind_gcast_right`), fuses adjacent casts (`gcast_gcast`), and discards
reflexive casts (`gcast_rfl`). Because `gcast` is a bare `Eq.rec`, a goal
whose two sides become a single cast between syntactically equal grades
closes by definitional proof irrelevance — this is the endgame of every law
proof in the layer. Interpretations *out* of `GFreeM` (`mapGM`, `mapM`,
`erase`) are cast-free; `bind_liftA` shows the casts of `liftA` + `bind`
collapsing to `roll` on the nose. Over a concrete monoid such as
`Multiplicative ℕ` the grade arithmetic is definitional and whole programs
reduce to transparent nested `roll` trees by `rfl`
(see `Examples.lean`).

## Connections To The Other Layers

- **Forget grades** (`GPFunctor.toPFunctor`, `GFreeM.erase`): project to the
  underlying container / plain free monad. No `[Unique]` hypotheses are
  needed (unlike the indexed erasures) because shapes never depended on the
  grade. `erase` is a monad morphism (`erase_bind`), and the plain
  interpretation factors through it (`mapM_eq_erase_mapM`).
- **Trivial grading** (`GPFunctor.ofPFunctor`, `GFreeM.ofFreeM`): every
  container is trivially graded with all shapes at grade `1`, and every
  plain tree embeds as a trivially graded tree sectioning `erase`
  (`erase_ofFreeM`). Over the one-element monoid the embedding is an
  equivalence (`GFreeM.equivFreeM`): `PFunctor.FreeM` is the trivially
  graded fragment of `GFreeM`.
- **Indexed image** (`GPFunctor.toIPFunctor`, `[Mul G]`): the state-indexed
  polynomial on `G` itself with constant shapes and
  `src g a b = g * P.grade a`, reading the state as the accumulated grade.
  Per-shape grading makes the source map response-independent, so the image
  satisfies `IPFunctor.DeterministicTransitions` — per-shape grading embeds
  into the deterministic-transitions fragment of the indexed theory.
- **Translation** (`GFreeM.toFreeM₂`): lands in
  `IPFunctor.FreeM₂ P.toIPFunctor 1 g α`. It is a *translation, not an
  equivalence* in general (see above); `toFreeM₂_bind` shows it is a
  morphism of monad structure, and `toFreeM₂From_mapM` that interpretation
  into a plain monad factors through it. The implementation is *Forded* —
  `toFreeM₂From k` takes a proof `k * g = t` instead of landing at the
  syntactic `k * g` — which absorbs all monoid-identity transports into
  `FreeM₂` leaf witnesses (`FreeM₂.pureCast`) and lets the
  `bind`-compatibility induction close without `mul_assoc` transport.
- **Cancellativity** (`GFreeM.toFreeM₂From_inj`, `GFreeM.toFreeM₂_injective`,
  `[IsLeftCancelMul G]`): the translation is injective. The grade equality
  comes from cancelling the Forded proofs, never from the induction, which
  also covers childless shapes.
- **The group case** (`GFreeM.ofFreeM₂`, `GFreeM.equivFreeM₂`, `[Group G]`):
  the accumulated grade can be divided off, so an indexed tree from
  accumulator `s` to `t` reconstructs a graded tree of grade `s⁻¹ * t`, and
  `GFreeM P g α ≃ FreeM₂ P.toIPFunctor 1 g α` — graded trees and
  accumulated-grade indexed trees are the same data on the group fragment.
- **Graded → indexed for monads** (`GradedMonad.toIndexedMonad`,
  `[Group G]`): `IxM i j α := M (i⁻¹ * j) α`, fulfilling the relationship
  documented in `Control/Monad/Indexed.lean`. Lawfulness is
  `GradedMonad.toIndexedMonad_lawful`.

## Path-Product Soundness

After erasure only the plain tree remains, but the grading of the underlying
container still assigns each root-to-leaf path a product of shape grades.
[`PolyFun/GPFunctor/Free/Path.lean`](../../PolyFun/GPFunctor/Free/Path.lean)
shows the type-level grade is exactly that product, on *every* path:

```lean
pathProd : (s : P.toPFunctor.FreeM α) → PFunctor.FreeM.Path s → G
GFreeM.pathProd_erase : ∀ (x : GFreeM P g α) (p : Path x.erase), pathProd P x.erase p = g
```

so the grade index is not an annotation but the runtime cost along every
execution path, and in particular the path product of an erased graded tree
is path-invariant (`pathProd_eq_pathProd`).

## Morphisms

`Lens` / `Chart` / `Equiv` mirror their `IPFunctor` counterparts with the
source-index preservation law replaced by **grade preservation**, e.g.

```lean
structure Lens (P Q : GPFunctor G) where
  toFunA   : P.A → Q.A
  toFunB   : ∀ a, Q.B (toFunA a) → P.B a
  grade_eq : ∀ a, P.grade a = Q.grade (toFunA a)
```

`grade_eq` is an equality of grade *values*, not types, so concrete morphisms
discharge it by `rfl`; because it mentions no responses it is strictly
simpler than `src_eq` (e.g. `Equiv.symm` needs only `Equiv.apply_symm_apply`
on the grade side). Each morphism induces its indexed counterpart on the
`toIPFunctor` images (`toIPLens` / `toIPChart` / `toIPEquiv`, with `src_eq`
given by `congrArg (g * ·) ∘ grade_eq`) and, for lenses and charts, the plain
counterpart on the underlying containers (`toPLens` / `toPChart`); both
inductions are functorial (`toIPLens_id` / `toIPLens_comp`, `toPLens_id` /
`toPLens_comp`, and the chart analogues), so lens/chart equivalences induce
equivalences on the images (`Lens.Equiv.toIPEquiv` / `toPEquiv`,
`Chart.Equiv.toIPEquiv` / `toPEquiv`). Plain lenses and charts lift to the
trivial grading (`Lens.ofPLens` / `Chart.ofPChart`), and grades relabel along
any `φ : G → H` (`Lens.mapGrade` / `Chart.mapGrade`) — no `MonoidHom` needed
at the structure level, matching `GPFunctor.mapGrade`.

### Transport of free graded trees

A graded lens acts on free graded trees
([`PolyFun/GPFunctor/Free/Lens.lean`](../../PolyFun/GPFunctor/Free/Lens.lean)):

```lean
GFreeM.mapLens : Lens P Q → GFreeM P g α → GFreeM Q g α
```

with one `gcast` along `grade_eq` per node — definitionally invisible for
concrete lenses whose `grade_eq` is `rfl`. Transport is functorial
(`mapLens_id`, `mapLens_comp`), a morphism of graded monad structure
(`mapLens_bind`), and *natural in both forgetful maps*:

```lean
erase_mapLens      : (x.mapLens l).erase = x.erase.mapLens l.toPLens
toFreeM₂_mapLens   : toFreeM₂ (x.mapLens l) = (toFreeM₂ x).mapLens l.toIPLens
```

where the indexed side uses `FreeM₂.mapLens` from
[`PolyFun/IPFunctor/Free/Lens.lean`](../../PolyFun/IPFunctor/Free/Lens.lean)
(defined once on the primitive `IFreeM`, with the propositional `src_eq`
absorbed by the pre-state transport `castPre`). On the interpretation side,
`mapGM_mapLens` pulls a shape handler back along a lens: the image handler is
`gmap`ped along the backward response map and transported along `grade_eq`.

### Grade reindexing of free graded trees

For `φ : G →* H`, the free-monad-level refinement of `GPFunctor.mapGrade`
lives in
[`PolyFun/GPFunctor/Free/MapGrade.lean`](../../PolyFun/GPFunctor/Free/MapGrade.lean):

```lean
GFreeM.mapGrade : (φ : G →* H) → GFreeM P g α → GFreeM (P.mapGrade φ) (φ g) α
```

with one `gcast` along `map_one` / `map_mul` per constructor. Reindexing is
functorial (`mapGrade_id`, `mapGrade_mapGrade`), a morphism of graded monad
structure up to `map_mul` transport (`mapGrade_bind`), invisible to grade
erasure (`erase_mapGrade`), and commutes with lens transport
(`mapGrade_mapLens`, via the structure-level `Lens.mapGrade`).

## Limitations / Future Work

- **No composition product `◃`.** A composite position `⟨a, f⟩` would carry
  grade `Q.grade a * P.grade (f b)`, which varies with the response — per-
  shape grading is not closed under composition. The composite exists on the
  `toIPFunctor` images.
- **No `do`-notation flavor.** Grade unification through `g * h` and `1` is
  harder than `FreeM₂`'s positional state unification and needs its own
  elaborator; build programs with `gbind` / `GFreeM.liftA` for now.
- **`mapGM` / `mapM` universe constraint.** Responses live in `Type uB`, so
  interpretation targets are constrained to `m : G → Type uB → Type w` /
  `m : Type uB → Type w`, mirroring the `IPFunctor.FreeM₂.mapM` discipline.
  The same constraint pins the value universe of `mapGMHom` and of the
  freeness theorem `GradedMonadHom.eq_mapGM`.

## A `gcast` Matching Gotcha

When a definition introduces a `gcast` whose proof's *type* is written in the
`φ`-pushed form (`φ (P.grade a) * φ g = …`), downstream `simp` lemmas whose
patterns mention the projection form (`(P.mapGrade φ).grade a * φ g`, as in
`bind_roll` or `gcast_gcast`) fail to match at reducible transparency, and
cast-fusion stalls. State such casts with a `show … from …` ascription in the
projection form — see `GFreeM.mapGrade` in
[`PolyFun/GPFunctor/Free/MapGrade.lean`](../../PolyFun/GPFunctor/Free/MapGrade.lean).
Residual goals of the shape `gcast p₁ T = gcast p₂ T` (proof-irrelevant
casts, definitionally equal implicits) close by `rfl`, which `simp` does not
attempt at that transparency.
