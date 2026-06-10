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
| `PolyFun/Control/Monad/Graded.lean` | `gcast` transport helper and lemma suite; `GradedMonad`, `LawfulGradedMonad`; trivial `PUnit` grading of any monad; `GradedMonad.toIndexedMonad` (graded → indexed over a group) and its lawfulness |
| `PolyFun/GPFunctor/Basic.lean` | `GPFunctor` structure; `Zero` / `One` / `monomial` / `X`; homogeneous-component `Obj`; `mapGrade`; `toIPFunctor` + `DeterministicTransitions` instance |
| `PolyFun/GPFunctor/Free/Basic.lean` | the free graded monad `GFreeM`; bind / lift / map; `GradedMonad` and `LawfulGradedMonad` instances; interpretations `mapGM` (into any graded monad) and `mapM` (into a plain monad); grade erasure `erase` |
| `PolyFun/GPFunctor/Free/Indexed.lean` | the translation `toFreeM₂` into `IPFunctor.FreeM₂ P.toIPFunctor 1 g` and its `bind`-compatibility |
| `PolyFun/GPFunctor/Lens/Basic.lean` | graded lenses with `grade_eq`; `toIPLens`, `toPLens` |
| `PolyFun/GPFunctor/Chart/Basic.lean` | graded charts with `grade_eq`; `toIPChart`, `toPChart` |
| `PolyFun/GPFunctor/Equiv/Basic.lean` | structural equivalences `≃ᵍ` with `grade_eq`; `toIPEquiv` |
| `PolyFun/GPFunctor/Examples.lean` | worked examples over `Multiplicative ℕ` (cost grading) |

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
the path-product encoding is reached only by the one-way translation
`GFreeM.toFreeM₂` (see below).

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
  grade. `erase` is a monad morphism (`erase_bind`).
- **Indexed image** (`GPFunctor.toIPFunctor`, `[Mul G]`): the state-indexed
  polynomial on `G` itself with constant shapes and
  `src g a b = g * P.grade a`, reading the state as the accumulated grade.
  Per-shape grading makes the source map response-independent, so the image
  satisfies `IPFunctor.DeterministicTransitions` — per-shape grading embeds
  into the deterministic-transitions fragment of the indexed theory.
- **Translation** (`GFreeM.toFreeM₂`): lands in
  `IPFunctor.FreeM₂ P.toIPFunctor 1 g α`. It is a *translation, not an
  equivalence* (see above); `toFreeM₂_bind` shows it is a morphism of monad
  structure. The implementation is *Forded* — `toFreeM₂From k` takes a proof
  `k * g = t` instead of landing at the syntactic `k * g` — which absorbs all
  monoid-identity transports into `FreeM₂` leaf witnesses
  (`FreeM₂.pureCast`) and lets the `bind`-compatibility induction close
  without `mul_assoc` transport.
- **Graded → indexed for monads** (`GradedMonad.toIndexedMonad`,
  `[Group G]`): `IxM i j α := M (i⁻¹ * j) α`, fulfilling the relationship
  documented in `Control/Monad/Indexed.lean`. Lawfulness is
  `GradedMonad.toIndexedMonad_lawful`.

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
counterpart on the underlying containers (`toPLens` / `toPChart`).

There is also a structure-only relabeling `GPFunctor.mapGrade (φ : G → H)`
requiring no `MonoidHom` — the underlying container is unchanged.

## Limitations / Future Work

- **No composition product `◃`.** A composite position `⟨a, f⟩` would carry
  grade `Q.grade a * P.grade (f b)`, which varies with the response — per-
  shape grading is not closed under composition. The composite exists on the
  `toIPFunctor` images.
- **`toFreeM₂` is not an equivalence.** For cancellative `G` (in particular
  groups) it is injective and should upgrade to an equivalence; not yet
  formalized.
- **`MonoidHom` grade refinement.** `mapGrade` is structure-only; the
  free-monad-level refinement `GFreeM P g α → GFreeM (P.mapGrade φ) (φ g) α`
  for `φ : G →* H` (one `map_mul` cast per node) is future work.
- **No `do`-notation flavor.** Grade unification through `g * h` and `1` is
  harder than `FreeM₂`'s positional state unification and needs its own
  elaborator; build programs with `gbind` / `GFreeM.liftA` for now.
- **`mapGM` / `mapM` universe constraint.** Responses live in `Type uB`, so
  interpretation targets are constrained to `m : G → Type uB → Type w` /
  `m : Type uB → Type w`, mirroring the `IPFunctor.FreeM₂.mapM` discipline.
