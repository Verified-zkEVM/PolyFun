# Mathematical background and scope

PolyFun uses polynomial interfaces as a common representation for typed
interaction. The [bibliography](../../REFERENCES.md) gives public references;
the linked Lean modules determine which statements are formalized. This page
collects the useful correspondences without treating a literature analogy as
a proved equivalence.

## Polynomial interfaces

A polynomial has positions `A` and directions `B : A → Type`. Its action on
`X` is `Σ a, B a → X`: choose a position and give a continuation for every
direction. For interaction, positions are requests and directions are their
possible replies. A lens maps positions forward and directions backward;
a chart maps both forward. These are different notions of morphism.

[Mathlib's polynomial type](../../PolyFun/PFunctor/Basic.lean) underlies this
representation. [Indexed polynomials](../guides/ipfunctor.md) add a source
index to each direction, following the indexed-container viewpoint.

## Products and internal homs

| Construction | Meaning | Source |
|---|---|---|
| `p * q` | Categorical product for polynomial lenses | [Basic](../../PolyFun/PFunctor/Basic.lean) |
| `p ⊗ q` | Tensor product of polynomials | [Basic](../../PolyFun/PFunctor/Basic.lean) |
| `p ◃ q` | Substitution/composition product | [Basic](../../PolyFun/PFunctor/Basic.lean) |
| `ihom q r` | Tensor internal hom; positions are lenses `q ⇆ r` | [InternalHom](../../PolyFun/PFunctor/InternalHom.lean) |
| `exp q r` | Cartesian exponential for `*` | [CartesianClosed](../../PolyFun/PFunctor/CartesianClosed.lean) |

The two curry/uncurry constructions serve different products. A proof about
`Lens (p ⊗ q) r` uses the tensor internal hom; it is not an application of the
cartesian exponential. Likewise, `OpenTheory.IsCompactClosed` states laws of
an open-system model, not compact closure of the polynomial lens category.

## Induction, coinduction, and programs

- `FreeM P α` is the well-founded request tree with return values in `α`,
  represented by a W-type and supplied by CSLib.
- `Resumption P α` is its possibly infinite M-type counterpart. The exact
  well-founded-fragment equivalence is in
  [Resumption.WellFounded](../../PolyFun/PFunctor/Resumption/WellFounded.lean).
- `ITree P α` adds explicit silent steps. Strong bisimulation identifies
  the same M-type behavior; weak bisimulation can ignore finite silent
  prefixes. It does not identify every diverging behavior with a return.
- A `DynSystem S P` makes the implementation state `S` explicit. Its behavior
  map into an M-type forgets that representation, while simulation can relate
  different state spaces.

Well-foundedness does not supply one uniform natural-number bound for an
infinitely branching tree. See [computation models](../guides/computation-models.md)
and [execution](../guides/execution.md) before using a qualitative termination
result as a resource bound.

## Free and cofree algebra

[Substitution monoids](../../PolyFun/PFunctor/SubstMonoid.lean) package monoids
for `◃`. [Free.Universal](../../PolyFun/PFunctor/Free/Universal.lean) provides
the free substitution-monoid universal property. Polynomial comonoids and
their homomorphisms provide the categorical setting for cofree behavior.

The “pattern runs on matter” construction pairs free programs with cofree
behavior. Its interaction map and dependent path action are explained in
[the focused reference](pattern-runs-on-matter.md). This is an action/pairing;
it is not a claim that `FreeM` and `CofreeC` form an adjunction with each other.
The free and cofree universal properties have their own domains and codomains.

[Comonoid.Category](../../PolyFun/PFunctor/Comonoid/Category.lean) extracts
categorical structure from a polynomial comonoid and relates homomorphisms
to retrofunctor laws. This should not be read as a packaged equivalence of
all categories with polynomial comonoids. Similarly, individual tensor and
duoidal coherence laws do not by themselves assert a complete abstract
monoidal-category packaging or a bicomodule theory.

## Protocol and open-system interpretations

Hancock–Setzer interaction interfaces motivate the command/response view.
`TypeTree` specializes a free tree to protocol move types; decorations attach
roles, observations, strategies, or samplers to its nodes. It is distinct
from the potentially infinite `ITree` computation datatype.

[Parallel composition](parallel-composition.md) explains the interpretation
of one-sided and synchronized joint composition. [Open systems](../guides/open-systems.md) gives
the paper-to-code ledger for contextual emulation and the precise assumptions
on observations and schedulers. Those generic laws are reused by VCVio's
cryptographic interpretations; the [ownership guide](../guides/polyfun-and-vcvio.md)
explains the additional semantics and adequacy obligations.
