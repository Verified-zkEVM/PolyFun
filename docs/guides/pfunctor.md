# Polynomial Functors and `FreeM`

Polynomial interfaces separate the shape of a request from its possible
responses. This guide connects that data to programs, morphisms, and trees;
the linked source gives the precise universe parameters and laws.

## Why polynomial functors

A **polynomial functor** is a pair `⟨A, B⟩` where

- `A : Type*` is the *position* / *shape* type;
- `B : A → Type*` is the *direction* / *arity* family.

Concretely, a `PFunctor` is a generic notion of "branching tree shape":
each shape `a : A` chooses a branching arity `B a`. This single primitive
captures inductive types (`W`-types), free monads on signatures, M-types
(coinductive types), event signatures for interaction trees, and the kind
of dependent typing needed for protocol move spaces.

The Niu–Spivak *Poly* category (positions and directions composed via
`Σ` / `Π`) is the categorical home of all of these. PolyFun internalizes
enough of that category to model:

- free monads on signatures (`PFunctor.FreeM`);
- displayed families and decorations over them
  (`PFunctor.FreeM.Displayed`);
- branch paths through trees (`PFunctor.FreeM.Path`);
- finite typed prefixes selecting residual subtrees (`PFunctor.FreeM.Cursor`);
- the cofree comonad / M-type (`PFunctor.CofreeC`);
- lenses and charts between polynomial functors as morphisms of two
  natural categories on `Poly`;
- numeric and structural ornaments (`PFunctor.Bound`).

References:
[`REFERENCES.md`](../../REFERENCES.md). Hancock-Setzer 2000,
Altenkirch-Ghani-Hancock-McBride-Morris 2015 (*Indexed Containers*),
Niu–Spivak 2025 (*Polynomial Functors: A Mathematical Theory of Interaction*),
McBride 2010 / Dagand-McBride 2014 (displayed algebras / ornaments).

## Polynomial objects

Use Mathlib's `PFunctor.Obj.mk`, `.fst`, and `.snd` for values of `P.Obj α`.
Their simplification rules (`Obj.fst_mk`, `Obj.snd_mk`, and `PFunctor.map_eq`)
are the canonical constructor interface. Pattern matching and `cases` use
`Obj.rec`. Positions of an indexed sum `PFunctor.sigma F` have the same shape
of interface: build them with `sigma.mk i a`, project with `sigma.fst` and
`sigma.snd`, eliminate with `sigma.rec`, and rewrite their direction type with
`sigma.B_mk`. `sigma.mk i a` has type `(sigma F).A` at every transparency, so
statements about indexed-sum positions elaborate in ordinary-import consumers
and under `linter.tacticCheckInstances` without a local reducibility override
on `sigma`; prefer it to the anonymous constructor. Apply the projections as
`sigma.fst x` and `sigma.snd x`: field notation on a position resolves to
`Sigma.fst` and `Sigma.snd`, because the position type unfolds to a sigma type.
Other composite positions and directions that are genuine sigma types use the
ordinary sigma API.

Handlers combine along the same constructions: `Handler.sigma` answers an
indexed sum member by member, and `Handler.sum` (in
[`Handler/Sum.lean`](../../PolyFun/PFunctor/Handler/Sum.lean)) routes a binary
sum `P + Q` to one of two handlers. Interpreting a program relabelled into the
sum along `Lens.inl` uses only the left handler (`liftM_sum_mapLens_inl`), a
consequence of `FreeM.liftM_mapLens`: interpreting a relabelled program pulls
the handler back along the lens. Lenses between monomials, the shape of
input/output transformers and of proof-system context lenses, are built with
`Lens.ofMonomial`, `monomialMapFst`, and `monomialMapSnd` in
[`Lens/Monomial.lean`](../../PolyFun/PFunctor/Lens/Monomial.lean).

## Representables, Yoneda, and natural transformations

`Lens.fromPurePowerEquiv : Lens (y^S) Q ≃ Q.Obj S` is the Yoneda lemma for polynomials, and
`Lens.equivPiObj : Lens P Q ≃ ((a : P.A) → Q.Obj (P.B a))` reads a lens as its value on each
generic element `Obj.mk a id`. Lenses are exactly the natural transformations between
actions: the action `Lens.mapObj` is natural (`Lens.mapObj_map`), and every natural family
`η X : P.Obj X → Q.Obj X`, with components at the source's direction universe, is the action
of exactly one lens (`Lens.existsUnique_mapObj`), namely `Lens.ofNatural η`
(`Lens.mapObj_ofNatural`). `Lens` stays the carrier; convert a natural family once with
`Lens.ofNatural`. `Obj.punitEquiv` and `Obj.pemptyEquiv` compute `p(1) ≃ P.A` and
`p(0)`, and `Lens.purePowerMap` is the representable map `y^S ⇆ y^R` of a function `R → S`.

[`Equiv/Special.lean`](../../PolyFun/PFunctor/Equiv/Special.lean) presents every polynomial as
the sum of the representables at its directions (`Equiv.sigmaPurePower`) and defines the
pure-power (the book's representable), constant, linear, and monomial classes up to `≃ₚ`. `isPurePower_iff`,
`isConstant_iff`, `isLinear_iff`, and `isMonomial_iff` characterize them by positions and
directions.

[`Lens/Universal.lean`](../../PolyFun/PFunctor/Lens/Universal.lean) states the universal
properties of sums and products as hom-set equivalences (`Lens.sigmaEquiv`, `Lens.piEquiv` with
the projections `Lens.piProj`, and the binary `Lens.sumEquiv` and `Lens.prodEquiv`), and shows
that the actions of sums and products are sums and products of actions (`Obj.sigmaEquiv`,
`Obj.piEquiv`, `Obj.sumEquiv`, `Obj.prodEquiv`). It also reduces lenses into and out of the
special polynomials to functions: `Lens.fromLinearEquiv` and `Lens.fromConstEquiv` (with `homToConst`,
the adjoint quadruple between `Set` and `Poly`), `Lens.sectionEquiv` for sections `Lens p y`,
`Lens.toPurePowerEquiv` and `Lens.toMonomialEquiv` for lenses into representables and monomials,
and `Lens.sectionTensorEquiv` for sections of `p ⊗ q`.

## Monoidal structures

[`Lens/Coherence.lean`](../../PolyFun/PFunctor/Lens/Coherence.lean) states the coherence laws of
the parallel product `⊗` (pentagon, triangle, braiding naturality, symmetry, both hexagons) and of
the composition product `◃` (associator and unitor naturality, pentagon, triangle) at independent
universes. All of them hold by `rfl`. The same file proves that `◃` acts as the composite of
actions, `Obj.compEquiv : (P ◃ Q).Obj X ≃ P.Obj (Q.Obj X)`, with `◃ₗ` as the horizontal composite,
and splits composition powers with `Lens.Equiv.compNthAdd`.

[`Category/Monoidal.lean`](../../PolyFun/PFunctor/Category/Monoidal.lean) packages these as Mathlib
structures. Each structure has its own carrier, because a monoidal instance is keyed on its
carrier:

* `LensCat` is a `CartesianMonoidalCategory` for `*` and `1`;
* `TensorCat` is a `SymmetricCategory` for `⊗` and `y`;
* `CompCat.{u, v}` (polynomials at `{max u v, v}`) is a `MonoidalCategory` for `◃` and `y`.

Their coherence fields are the `rfl` lemmas above, and Mathlib's `monoidal` tactic closes
coherence goals in them. The carriers unfold to `PFunctor`, so the polynomial `⊗` from
`open scoped PFunctor` and Mathlib's monoidal `⊗` both elaborate on their objects. Work with the
Mathlib structures where PolyFun's scoped notation is not open.

## Where to start

| Task | Modules |
|---|---|
| Describe an interface and translate requests/replies | [Basic](../../PolyFun/PFunctor/Basic.lean), [lenses](../../PolyFun/PFunctor/Lens/Basic.lean), [charts](../../PolyFun/PFunctor/Chart/Basic.lean), [Yoneda](../../PolyFun/PFunctor/Lens/Yoneda.lean) |
| Write and interpret a well-founded program | [FreeM](../../PolyFun/PFunctor/Free/Basic.lean), [handlers](../../PolyFun/PFunctor/Handler.lean), [first tutorial](../tutorials/first-program.md) |
| Inspect or decorate a program | [Paths](../../PolyFun/PFunctor/Free/Path.lean), [cursors](../../PolyFun/PFunctor/Free/Cursor.lean), [displayed programs](../../PolyFun/PFunctor/Free/Displayed.lean) |
| Model stateful behavior | [Dynamical systems](../../PolyFun/PFunctor/Dynamical/Basic.lean), [resumable execution](execution.md#resumable-execution), [computation model guide](computation-models.md) |
| Compare possibly infinite trees | [M-types](../../PolyFun/PFunctor/M.lean), [resumptions](../../PolyFun/PFunctor/Resumption.lean) |
| Study the categorical structure | [Monoidal structures](../../PolyFun/PFunctor/Category/Monoidal.lean), [coherence](../../PolyFun/PFunctor/Lens/Coherence.lean), [Tensor internal hom](../../PolyFun/PFunctor/InternalHom.lean), [cartesian exponential](../../PolyFun/PFunctor/CartesianClosed.lean), [mathematical background](../reference/mathematical-background.md) |
| Relate free and cofree constructions | [Pattern runs on matter](../reference/pattern-runs-on-matter.md) |

Mathlib owns `PFunctor`, its object action, and W/M-type foundations. CSLib
owns the basic polynomial constructions (`A y^ B`, `C`, `linear`,
`selfMonomial`, `y^ B`, `y`, `0`, `1`, `P + Q` and `P * Q`), `PFunctor.FreeM`,
its fold `FreeM.foldFreeM`, and the equivalence `FreeM.equivWOfIsEmpty`
between a free monad with an empty leaf type and the W-type. PolyFun extends
those definitions instead of introducing parallel foundational types. The [repository map](../reference/repo-map.md)
explains the staging library `ToCslib` and the optional `ComplexityBackends`.

## CSLib's polynomial constructions

`PolyFun.PFunctor.Basic` re-exports `Cslib.Foundations.Data.PFunctor.Basic`,
and the constructions it supplies keep CSLib's transparency:

- `monomial`, `C`, `linear`, `selfMonomial`, `purePower` and `y` are reducible
  abbreviations of one structure literal, so `(A y^ B).B a` is `B` during
  elaboration, unification and instance search. `Unique y.A`,
  `Unique (y.B a)`, `Unique ((linear α).B a)`, `Unique (y^ β).A` and
  `IsEmpty ((C α).B a)` are found by unfolding, without dedicated instances.
  Simp's projection step computes `(C A).A`, `(y^ B).B a` and the other heads
  and children, so PolyFun's equations `C_A`, `C_B`, `y_A`, `y_B`,
  `linear_A`, `linear_B`, `selfMonomial_A`, `selfMonomial_B`, `purePower_A`
  and `purePower_B` are plain lemmas for `rw` and `simp only`.
- `P + Q` elaborates through CSLib's `instHAddPFunctor` to `PFunctor.add`, and
  `P * Q` through `instHMulPFunctor` to `PFunctor.prod`; both definitions are
  `implicit_reducible`. Instance search therefore does not see through `P + Q`:
  a `Unique ((P + Q).B (.inl a))` goal needs an explicit instance or a rewrite.
  PolyFun's named sum `PFunctor.sum` is a separate reducible structure literal
  with the same body, so `P + Q = PFunctor.sum P Q` holds by `rfl` but not at
  reducible and instance transparency. The homogeneous instance
  `instAddPFunctor` is defined by `sum`.
- CSLib's global simp lemmas include `hAdd_A` and `hAdd_B` (which rewrites
  `(P + Q).B t` to `Sum.rec P.B Q.B t` for every `t`, not only constructors),
  `hMul_A`, `hMul_B`, `zero_A`, `zero_B`, `one_A`, `one_B`, `C_pempty`,
  `C_punit`, `linear_punit`, `selfMonomial_punit`, `purePower_punit`,
  `add_eq_add` and `prod_eq_mul`.
- The universe parameters of `purePower` (and its alias `representable`) are
  `.{uB, uA}`, child universe first; those of `prod` and `instHMulPFunctor`
  are `.{uA₁, uA₂, uB₁, uB₂}`; `instZeroPFunctor` and `instOnePFunctor` take
  the child universe first.

Three rules follow from this transparency:

- Do not declare instances on the positions or directions of an abbreviated
  polynomial, such as `y.A` or `(linear α).B a`. Their keys reduce to `PUnit`
  or `PEmpty`, so they apply to every `Unique PUnit` or `IsEmpty PEmpty` goal
  and can leave universe metavariables behind; instance search already finds
  the `PUnit` and `PEmpty` instances by unfolding.
- Write implicit type arguments on simp left-hand sides in their reduced form,
  for example `(Sum.inl op : F.A ⊕ PUnit)` rather than an ascription through
  `(F + y).A`. Simp reduces `P.B a` to the concrete direction type before it
  consults its index when `P` is one of these abbreviations, so a lemma about
  a generic `P` whose left side carries `P.B a` in an implicit argument, as
  `FreeM.lift a` does, needs `no_index` on that argument, as in
  `Handler.Stateful.run_lift`, `FreeM.support_lift` and CSLib's
  `FreeM.foldFreeM_lift`. A `>>=` on such a left side is written
  `Bind.bind (α := no_index (P.B a))`, as in
  `FreeM.isRollBound_lift_bind_iff'`, and
  [`ConcreteSimp.lean`](../../PolyFunTest/PFunctor/ConcreteSimp.lean) tests
  each lift equation on a concrete interface. `no_index` does not help when an
  explicit argument whose type mentions `P.B a` precedes the lift, as the
  predicate of `FreeM.allOutputs_lift` does, because simp unifies that argument
  before `P` is known; the
  [upstream page](../development/upstream.md#remaining-abstraction-boundaries)
  lists the lemmas that still miss.
- Do not put `OfNat.ofNat`, `One.one` or `Zero.zero` in a simp set. `1` is
  literally `PUnit y^ PEmpty`, which `C_punit` folds back to `1`, so simp
  loops; use `inferInstanceAs` for the instance or a projection lemma such as
  `one_B` for the equation.

## Mental model

- `PFunctor` is a *small* gadget: just `(A : Type, B : A → Type)`. Almost
  every interesting structure in PolyFun is built by combining a few of
  these via `+` / `*` / `⊗` / `Σ` / `Π` / composition, or by taking the
  free monad / cofree comonad / lens / chart of one.
- `FreeM P` is the free monad on `P` (the upstream cslib type). Operationally
  it is the inductive type of well-founded `P`-branching trees with `α`-leaves,
  built from a `pure` leaf and a combined `liftBind` step. It is the syntax of
  "programs" in the signature `P`.
- `CofreeC P` is the cofree comonad on `P`. Coinductively, it is the
  type of possibly infinite, fully-decorated `P`-trees. `CofreeP P` packages the
  same data polynomially: an unlabelled M-tree is a position and each finite
  rooted vertex is a direction; `(CofreeP P).Obj X ≃ CofreeC P X` labels all
  such vertices by `X`. Its root/vertex-concatenation lenses form the cofree
  substitution comonoid, while `CofreeP.map` supplies the heterogeneous
  lens-level functorial action. `Comonoid.Hom` requires its two carrier
  universe pairs to agree. The current `CofreeP.mapHom` API ensures that by
  choosing a common generator universe pair, so both resulting comonoid
  universes are definitionally `max uA uB`. This API requires the shared
  maximum explicitly. `CofreeP.homEquiv` packages the cofree
  universal property at the same fixed-maximum boundary, while its underlying
  coiteration remains fully heterogeneous. `CofreeP.laxTensor` synchronizes
  two behavior trees node by node and proves the concrete naturality and
  monoidal coherence equations without installing an abstract monoidal-functor
  instance. PolyFun separately formalizes
  `LawfulMonad (FreeM P)` and `LawfulComonad (CofreeC F)`; those type-level
  structures are not the paper's polynomial module action. The latter is
  `FreeP.runOn p q : Lens (FreeP p ⊗ CofreeP q) (FreeP (p ⊗ q))`: it executes a
  finite pattern against potentially infinite matter, is natural in both
  inputs, agrees with the paper's convolution/free-universal construction
  `FreeP.xi`, and satisfies the concrete unit and associativity equations.
- `Lens P Q` and `Chart P Q` are the two natural categorical morphisms
  between polynomial functors. Lenses go `forward on positions, backward
  on directions`; charts go forward on both. Both categories are useful
  and distinct.
- `Displayed D s` is the dependent-types view of "decorating every node
  of a tree with extra data". `Decoration Γ s` is the special case where
  the data only depends on the local position.

## What lives where downstream

- `PolyFun/ITree/` (see [`itree.md`](itree.md)) builds interaction trees
  as the M-type of a one-step polynomial functor. It uses
  `PolyFun/PFunctor/M.lean` and the cofree apparatus.
- `PolyFun/Interaction/Basic/` (see [`interaction.md`](interaction.md))
  builds protocol `TypeTree`s as `PFunctor.FreeM TypeTree.basePFunctor PUnit`,
  i.e. `PUnit`-leaved free trees on a particular base polynomial. Most
  of the interaction framework is just a dependent-typed dressing on top
  of `FreeM` plus `Decoration` / `Displayed`.

If a concept appears redundant between layers, the substrate version
(here, in `PFunctor/`) is almost always the load-bearing one. Downstream
layers exist to give protocol-flavored names and ergonomics; the maths
lives in `PFunctor/Free/`, `PFunctor/Cofree.lean`, and `PFunctor/Cofree/`.

The execution API exposes `TraceList.positions` and `FreeM.Path.positions` for ordered input
observations, including repeated inputs. Prefer these over mapping a bare `Sigma.fst` across
the event carrier, and build or destructure paths through `Path.cons` / `Path.head` /
`Path.tail` rather than the anonymous constructor and projections of the underlying sigma.

## Object equality

Use Mathlib's `PFunctor.Obj.mk`, `Obj.fst`, `Obj.snd`, and `Obj.rec` when
constructing or eliminating the object action. `PFunctor/Obj.lean` supplies
`Obj.ext`, its generated `Obj.ext_iff`, and `Obj.mk.inj` / `Obj.mk.inj_iff` for
dependent equality. These use shape equality and heterogeneous equality of
child functions, without normalizing public statements to `Sigma`.
Positions and directions which are themselves Sigma types still use the
ordinary Sigma API. The indexed counterpart in `IPFunctor/Basic.lean` preserves
the source fiber of each child.

## Comonadic structure and pairing

`Comonad` supplies `Functor`, `Extract`, and `Extend`. `LawfulComonad` adds the
usual counit, associativity, and map-compatibility laws. `Coapplicative` is an
independent choice of context pairing, with its own law class; generic comonad
consumers do not obtain a pairing instance automatically. `EnvT` and `StoreT`
lift these interfaces separately. Concrete pairings retain their meaning:
streams zip pointwise, while `CofreeC` retains the left tree and the right root
value. A consumer using only pairing can ask for `Coapplicative` or the smaller
operation class it needs. A consumer already requiring `Comonad` should add
`Coseq` for pairing, rather than another independent `Coapplicative` assumption:
the latter also chooses `Functor` and `Extract` data and can create conflicting
instances. Concrete instances share those operations, but two arbitrary class
parameters do not assert that they agree.

The [Parliament walkthrough](../../Examples/Parliament/Docs/walkthrough.md) applies these
APIs to legal meeting inputs, finite prefixes with event labels, safety specifications,
and the application's resumption semantics. Its writer-handler erasure proof instantiates
`runChunk_natural` without changing the underlying application machine.
