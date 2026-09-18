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

The Spivak-Niu *Poly* category (positions and directions composed via
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
Spivak-Niu 2025 (*Polynomial Functors: A Mathematical Theory of Interaction*),
McBride 2010 / Dagand-McBride 2014 (displayed algebras / ornaments).

## Polynomial objects

Use Mathlib's `PFunctor.Obj.mk`, `.fst`, and `.snd` for values of `P.Obj α`.
Their simplification rules (`Obj.fst_mk`, `Obj.snd_mk`, and `PFunctor.map_eq`)
are the canonical constructor interface. Pattern matching and `cases` use
`Obj.rec`. The position and direction types of composite polynomials may
still be genuine sigma types; those use their own constructors and projections.

## Where to start

| Task | Modules |
|---|---|
| Describe an interface and translate requests/replies | [Basic](../../PolyFun/PFunctor/Basic.lean), [lenses](../../PolyFun/PFunctor/Lens/Basic.lean), [charts](../../PolyFun/PFunctor/Chart/Basic.lean) |
| Write and interpret a well-founded program | [FreeM](../../PolyFun/PFunctor/Free/Basic.lean), [handlers](../../PolyFun/PFunctor/Handler.lean), [first tutorial](../tutorials/first-program.md) |
| Inspect or decorate a program | [Paths](../../PolyFun/PFunctor/Free/Path.lean), [cursors](../../PolyFun/PFunctor/Free/Cursor.lean), [displayed programs](../../PolyFun/PFunctor/Free/Displayed.lean) |
| Model stateful behavior | [Dynamical systems](../../PolyFun/PFunctor/Dynamical/Basic.lean), [resumable execution](execution.md#resumable-execution), [computation model guide](computation-models.md) |
| Compare possibly infinite trees | [M-types](../../PolyFun/PFunctor/M.lean), [resumptions](../../PolyFun/PFunctor/Resumption.lean) |
| Study the categorical structure | [Tensor internal hom](../../PolyFun/PFunctor/InternalHom.lean), [cartesian exponential](../../PolyFun/PFunctor/CartesianClosed.lean), [mathematical background](../reference/mathematical-background.md) |
| Relate free and cofree constructions | [Pattern runs on matter](../reference/pattern-runs-on-matter.md) |

Mathlib owns `PFunctor`, its object action, and W/M-type foundations. CSLib
owns `PFunctor.FreeM`. PolyFun extends those definitions instead of introducing
parallel foundational types. The [repository map](../reference/repo-map.md)
explains the staging library `ToCslib` and optional adapters.

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
  `FreeP.runOn : FreeP p ⊗ CofreeP q ⇆ FreeP (p ⊗ q)`: it executes a
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
