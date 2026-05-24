/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Basic

/-!
# Two-Index (Indexed) Polynomial Functors

This file defines `IPFunctor I J`, an Atkey-style polynomial functor between indexed family
categories. Equivalently, it is the container form of the polynomial diagram

```
I ←—— E ——▶ B ——▶ J
```

denoting a functor `(I → Type) → (J → Type)`. The data is

* `A : J → Type` — the available head shapes at each output index `j : J`;
* `B : (j : J) → A j → Type` — the response (child) type for each shape;
* `src : (j : J) → (a : A j) → B j a → I` — the source index of each child.

The associated object action sends a family `X : I → Type` and an output index `j : J` to

```
P.Obj X j = Σ a : A j, (b : B j a) → X (src j a b)
```

so a child at position `(j, a, b)` is drawn from the fiber `X (src j a b)`.

## Endomorphic case

The free constructions of this library — `IFreeM`, `FreeM`, `FreeM₂` — and the indexed monad
structure only make sense when input and output indices coincide. The endomorphic
specialization `IPFunctor.Endo I := IPFunctor I I` carves this case out as a top-level
abbreviation, mirroring the way ordinary monads arise from endofunctors.

## Composition

The composition `Q ◃ P : IPFunctor I K` of `P : IPFunctor I J` and `Q : IPFunctor J K`
implements the functor composition `Q ∘ P : (I → Type) → (K → Type)`. See `comp` below.

## Pointers

* The state-indexed free monad on an `IPFunctor.Endo I` is defined in
  [`PolyFun/IPFunctor/Free/Family.lean`](Free/Family.lean) as `IFreeM`; its constant-family
  and equality-tagged specializations `FreeM` / `FreeM₂` live in
  [`PolyFun/IPFunctor/Free/Basic.lean`](Free/Basic.lean) and
  [`PolyFun/IPFunctor/Free/Indexed.lean`](Free/Indexed.lean).
* Indexed lenses, charts, and structural equivalences (each carrying a source-index
  preservation law) live in [`PolyFun/IPFunctor/Lens/Basic.lean`](Lens/Basic.lean),
  [`PolyFun/IPFunctor/Chart/Basic.lean`](Chart/Basic.lean), and
  [`PolyFun/IPFunctor/Equiv/Basic.lean`](Equiv/Basic.lean).
* When `J` has at most one element, `IPFunctor I J` reduces to an ordinary `PFunctor` via
  `IPFunctor.toPFunctor`; the unconditional Σ-bundled erasure is `IPFunctor.sigmaPFunctor`.
-/

@[expose] public section

universe uI uJ uK uA uB

/-- Atkey-style polynomial functor between indexed family categories. Given input index type
`I` and output index type `J`, `IPFunctor I J` packages the shapes available at each `j : J`,
the response type at each shape, and the source index (in `I`) of each child. -/
structure IPFunctor (I : Type uI) (J : Type uJ) where
  /-- The head type at each output index. -/
  A : J → Type uA
  /-- The child family of types, dependent on the output index and chosen shape. -/
  B : (j : J) → A j → Type uB
  /-- Source-index map: each child of position `(j, a, b)` is drawn from fiber `X (src j a b)`
  in the target family `X : I → Type`. -/
  src : (j : J) → (a : A j) → B j a → I

/-- Endomorphic specialization `IPFunctor I I`. This is the case where the polynomial action
is an endofunctor `(I → Type) → (I → Type)`, and free monads / indexed monads / `do`-notation
make sense. -/
abbrev IPFunctor.Endo (I : Type uI) : Type _ := IPFunctor.{uI, uI, uA, uB} I I

namespace IPFunctor

variable {I : Type uI} {J : Type uJ} {K : Type uK}

/-- Applying `P : IPFunctor I J` to an indexed family `X : I → Type` at output index `j : J`.
The child at position `⟨a, f⟩` and response `b` is the value `f b : X (P.src j a b)`. -/
@[coe]
def Obj (P : IPFunctor I J) (X : I → Type*) (j : J) : Type _ :=
  Σ a : P.A j, (b : P.B j a) → X (P.src j a b)

instance : CoeFun (IPFunctor I J) (fun _ => (I → Type*) → J → Type _) where
  coe := Obj

/-- The zero `IPFunctor`: no shapes are available at any output index. -/
instance (I : Type uI) (J : Type uJ) : Zero (IPFunctor.{uI, uJ, uA, uB} I J) where
  zero := { A _ := PEmpty, B _ _ := PEmpty, src _ _ := PEmpty.elim }

/-- The unit `IPFunctor`: a single trivial shape at each output index, with no continuation. -/
instance (I : Type uI) (J : Type uJ) : One (IPFunctor.{uI, uJ, uA, uB} I J) where
  one := { A _ := PUnit, B _ _ := PEmpty, src _ _ := PEmpty.elim }

instance : Inhabited (IPFunctor I J) := ⟨0⟩

/-- View an `IPFunctor I J` as a `PFunctor` when `J` has exactly one element. The single
fiber `P.A default` becomes the position type and `P.B default` the response. The source
map `P.src` is dropped — under `[Unique J]` the source index carries no information beyond
"there is exactly one place to be," so collapsing it loses nothing.

The constraint is `[Unique J]` rather than `[Inhabited J]` because a richer `J` would
have multiple fibers and silently picking the default one would discard observable
information; for arbitrary `J`, use [`sigmaPFunctor`](#IPFunctor.sigmaPFunctor) instead,
which Σ-bundles the index into positions and preserves every fiber. -/
@[reducible, inline]
def toPFunctor [Unique J] (P : IPFunctor I J) : PFunctor where
  A := P.A default
  B := P.B default

@[simp] lemma toPFunctor_zero [Unique J] :
    (0 : IPFunctor.{uI, uJ, uA, uB} I J).toPFunctor = 0 := rfl

@[simp] lemma toPFunctor_one [Unique J] :
    (1 : IPFunctor.{uI, uJ, uA, uB} I J).toPFunctor = 1 := rfl

/-- View an `IPFunctor` as a `PFunctor` by Σ-bundling the output index into each position.
Unlike `toPFunctor`, no shape information is lost — but positions become `Σ j : J, P.A j` and
the source map `P.src` is still not represented on the target side. Works for any input
and output index types (no `[Inhabited J]` required).

Used by the Σ-bundled forgetful map from indexed free trees into plain `PFunctor.FreeM`. -/
@[reducible, inline]
def sigmaPFunctor (P : IPFunctor I J) : PFunctor where
  A := Σ j : J, P.A j
  B := fun x => P.B x.1 x.2

/-! ## Composition

`Q ◃ P : IPFunctor I K` is the container realising the functor composition
`Q ∘ P : (I → Type) → (K → Type)`, for `P : IPFunctor I J` and `Q : IPFunctor J K`.

A position in `Q ◃ P` at output index `k : K` is a `Q`-shape `a : Q.A k` together with, for
each response `b : Q.B k a`, a `P`-shape at the source index `Q.src k a b`. A response is a
pair `(b, b')` with `b : Q.B k a` and `b' : P.B _ (f b)`; its source index is the source of
`b'` in the inner `P`. -/

/-- Composition of indexed polynomials. For `P : IPFunctor I J` and `Q : IPFunctor J K`,
`Q ◃ P : IPFunctor I K` is the container for the composite functor `Q ∘ P`. -/
def comp (Q : IPFunctor.{uJ, uK, uA, uB} J K) (P : IPFunctor.{uI, uJ, uA, uB} I J) :
    IPFunctor.{uI, uK, max uA uB, uB} I K where
  A k := Σ a : Q.A k, (b : Q.B k a) → P.A (Q.src k a b)
  B k := fun x => Σ b : Q.B k x.1, P.B (Q.src k x.1 b) (x.2 b)
  src k := fun x d => P.src (Q.src k x.1 d.1) (x.2 d.1) d.2

@[inherit_doc] scoped infixl:80 " ◃ " => IPFunctor.comp

end IPFunctor

/-! ## Deterministic transitions

When `P.src j a b` is independent of the response `b`, the source map collapses to a function
`next : (j : J) → P.A j → I`. Under this hypothesis, a single `liftA`-style step of the
free monad lands at a uniquely determined source index, which permits a specialized bind
operation and the deterministic `do`-notation in
[`PolyFun/IPFunctor/Notation/Deterministic.lean`](Notation/Deterministic.lean). -/

/-- An `IPFunctor` has *deterministic transitions* when `P.src j a b` is independent of the
response `b`. Equivalently, `(fun b => P.src j a b)` is a constant function for every shape `a`.

This is the structural condition that lets `liftA`-style steps of the single-index free monad
`IPFunctor.FreeM` land at a uniquely determined source index. -/
class IPFunctor.DeterministicTransitions {I : Type uI} {J : Type uJ}
    (P : IPFunctor.{uI, uJ, uA, uB} I J) where
  /-- The (unique) source index after taking shape `a` at output `j`. -/
  next : (j : J) → P.A j → I
  /-- `P.src j a b` agrees with `next j a` for every response `b`. -/
  spec : ∀ j a b, P.src j a b = next j a
