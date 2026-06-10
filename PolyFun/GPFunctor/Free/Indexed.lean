/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.GPFunctor.Free.Basic
public import PolyFun.IPFunctor.Free.Indexed

/-!
# Translating the Free Graded Monad into the Two-Index Indexed Free Monad

A graded polynomial `P : GPFunctor G` induces a state-indexed polynomial `P.toIPFunctor` on
`G` itself, reading the state as the accumulated grade. This file translates the free graded
monad into the two-index free monad of that indexed image:

```
toFreeM₂ : GFreeM P g α → IPFunctor.FreeM₂ P.toIPFunctor 1 g α
```

sending a grade-`g` tree to an accumulated-grade tree that starts at `1` and whose every leaf
is forced (by the `FreeM₂` leaf witness) to sit at `g`.

## A translation, not an equivalence

`FreeM₂ P.toIPFunctor 1 g α` is the *path-product* object: trees in which every root-to-leaf
product of grades equals `g` propositionally. Over a non-cancellative monoid this is strictly
larger than `GFreeM P g α`:

* if `x * y = x * z` with `y ≠ z`, a node of grade `x` may have one branch whose own grade
  product is `y` and a sibling at `z` — all paths agree after the prefix `x`, but the
  siblings share no remaining grade, so no `GFreeM` tree maps onto it;
* a childless node (empty response type) inhabits `FreeM₂ P.toIPFunctor 1 g α` for *every*
  `g`, but `GFreeM` trees through that node only realize grades of the form
  `P.grade a * g'`.

Consequently `toFreeM₂` is not an equivalence in general (for cancellative `G` — in
particular for groups — it is injective; upgrading it to an equivalence there is future
work), and the path-product object supports no interpretation into a general graded monad,
which is why `GFreeM` is defined directly rather than as this encoding.

## Fording

`toFreeM₂` is the `k = 1` instance of `toFreeM₂From k`, which translates relative to an
arbitrary starting accumulator `k` and is *Forded*: rather than landing at the syntactic
post-state `k * g`, it takes a proof `k * g = t` and lands at `t`. All monoid-identity
transports are thereby absorbed into the `FreeM₂` leaf witnesses (via `FreeM₂.pureCast`) and
into the proof argument, so the translation itself is cast-free and the compatibility lemma
`toFreeM₂From_bind` can quantify over the intermediate accumulator, letting its induction
close without transport along `mul_assoc`.
-/

@[expose] public section

universe uG uA uB v

namespace GPFunctor

namespace GFreeM

variable {G : Type uG} [Monoid G] {P : GPFunctor.{uG, uA, uB} G} {α β : Type v}

/-! ## The translation -/

/-- Translate a grade-`g` tree into the two-index free monad over `P.toIPFunctor`, relative
to a starting accumulator `k`. Forded: lands at any `t` provably equal to `k * g`, with the
proof absorbed into the leaf witnesses. -/
def toFreeM₂From : (k : G) → {g : G} → GFreeM P g α → {t : G} → k * g = t →
    IPFunctor.FreeM₂ P.toIPFunctor k t α
  | k, _, .pure x, _, e => IPFunctor.FreeM₂.pureCast ((mul_one k).symm.trans e) x
  | k, _, .roll a r, _, e =>
      IPFunctor.FreeM₂.roll (P := P.toIPFunctor) a
        (fun b => toFreeM₂From (k * P.grade a) (r b) ((mul_assoc k (P.grade a) _).trans e))

/-- The canonical translation: start the accumulator at `1`, so a grade-`g` tree becomes a
`FreeM₂` tree from state `1` to state `g`. -/
def toFreeM₂ {g : G} (x : GFreeM P g α) : IPFunctor.FreeM₂ P.toIPFunctor 1 g α :=
  toFreeM₂From 1 x (one_mul g)

/-! ## Equation and commutation lemmas -/

@[simp]
lemma toFreeM₂From_pure (k : G) {t : G} (x : α) (e : k * 1 = t) :
    toFreeM₂From k (GFreeM.pure (P := P) x) e =
      IPFunctor.FreeM₂.pureCast ((mul_one k).symm.trans e) x := rfl

@[simp]
lemma toFreeM₂From_roll (k : G) {g t : G} (a : P.A) (r : (b : P.B a) → GFreeM P g α)
    (e : k * (P.grade a * g) = t) :
    toFreeM₂From k (GFreeM.roll a r) e =
      IPFunctor.FreeM₂.roll (P := P.toIPFunctor) a
        (fun b => toFreeM₂From (k * P.grade a) (r b)
          ((mul_assoc k (P.grade a) g).trans e)) := rfl

/-- Grade casts on the input are absorbed into the Forded proof. -/
@[simp]
lemma toFreeM₂From_gcast (k : G) {g g' t : G} (eg : g = g') (x : GFreeM P g α)
    (e : k * g' = t) :
    toFreeM₂From k (gcast eg x) e =
      toFreeM₂From k x ((congrArg (k * ·) eg).trans e) := by
  subst eg; rfl

/-- Pre-state transports are absorbed into the accumulator. -/
@[simp]
lemma castPre_toFreeM₂From {k k' : G} (ek : k = k') {g t : G} (x : GFreeM P g α)
    (e : k * g = t) :
    IPFunctor.FreeM₂.castPre ek (toFreeM₂From k x e) =
      toFreeM₂From k' x ((congrArg (· * g) ek).symm.trans e) := by
  subst ek; rfl

@[simp]
lemma toFreeM₂_pure (x : α) :
    toFreeM₂ (GFreeM.pure (P := P) x) = IPFunctor.FreeM₂.pure x := rfl

@[simp]
lemma toFreeM₂_liftA (a : P.A) :
    toFreeM₂ (GFreeM.liftA a) =
      IPFunctor.FreeM₂.roll (P := P.toIPFunctor) a
        (fun b => IPFunctor.FreeM₂.pureCast (one_mul (P.grade a)) b) := by
  simp only [GFreeM.liftA, toFreeM₂, toFreeM₂From_gcast, toFreeM₂From_roll,
    toFreeM₂From_pure]
  rfl

/-! ## Compatibility with `bind`

The translation is a morphism of monad structure: graded bind maps to `FreeM₂.bind`, with
the continuation translated relative to the accumulated grade of the prefix. The statement
is Forded over the intermediate state `t₁`, which is what lets the `roll` case of the
induction apply its hypothesis without transport. -/

theorem toFreeM₂From_bind (k : G) {g h t t₁ : G} (x : GFreeM P g α)
    (f : α → GFreeM P h β) (e₁ : k * g = t₁) (e₂ : t₁ * h = t) (e : k * (g * h) = t) :
    toFreeM₂From k (x.bind f) e =
      (toFreeM₂From k x e₁).bind (fun a => toFreeM₂From t₁ (f a) e₂) := by
  induction x generalizing k t t₁ with
  | pure x =>
    simp only [GFreeM.bind_pure, toFreeM₂From_gcast, toFreeM₂From_pure,
      IPFunctor.FreeM₂.bind_pureCast, castPre_toFreeM₂From]
  | roll a r ih =>
    simp only [GFreeM.bind_roll, toFreeM₂From_gcast, toFreeM₂From_roll,
      IPFunctor.FreeM₂.bind_roll]
    exact congrArg _ (funext fun b => ih b _ _ _ _ _)

/-- Compatibility of the canonical translation with `bind`: the continuation is translated
relative to the accumulated grade `g` of the prefix. -/
theorem toFreeM₂_bind {g h : G} (x : GFreeM P g α) (f : α → GFreeM P h β) :
    toFreeM₂ (x.bind f) =
      (toFreeM₂ x).bind (fun a => toFreeM₂From g (f a) rfl) :=
  toFreeM₂From_bind 1 x f (one_mul g) rfl (one_mul (g * h))

end GFreeM

end GPFunctor
