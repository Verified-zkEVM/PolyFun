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

Consequently `toFreeM₂` is not an equivalence in general, and the path-product object
supports no interpretation into a general graded monad, which is why `GFreeM` is defined
directly rather than as this encoding. The mismatch is governed exactly by cancellativity:
over a left-cancellative monoid the translation is injective (`toFreeM₂From_inj`,
`toFreeM₂_injective`), and over a group it is an equivalence (`ofFreeM₂`, `equivFreeM₂`) —
graded trees and accumulated-grade indexed trees are the same data on the group fragment.

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

universe uG uA uB v w

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

/-! ## Compatibility with `mapM`

The two forgetful routes from a graded tree to a plain-monad interpretation — translate
into the indexed encoding and interpret, or interpret directly — agree. -/

theorem toFreeM₂From_mapM {m : Type uB → Type w} [Pure m] [Bind m] {α : Type uB}
    (h : (a : P.A) → m (P.B a)) (k : G) {g t : G} (x : GFreeM P g α) (e : k * g = t) :
    (toFreeM₂From k x e).mapM (fun _ a => h a) = x.mapM h := by
  induction x generalizing k t with
  | pure x => rfl
  | roll a r ih => exact congrArg (Bind.bind (h a)) (funext fun b => ih b _ _)

/-! ## Injectivity over a left-cancellative monoid

How far the translation is from an equivalence is governed by cancellativity. The
injectivity statement is heterogeneous in the grades and Forded over a shared target
accumulator: the grade equality comes from cancelling the Forded proofs (never from the
induction, which also covers childless shapes), and the trees then agree by structural
induction. -/

theorem toFreeM₂From_inj [IsLeftCancelMul G] (k : G) {g₁ g₂ t : G}
    (x₁ : GFreeM P g₁ α) (x₂ : GFreeM P g₂ α) (e₁ : k * g₁ = t) (e₂ : k * g₂ = t)
    (h : toFreeM₂From k x₁ e₁ = toFreeM₂From k x₂ e₂) :
    ∃ hg : g₂ = g₁, x₁ = gcast hg x₂ := by
  induction x₁ using GFreeM.inductionOn generalizing k t g₂ x₂ with
  | pure x =>
    cases x₂ with
    | pure y =>
      obtain rfl := (IPFunctor.FreeM₂.pureCast_inj ((mul_one k).symm.trans e₁)
        ((mul_one k).symm.trans e₂) x y).mp h
      exact ⟨rfl, rfl⟩
    | roll a' r' => exact absurd h (IPFunctor.FreeM₂.pureCast_ne_roll _ _ _ _)
  | roll g a r ih =>
    cases x₂ with
    | pure y => exact absurd h (IPFunctor.FreeM₂.roll_ne_pureCast _ _ _ _)
    | @roll _ g' a' r' =>
      obtain ⟨ha, hr⟩ := (IPFunctor.FreeM₂.roll_inj _ _ _ _).mp h
      subst ha
      obtain rfl : g = g' :=
        mul_left_cancel (((mul_assoc k (P.grade a) g).trans e₁).trans
          (((mul_assoc k (P.grade a) g').trans e₂).symm))
      refine ⟨rfl, ?_⟩
      refine congrArg (GFreeM.roll a) (funext fun b => ?_)
      obtain ⟨hg, hb⟩ := ih b (k * P.grade a) (r' b)
        ((mul_assoc k (P.grade a) g).trans e₁) ((mul_assoc k (P.grade a) g).trans e₂)
        (congrFun hr b)
      rwa [gcast_rfl] at hb

/-- Over a left-cancellative monoid, the canonical translation is injective. -/
theorem toFreeM₂_injective [IsLeftCancelMul G] {g : G} :
    Function.Injective (toFreeM₂ (P := P) (g := g) (α := α)) := by
  intro x y h
  obtain ⟨hg, hx⟩ := toFreeM₂From_inj 1 x y (one_mul g) (one_mul g) h
  rwa [gcast_rfl] at hx

end GFreeM

namespace GFreeM

/-! ## The group case: an equivalence

Over a group the accumulated grade can be *divided off*, so the path-product encoding
collapses back onto the uniform-sibling-grade trees: `ofFreeM₂` reconstructs a graded tree
of grade `s⁻¹ * t` from an indexed tree running from accumulator `s` to `t`, and the two
translations are mutually inverse (`toFreeM₂From_ofFreeM₂`, `ofFreeM₂_toFreeM₂From`,
bundled as `equivFreeM₂`). -/

section group

variable {G : Type uG} [Group G] {P : GPFunctor.{uG, uA, uB} G} {α : Type v}

/-- Translate an accumulated-grade indexed tree back into the free graded monad, over a
group: a tree from accumulator `s` to `t` has uniform grade `s⁻¹ * t`. -/
def ofFreeM₂ {s t : G} (x : IPFunctor.FreeM₂ P.toIPFunctor s t α) :
    GFreeM P (s⁻¹ * t) α :=
  IPFunctor.IFreeM.construct (C := fun s _ => GFreeM P (s⁻¹ * t) α)
    (fun s p => gcast (show (1 : G) = s⁻¹ * t by rw [p.1, inv_mul_cancel]) (.pure p.2))
    (fun s a _ ih =>
      gcast (show P.grade a * ((s * P.grade a)⁻¹ * t) = s⁻¹ * t by
        rw [mul_inv_rev, mul_assoc, mul_inv_cancel_left]) (.roll a ih)) x

@[simp]
lemma ofFreeM₂_pureCast {s t : G} (w : s = t) (x : α) :
    ofFreeM₂ (P := P) (IPFunctor.FreeM₂.pureCast w x) =
      gcast (show (1 : G) = s⁻¹ * t by rw [w, inv_mul_cancel]) (GFreeM.pure x) := rfl

@[simp]
lemma ofFreeM₂_pure {s : G} (x : α) :
    ofFreeM₂ (P := P) (IPFunctor.FreeM₂.pure (s := s) x) =
      gcast (inv_mul_cancel s).symm (GFreeM.pure x) := rfl

@[simp]
lemma ofFreeM₂_roll {s t : G} (a : P.A)
    (r : (b : P.B a) → IPFunctor.FreeM₂ P.toIPFunctor (s * P.grade a) t α) :
    ofFreeM₂ (IPFunctor.FreeM₂.roll (P := P.toIPFunctor) (s := s) a r) =
      gcast (show P.grade a * ((s * P.grade a)⁻¹ * t) = s⁻¹ * t by
        rw [mul_inv_rev, mul_assoc, mul_inv_cancel_left])
        (GFreeM.roll a fun b => ofFreeM₂ (r b)) := rfl

/-- Translating back and forth from the indexed encoding is the identity. -/
@[simp]
theorem toFreeM₂From_ofFreeM₂ {s t : G} (x : IPFunctor.FreeM₂ P.toIPFunctor s t α)
    (e : s * (s⁻¹ * t) = t) :
    toFreeM₂From s (ofFreeM₂ x) e = x := by
  induction x using IPFunctor.FreeM₂.inductionOn with
  | pure s x =>
    simp only [ofFreeM₂_pure, toFreeM₂From_gcast, toFreeM₂From_pure,
      IPFunctor.FreeM₂.pureCast_rfl]
  | roll s t a r ih =>
    simp only [ofFreeM₂_roll, toFreeM₂From_gcast, toFreeM₂From_roll]
    exact congrArg (IPFunctor.FreeM₂.roll a) (funext fun b => ih b _)

/-- Translating forth and back from the indexed encoding is the identity, up to transport
along the group identity recovering the grade from the accumulators. -/
@[simp]
theorem ofFreeM₂_toFreeM₂From (k : G) {g t : G} (x : GFreeM P g α) (e : k * g = t) :
    ofFreeM₂ (toFreeM₂From k x e) =
      gcast (show g = k⁻¹ * t by rw [← e, inv_mul_cancel_left]) x := by
  induction x generalizing k t with
  | pure x => exact ofFreeM₂_pureCast _ x
  | roll a r ih =>
    simp only [toFreeM₂From_roll, ofFreeM₂_roll, ih, roll_gcast, gcast_gcast]

/-- Over a group, a grade-`g` graded tree is the same data as an accumulated-grade indexed
tree from `1` to `g`: the uniform-sibling-grade and path-product readings coincide on the
group fragment. -/
def equivFreeM₂ (g : G) :
    GFreeM P g α ≃ IPFunctor.FreeM₂ P.toIPFunctor 1 g α where
  toFun := toFreeM₂
  invFun y := gcast (show (1 : G)⁻¹ * g = g by rw [inv_one, one_mul]) (ofFreeM₂ y)
  left_inv x := by
    simp only [toFreeM₂, ofFreeM₂_toFreeM₂From, gcast_gcast, gcast_rfl]
  right_inv y := by
    simp only [toFreeM₂, toFreeM₂From_gcast, toFreeM₂From_ofFreeM₂]

end group

end GFreeM

end GPFunctor
