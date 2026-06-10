/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.GPFunctor.Basic
public import PolyFun.Control.Monad.Graded
public import PolyFun.PFunctor.Free.Basic

/-!
# Free Graded Monad on a `GPFunctor`

This file defines `GPFunctor.GFreeM P g α`, the free graded monad over a graded polynomial
functor `P : GPFunctor G` with `[Monoid G]`. A `GFreeM P g α` tree is a tree over the
underlying container of `P` of total grade `g`: a leaf has the trivial grade, and a node with
shape `a` whose branches all have remaining grade `g'` has grade `P.grade a * g'`.

## Freeness and uniform sibling grades

The `roll` constructor requires every branch to carry the *same* remaining grade. This is not
a restriction bolted on for convenience — it is what freeness means here. A graded algebra
for `P` has operations `(P.B a → A g) → A (P.grade a * g)` with a single grade `g` across the
branches (mirroring `gbind`, whose continuation `α → M h β` has a single grade `h`), and
`GFreeM` is the initial such algebra. Concretely, the interpretation `GFreeM.mapGM` into an
arbitrary graded monad exists *because* siblings share a grade — and it is cast-free.

The alternative "path-product" reading ("trees in which every root-to-leaf product of grades
equals `g`") is realized by the two-index indexed free monad over `P.toIPFunctor`; over a
non-cancellative monoid it is strictly larger than `GFreeM` and supports no interpretation
into a general graded monad. The translation from `GFreeM` into that encoding lives in
[`PolyFun/GPFunctor/Free/Indexed.lean`](Indexed.lean).

## Grade transport discipline

`GFreeM.bind` must return at grade `g * h` while its pieces naturally produce `1 * h` (leaf
case) and `P.grade a * (g' * h)` (node case), so the definition transports along `one_mul` /
`mul_assoc` using [`gcast`](../../Control/Monad/Graded.lean). All casts float to the root of
a term: the simp set rewrites with the equation lemmas (`bind_pure`, `bind_roll`), commutes
casts outward (`roll_gcast`, `bind_gcast_left`, `bind_gcast_right`, `map_gcast`, …), fuses
adjacent casts (`gcast_gcast`), and discards reflexive casts (`gcast_rfl`). Goals whose two
sides become a single cast between syntactically equal grades close by definitional proof
irrelevance. Interpretations out of `GFreeM` (`mapGM`, `mapM`, `erase`) are cast-free.
-/

@[expose] public section

universe uG uA uB v w

namespace GPFunctor

variable {G : Type uG}

/-- The free graded monad over a graded polynomial functor. `GFreeM P g α` is a tree over
the container of `P` with total grade `g`: leaves are at the trivial grade, and a node
contributes its shape's grade on top of the (uniform) remaining grade of its branches. -/
inductive GFreeM [Monoid G] (P : GPFunctor.{uG, uA, uB} G) :
    G → Type v → Type (max uG uA uB (v + 1))
  /-- A pure value, at the trivial grade. -/
  | pure {α : Type v} (x : α) : GFreeM P 1 α
  /-- Roll a shape into a continuation whose branches all carry the same remaining grade
  `g`; the node's total grade is `P.grade a * g`. -/
  | roll {α : Type v} {g : G} (a : P.A) (r : (b : P.B a) → GFreeM P g α) :
      GFreeM P (P.grade a * g) α

namespace GFreeM

variable [Monoid G] {P : GPFunctor.{uG, uA, uB} G} {α β γ : Type v}

/-! ## Cast toolkit

`GFreeM`-specific commutation lemmas for [`gcast`](../../Control/Monad/Graded.lean),
complementing the generic `gcast_gcast` / `gcast_rfl` suite. Each is proved by `subst`. -/

/-- Casts inside the branches of a `roll` float to the root. -/
@[simp]
lemma roll_gcast {g g' : G} (e : g = g') (a : P.A) (r : (b : P.B a) → GFreeM P g α) :
    GFreeM.roll a (fun b => gcast e (r b)) =
      gcast (congrArg (P.grade a * ·) e) (GFreeM.roll a r) := by
  subst e; rfl

/-! ## Bind -/

/-- Bind on the free graded monad: grades multiply. The leaf case returns at `1 * h` and the
node case at `P.grade a * (g' * h)`, so both transport to the stated grade via `gcast`. -/
protected def bind {h : G} : {g : G} → GFreeM P g α → (α → GFreeM P h β) →
    GFreeM P (g * h) β
  | _, .pure x,   f => gcast (one_mul h).symm (f x)
  | _, .roll a r, f =>
      gcast (mul_assoc (P.grade a) _ h).symm (.roll a (fun b => (r b).bind f))

@[simp]
lemma bind_pure {h : G} (x : α) (f : α → GFreeM P h β) :
    (GFreeM.pure (P := P) x).bind f = gcast (one_mul h).symm (f x) := rfl

@[simp]
lemma bind_roll {g h : G} (a : P.A) (r : (b : P.B a) → GFreeM P g α)
    (f : α → GFreeM P h β) :
    (GFreeM.roll a r).bind f =
      gcast (mul_assoc (P.grade a) g h).symm
        (GFreeM.roll a (fun b => (r b).bind f)) := rfl

/-- Casts on the tree argument of `bind` float to the root. -/
@[simp]
lemma bind_gcast_left {g g' h : G} (e : g = g') (x : GFreeM P g α)
    (f : α → GFreeM P h β) :
    (gcast e x).bind f = gcast (congrArg (· * h) e) (x.bind f) := by
  subst e; rfl

/-- Casts inside the continuation of `bind` float to the root. -/
@[simp]
lemma bind_gcast_right {g h h' : G} (e : h = h') (x : GFreeM P g α)
    (f : α → GFreeM P h β) :
    x.bind (fun a => gcast e (f a)) = gcast (congrArg (g * ·) e) (x.bind f) := by
  subst e; rfl

/-! ## Lifting -/

/-- Lift a shape into the free graded monad at its own grade, returning the response. -/
def liftA (a : P.A) : GFreeM P (P.grade a) (P.B a) :=
  gcast (mul_one (P.grade a)) (.roll a (fun b => .pure b))

/-- Lift a grade-`g` homogeneous position (a shape of grade `g` with a continuation of
values) into the free graded monad. -/
def lift {g : G} (x : P.Obj g α) : GFreeM P g α :=
  gcast ((mul_one (P.grade x.1.1)).trans x.1.2) (.roll x.1.1 (fun b => .pure (x.2 b)))

/-- Binding a lifted shape is exactly `roll`: the casts introduced by `liftA` and `bind`
compose to a reflexive transport and vanish. The result type `β` lives in `Type uB` because
the intermediate payload of `liftA a` is the response type `P.B a`. -/
@[simp]
lemma bind_liftA {h : G} {β : Type uB} (a : P.A) (f : P.B a → GFreeM P h β) :
    (liftA a).bind f = GFreeM.roll a f := by
  simp only [liftA, bind_gcast_left, bind_roll, bind_pure, roll_gcast, gcast_gcast,
    gcast_rfl]

/-! ## Injectivity -/

lemma pure_inj (x y : α) :
    GFreeM.pure (P := P) x = GFreeM.pure y ↔ x = y := by
  refine ⟨?_, fun h => by rw [h]⟩
  intro h; cases h; rfl

@[simp]
lemma roll_inj {g : G} (a : P.A) (r r' : (b : P.B a) → GFreeM P g α) :
    GFreeM.roll a r = GFreeM.roll a r' ↔ r = r' := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  injection h

/-! ## Functor map -/

/-- Functor map on the free graded monad. Mapping rewrites leaves only, so it is cast-free
and preserves the grade. -/
protected def map (f : α → β) : {g : G} → GFreeM P g α → GFreeM P g β
  | _, .pure x   => .pure (f x)
  | _, .roll a r => .roll a (fun b => (r b).map f)

@[simp]
lemma map_pure (f : α → β) (x : α) :
    (GFreeM.pure (P := P) x).map f = GFreeM.pure (f x) := rfl

@[simp]
lemma map_roll {g : G} (f : α → β) (a : P.A) (r : (b : P.B a) → GFreeM P g α) :
    (GFreeM.roll a r).map f = GFreeM.roll a (fun b => (r b).map f) := rfl

/-- Casts commute with `map`. -/
@[simp]
lemma map_gcast {g g' : G} (e : g = g') (f : α → β) (x : GFreeM P g α) :
    (gcast e x).map f = gcast e (x.map f) := by
  subst e; rfl

/-! ## Induction principle -/

/-- Induction principle for `GFreeM` with the grade in the motive. The native `induction`
tactic also works directly; this wrapper names the cases after the high-level constructors. -/
@[elab_as_elim]
protected def inductionOn {C : ∀ g, GFreeM P g α → Prop}
    (pure : ∀ x : α, C 1 (GFreeM.pure x))
    (roll : ∀ (g : G) (a : P.A) (r : (b : P.B a) → GFreeM P g α),
      (∀ b, C g (r b)) → C (P.grade a * g) (GFreeM.roll a r)) :
    ∀ {g} (x : GFreeM P g α), C g x
  | _, .pure x   => pure x
  | _, .roll a r => roll _ a r (fun b => GFreeM.inductionOn pure roll (r b))

/-! ## `Functor` / `LawfulFunctor` instances -/

instance (g : G) : Functor (GFreeM P g) where
  map f x := GFreeM.map f x
  mapConst b x := GFreeM.map (fun _ => b) x

instance (g : G) : LawfulFunctor (GFreeM P g) where
  map_const := rfl
  id_map x := by
    induction x with
    | pure x => rfl
    | roll a r ih => exact congrArg _ (funext ih)
  comp_map f h x := by
    induction x with
    | pure x => rfl
    | roll a r ih => exact congrArg _ (funext fun b => ih b f)

/-! ## Monad laws at the `bind` level

The laws of `LawfulGradedMonad`, proved by structural induction. Each proof normalizes both
sides to a single cast over the same tree; the residual goal equates two casts between
syntactically equal grades, which holds by definitional proof irrelevance. -/

/-- Right identity: binding with `pure` is the (transported) identity. -/
@[simp]
protected lemma bind_pure_right {g : G} (x : GFreeM P g α) :
    x.bind GFreeM.pure = gcast (mul_one g).symm x := by
  induction x with
  | pure x => rfl
  | roll a r ih => simp only [bind_roll, ih, roll_gcast, gcast_gcast]

/-- Binding with a `pure`-composed function is a (transported) `map`. -/
@[simp]
protected lemma bind_pure_comp {g : G} (f : α → β) (x : GFreeM P g α) :
    x.bind (fun a => GFreeM.pure (f a)) = gcast (mul_one g).symm (x.map f) := by
  induction x with
  | pure x => rfl
  | roll a r ih => simp only [bind_roll, ih, roll_gcast, gcast_gcast, map_roll]

/-- Associativity of `bind`, up to transport along `mul_assoc`. -/
protected lemma bind_assoc {g₁ g₂ g₃ : G} (x : GFreeM P g₁ α)
    (f : α → GFreeM P g₂ β) (k : β → GFreeM P g₃ γ) :
    (x.bind f).bind k =
      gcast (mul_assoc g₁ g₂ g₃).symm (x.bind (fun a => (f a).bind k)) := by
  induction x with
  | pure x => simp only [bind_pure, bind_gcast_left, gcast_gcast]
  | roll a r ih =>
    simp only [bind_roll, bind_gcast_left, ih, roll_gcast, gcast_gcast]

/-! ## `Pure`, `GradedMonad`, and `LawfulGradedMonad` instances -/

/-- Plain `Pure` instance for the trivial-grade slice. -/
instance : Pure (GFreeM P (1 : G)) where
  pure x := GFreeM.pure x

instance (P : GPFunctor.{uG, uA, uB} G) : GradedMonad G (GFreeM.{uG, uA, uB, v} P) where
  gpure := GFreeM.pure
  gbind := GFreeM.bind

@[simp]
lemma gpure_def (x : α) : (gpure x : GFreeM P 1 α) = GFreeM.pure x := rfl

@[simp]
lemma gbind_def {g h : G} (x : GFreeM P g α) (f : α → GFreeM P h β) :
    gbind x f = x.bind f := rfl

instance (P : GPFunctor.{uG, uA, uB} G) :
    LawfulGradedMonad G (GFreeM.{uG, uA, uB, v} P) where
  gpure_gbind _ _ := rfl
  gbind_gpure := GFreeM.bind_pure_right
  gbind_assoc := GFreeM.bind_assoc

/-- The derived graded functor map agrees with the structural `GFreeM.map`. -/
lemma gmap_eq_map {g : G} (f : α → β) (x : GFreeM P g α) :
    GradedMonad.gmap f x = x.map f := by
  simp only [GradedMonad.gmap, gbind_def, gpure_def, GFreeM.bind_pure_comp, gcast_gcast,
    gcast_rfl]

/-! ## `mapGM`: interpreting into a graded monad

`GFreeM` is the *free* graded monad: a shape handler `h` assigning each shape a
grade-matching action in an arbitrary graded monad `m` extends to an interpretation of whole
trees. The grade indices line up exactly (`pure` at `1`, `roll` at `P.grade a * g`), so the
interpretation is cast-free. The responses `P.B a` live in `Type uB`, so the target is
constrained to `m : G → Type uB → Type w`. -/

section mapGM

variable {m : G → Type uB → Type w} [GradedMonad G m] {α : Type uB}

/-- Interpret a `GFreeM` tree into an arbitrary graded monad, sending each shape `a` to a
grade-`P.grade a` action producing its response. -/
protected def mapGM (h : (a : P.A) → m (P.grade a) (P.B a)) :
    {g : G} → GFreeM P g α → m g α
  | _, .pure x   => gpure x
  | _, .roll a r => gbind (h a) (fun b => (r b).mapGM h)

variable (h : (a : P.A) → m (P.grade a) (P.B a))

@[simp]
lemma mapGM_pure (x : α) :
    (GFreeM.pure (P := P) x).mapGM h = gpure x := rfl

@[simp]
lemma mapGM_roll {g : G} (a : P.A) (r : (b : P.B a) → GFreeM P g α) :
    (GFreeM.roll a r).mapGM h = gbind (h a) (fun b => (r b).mapGM h) := rfl

/-- Casts commute with `mapGM`. -/
@[simp]
lemma mapGM_gcast {g g' : G} (e : g = g') (x : GFreeM P g α) :
    (gcast e x).mapGM h = gcast e (x.mapGM h) := by
  subst e; rfl

end mapGM

/-! ## `mapM`: interpreting into a plain monad

Forget the grades on the target side and interpret into an ordinary monad. As with `mapGM`,
the responses live in `Type uB`, constraining the target to `m : Type uB → Type w`. -/

section mapM

variable {m : Type uB → Type w} [Pure m] [Bind m] {α : Type uB}

/-- Interpret a `GFreeM` tree into an ordinary monad, dropping the grades. -/
protected def mapM (h : (a : P.A) → m (P.B a)) :
    {g : G} → GFreeM P g α → m α
  | _, .pure x   => Pure.pure x
  | _, .roll a r => h a >>= fun b => (r b).mapM h

variable (h : (a : P.A) → m (P.B a))

@[simp]
lemma mapM_pure (x : α) :
    (GFreeM.pure (P := P) x).mapM h = Pure.pure x := rfl

@[simp]
lemma mapM_roll {g : G} (a : P.A) (r : (b : P.B a) → GFreeM P g α) :
    (GFreeM.roll a r).mapM h = h a >>= fun b => (r b).mapM h := rfl

/-- Casts commute with `mapM`. -/
@[simp]
lemma mapM_gcast {g g' : G} (e : g = g') (x : GFreeM P g α) :
    (gcast e x).mapM h = x.mapM h := by
  subst e; rfl

end mapM

/-! ## Forgetting grades

Erase the grades entirely, yielding a tree of the plain free monad on the underlying
container. Unlike the indexed erasures, no `[Unique]` hypothesis is needed: the shape and
response data never depended on the grade. -/

/-- Forget the grades, yielding a `PFunctor.FreeM` tree over the underlying container. -/
def erase : {g : G} → GFreeM P g α → P.toPFunctor.FreeM α
  | _, .pure x   => .pure x
  | _, .roll a r => .roll a (fun b => (r b).erase)

@[simp]
lemma erase_pure (x : α) :
    (GFreeM.pure (P := P) x).erase = PFunctor.FreeM.pure x := rfl

@[simp]
lemma erase_roll {g : G} (a : P.A) (r : (b : P.B a) → GFreeM P g α) :
    (GFreeM.roll a r).erase = PFunctor.FreeM.roll a (fun b => (r b).erase) := rfl

/-- Casts vanish under grade erasure. -/
@[simp]
lemma erase_gcast {g g' : G} (e : g = g') (x : GFreeM P g α) :
    (gcast e x).erase = x.erase := by
  subst e; rfl

/-- Grade erasure is a monad morphism onto the plain free monad. -/
lemma erase_bind {g h : G} (x : GFreeM P g α) (f : α → GFreeM P h β) :
    (x.bind f).erase = x.erase.bind (fun a => (f a).erase) := by
  induction x with
  | pure x => simp
  | roll a r ih => simp [ih]

end GFreeM

end GPFunctor
