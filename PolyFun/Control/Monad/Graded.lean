/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.PUnit
public import PolyFun.Control.Monad.Indexed

/-!
# Graded Monads

A **graded monad** over a monoid `G` is a family of types `M : G → Type → Type` equipped with:
- `gpure : α → M 1 α`
- `gbind : M g α → (α → M h β) → M (g * h) β`

The grade tracks a quantity that accumulates multiplicatively under sequencing (cost, effect
footprint, trace length, …). Unlike indexed monads ([`IndexedMonad`](Indexed.lean)), the monad
laws cannot be stated as exact equalities: the two sides live at grades that are equal only
*propositionally* (`1 * h = h`, `g * 1 = g`, `(g₁ * g₂) * g₃ = g₁ * (g₂ * g₃)`), which for a
generic monoid are not definitional. The laws therefore transport one side along the relevant
monoid identity.

## Grade transport

All transport is funneled through a single helper `gcast : g = h → M g α → M h α`. Because
`gcast` is a bare `Eq.rec`, transporting along any proof of a *reflexive* equation is
definitionally the identity (proof irrelevance), so `gcast`-heavy goals close by `rfl` once
both sides are normalized to a single cast between syntactically equal grades. The intended
simp normal form floats casts to the root of a term (`gbind_gcast_left`, `gbind_gcast_right`),
fuses adjacent casts (`gcast_gcast`), and discards reflexive casts (`gcast_rfl`).

## Relationship to indexed monads

Graded monads and indexed monads are *parallel* generalizations of monads — neither subsumes
the other in general (see the discussion in [`Indexed.lean`](Indexed.lean)). Over a *group*
`G`, a graded monad induces an indexed monad via `IxM i j α := M (i⁻¹ * j) α`; this is
`GradedMonad.toIndexedMonad` below. Every ordinary `Monad m` is trivially graded over the
one-element monoid (`instGradedMonadOfMonad`).

## Main definitions

- `gcast` — transport along an equality of grades, with its commutation lemma suite
- `GradedMonad` — type class for graded monads
- `LawfulGradedMonad` — the three monad laws, stated up to `gcast` transport
- `instGradedMonadOfMonad` — every `Monad` is a `GradedMonad PUnit`
- `GradedMonad.toIndexedMonad` — over a group, a graded monad induces an indexed monad

## References

See `REFERENCES.md` for the full citations.

- Smirnov, A. L. (2008). *Graded monads and rings of polynomials*. (Smi08)
- Katsumata, S. (2014). *Parametric effect monads and semantics of effect systems*. POPL. (Kat14)
- Milius, S., Pattinson, D., Schröder, L. (2015). *Generic trace semantics via coinduction
  and graded monads*. CALCO. (MPS15)
- Fujii, S., Katsumata, S., Melliès, P.-A. (2016). *Towards a formal theory of graded
  monads*. FoSSaCS. (FKM16)
- Orchard, D., Wadler, P., Eades, H. (2020). *Unifying graded and parameterised monads*.
  MSFP. (OWE20)
-/

@[expose] public section

universe u v

variable {G : Type*} {M : G → Type u → Type v}

/-! ## Grade transport -/

/-- Transport a graded computation along an equality of grades. A bare `Eq.rec`, so
transport along any reflexive equation is definitionally the identity; all the commutation
lemmas below are proved by `subst`. -/
def gcast {g h : G} {α : Type u} (e : g = h) (x : M g α) : M h α :=
  e ▸ x

@[simp]
lemma gcast_rfl {g : G} {α : Type u} (e : g = g) (x : M g α) :
    gcast e x = x := rfl

@[simp]
lemma gcast_gcast {g₁ g₂ g₃ : G} {α : Type u} (e₁ : g₁ = g₂) (e₂ : g₂ = g₃) (x : M g₁ α) :
    gcast e₂ (gcast e₁ x) = gcast (e₁.trans e₂) x := by
  subst e₂; subst e₁; rfl

@[simp]
lemma gcast_inj {g h : G} {α : Type u} (e : g = h) (x y : M g α) :
    gcast e x = gcast e y ↔ x = y := by
  subst e; exact Iff.rfl

lemma gcast_heq {g h : G} {α : Type u} (e : g = h) (x : M g α) :
    HEq (gcast e x) x := by
  subst e; rfl

lemma gcast_eq_iff_heq {g h : G} {α : Type u} (e : g = h) (x : M g α) (y : M h α) :
    gcast e x = y ↔ HEq x y := by
  subst e; simp

/-! ## Core definition -/

/-- A graded monad over a monoid `G`. The type family `M : G → Type u → Type v` supports
`gpure` at the unit grade and `gbind` that multiplies grades.

The grade tracks a quantity accumulated multiplicatively across sequencing: `M g α` is a
computation of total grade `g` producing a value of type `α`. -/
class GradedMonad (G : Type*) [Monoid G] (M : G → Type u → Type v) where
  /-- Embed a pure value at the trivial grade. -/
  gpure {α : Type u} : α → M 1 α
  /-- Sequentially compose two graded computations, multiplying their grades. -/
  gbind {α β : Type u} {g h : G} : M g α → (α → M h β) → M (g * h) β

export GradedMonad (gpure gbind)

section commutation

variable [Monoid G] [GradedMonad G M]

/-- Casts on the first argument of `gbind` float to the root. Holds in any graded monad,
lawful or not, by `subst`. -/
@[simp]
lemma gbind_gcast_left {g₁ g₂ h : G} {α β : Type u} (e : g₁ = g₂)
    (x : M g₁ α) (f : α → M h β) :
    gbind (gcast e x) f = gcast (congrArg (· * h) e) (gbind x f) := by
  subst e; rfl

/-- Casts inside the continuation of `gbind` float to the root. Holds in any graded monad,
lawful or not, by `subst`. -/
@[simp]
lemma gbind_gcast_right {g h₁ h₂ : G} {α β : Type u} (e : h₁ = h₂)
    (x : M g α) (f : α → M h₁ β) :
    gbind x (fun a => gcast e (f a)) = gcast (congrArg (g * ·) e) (gbind x f) := by
  subst e; rfl

end commutation

namespace GradedMonad

variable [Monoid G] [GradedMonad G M]

/-- Graded functor map, derived from `gpure` and `gbind`. The `mul_one` transport returns
the result to the original grade `g`. -/
def gmap {α β : Type u} {g : G} (f : α → β) (x : M g α) : M g β :=
  gcast (mul_one g) (gbind x (fun a => gpure (f a)))

/-- Sequence two graded computations, discarding the first result. -/
def gseq {α β : Type u} {g h : G} (x : M g α) (y : M h β) : M (g * h) β :=
  gbind x (fun _ => y)

end GradedMonad

/-! ## Laws -/

/-- Laws for a graded monad. Each law equates terms at propositionally equal grades, so the
right-hand side transports along the relevant monoid identity via `gcast`. The compound term
is kept on the left so that rewriting moves toward the right-associated normal form, after
which the `gcast` simp set fuses and discards the casts. -/
class LawfulGradedMonad (G : Type*) [Monoid G] (M : G → Type u → Type v)
    [GradedMonad G M] : Prop where
  /-- Left identity, up to transport along `1 * h = h`. -/
  gpure_gbind {α β : Type u} {h : G} (a : α) (f : α → M h β) :
    gbind (gpure a) f = gcast (one_mul h).symm (f a)
  /-- Right identity, up to transport along `g * 1 = g`. -/
  gbind_gpure {α : Type u} {g : G} (x : M g α) :
    gbind x gpure = gcast (mul_one g).symm x
  /-- Associativity, up to transport along `(g₁ * g₂) * g₃ = g₁ * (g₂ * g₃)`. -/
  gbind_assoc {α β γ : Type u} {g₁ g₂ g₃ : G} (x : M g₁ α)
      (f : α → M g₂ β) (k : β → M g₃ γ) :
    gbind (gbind x f) k =
      gcast (mul_assoc g₁ g₂ g₃).symm (gbind x (fun a => gbind (f a) k))

export LawfulGradedMonad (gpure_gbind gbind_gpure gbind_assoc)

attribute [simp] gpure_gbind gbind_gpure gbind_assoc

/-! ## Trivial grading: every monad is a graded monad over `PUnit` -/

/-- Every `Monad` is a `GradedMonad` over the one-element monoid,
with `gpure = pure` and `gbind = bind`. -/
instance instGradedMonadOfMonad (m : Type u → Type v) [Monad m] :
    GradedMonad PUnit (fun _ => m) where
  gpure := pure
  gbind x f := x >>= f

/-- The trivial grading of a lawful monad is a lawful graded monad. All grades in `PUnit`
are definitionally equal (structure eta), so every `gcast` is definitionally the identity
and the laws reduce to the ordinary monad laws. -/
instance instLawfulGradedMonadOfLawfulMonad (m : Type u → Type v)
    [Monad m] [LawfulMonad m] :
    LawfulGradedMonad PUnit (fun _ => m) where
  gpure_gbind a f := by
    change (pure a >>= f) = f a
    exact pure_bind a f
  gbind_gpure x := by
    change (x >>= pure) = x
    exact bind_pure x
  gbind_assoc x f k := by
    change ((x >>= f) >>= k) = x >>= fun a => f a >>= k
    exact bind_assoc x f k

/-! ## Graded to indexed, over a group -/

/-- Over a *group* `G`, a graded monad induces an Atkey indexed monad with
`IxM i j α := M (i⁻¹ * j) α`: a computation from pre-state `i` to post-state `j` is a
computation of grade `i⁻¹ * j`. The group inverse is essential for `ipure`, which needs a
computation at grade `i⁻¹ * i = 1`.

A `def` rather than an `instance`: the head `fun i j α => M (i⁻¹ * j) α` is not a usable
typeclass pattern. -/
@[reducible]
def GradedMonad.toIndexedMonad {G : Type*} [Group G] (M : G → Type u → Type v)
    [GradedMonad G M] : IndexedMonad G (fun i j α => M (i⁻¹ * j) α) where
  ipure {_ i} a := gcast (inv_mul_cancel i).symm (gpure a)
  ibind {_ _ i j k} x f :=
    gcast (show i⁻¹ * j * (j⁻¹ * k) = i⁻¹ * k by rw [mul_assoc, mul_inv_cancel_left])
      (gbind x f)

/-- The indexed monad induced by a lawful graded monad over a group is lawful. The proofs
are pure `gcast` algebra: float the casts to the root, apply the graded law, fuse, and
discharge the resulting reflexive cast by proof irrelevance. -/
theorem GradedMonad.toIndexedMonad_lawful {G : Type*} [Group G] (M : G → Type u → Type v)
    [GradedMonad G M] [LawfulGradedMonad G M] :
    @LawfulIndexedMonad G (fun i j α => M (i⁻¹ * j) α) (GradedMonad.toIndexedMonad M) := by
  letI := GradedMonad.toIndexedMonad M
  refine { ipure_ibind := ?_, ibind_ipure := ?_, ibind_assoc := ?_ }
  · intro α β i j a f
    change gcast _ (gbind (gcast _ (gpure a)) f) = f a
    simp
  · intro α i j x
    change gcast _ (gbind x (fun a => gcast _ (gpure a))) = x
    simp
  · intro α β γ i j k l x f g
    change gcast _ (gbind (gcast _ (gbind x f)) g) =
      gcast _ (gbind x (fun a => gcast _ (gbind (f a) g)))
    simp
