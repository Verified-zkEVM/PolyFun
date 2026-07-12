/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Hom-set adjunctions for trivial-interface polynomial functors

This file records the "trivial interface" hom-set equivalences of Spivak–Niu
*Polynomial Functors: A Mathematical Theory of Interaction* (Cambridge University
Press, 2025), §5.1. Each computes the set of lenses out of, or into, one of the
distinguished polynomial functors `0`, `1`, `X = y`, a constant `C A`, or a
linear `linear A` by a concrete data type. These are the hom-isomorphisms
witnessing the adjoint quadruple `linear ⊣ (−)(1) ⊣ C ⊣ (−)(0)` together with
the sections/principal-monomial refinements.

* `homFromZero` — `0` is initial in `Poly`: the lens `0 ⇆ p` is unique,
  `Lens 0 p ≃ PUnit`. (A special case of `Poly(I, q) ≅ Set(I, q(0))` from
  Spivak–Niu Thm 5.4 at `I = 0`.)
* `homToOne` — `1` is terminal in `Poly`: the lens `p ⇆ 1` is unique,
  `Lens p 1 ≃ PUnit`. (The `I = PUnit` case of `Poly(q, I) ≅ Set(q(1), I)`
  from Thm 5.4.)
* `homFromX` — a lens `y ⇆ p` is a position of `p`, `Lens X p ≃ p.A`. This is
  the counit of `linear ⊣ (−)(1)`, i.e. `Poly(y, q) ≅ q(1)` (Thm 5.4).
* `homToConst` — a lens `p ⇆ C A` is a map of positions `p.A → A`,
  `Lens p (C A) ≃ (p.A → A)`, i.e. `Poly(q, I) ≅ Set(q(1), I)` (Thm 5.4;
  the `C ⊣ (−)(0)` / `(−)(1) ⊣ C` unit).
* `homToLinear` — a lens `p ⇆ A·y` is a map of positions together with a
  section, `Lens p (linear A) ≃ (p.A → A) × ((a : p.A) → p.B a)`. This is the
  principal-monomial hom-iso `Poly(p, Iy^A) ≅ Set(p(1), I) × Set(A, Γ(p))` of
  Spivak–Niu Cor 5.15 specialised to `A_exp = PUnit`, where the second factor
  `(a : p.A) → p.B a` is the set of sections `Γ(p) = Poly(p, y)` (Prop 5.12).

## Design notes

The equivalences are stated as bare `Equiv`s between `Lens` types and concrete
types, matching the observation of the reading notes (§5.1) that none of these
hom-isos needs category-theory packaging to be useful.

These hom-isomorphisms are reference API: book-completeness formalizations of
the §5.1 trivial-interface adjunctions, staged for downstream (VCV-io)
consumers and exercised in `PolyFunTest/PFunctor/Adjunctions.lean`.

Both directions of `homFromX` and `homToLinear` hold definitionally
(`PUnit`/`Prod` eta), so their inverse laws are `rfl`. The three equivalences
touching an empty direction type (`homFromZero`, `homToOne`, `homToConst`)
need a `funext` into the empty type for one inverse law.

The final section implements the tensor-gluing universal property of
Spivak–Niu Proposition 5.49. A lens out of `p ⊗ q` is reconstructed from its
two views in which one factor is replaced by its position-only linear shadow;
compatibility is exactly equality of the two position maps.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂

namespace PFunctor

variable {p : PFunctor.{uA, uB}}

/-- **`0` is initial** (Spivak–Niu Thm 5.4, special case). The only lens out of
the zero polynomial functor is `Lens.initial`, so the hom-set is a singleton. -/
def homFromZero : Lens (0 : PFunctor.{uA₁, uB₁}) p ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Lens.initial
  left_inv _ := Lens.ext _ _ (fun a => a.elim) (fun a => a.elim)
  right_inv _ := rfl

/-- **`1` is terminal** (Spivak–Niu Thm 5.4, `I = PUnit` case of
`Poly(q, I) ≅ Set(q(1), I)`). The only lens into the unit polynomial functor is
`Lens.terminal`, so the hom-set is a singleton. -/
def homToOne : Lens p (1 : PFunctor.{uA₁, uB₁}) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Lens.terminal
  left_inv l := by
    refine Lens.ext _ _ (fun a => rfl) (fun a => ?_)
    funext d
    exact d.elim
  right_inv _ := rfl

/-- **Representability of `y`** (Spivak–Niu Thm 5.4, `Poly(y, q) ≅ q(1)`). A
lens `X ⇆ p` picks a single position of `p` via `toFunA PUnit.unit`, and its
`toFunB` is forced (every direction of `X` is `PUnit.unit`). -/
def homFromX : Lens X.{uA₁, uB₁} p ≃ p.A where
  toFun l := l.toFunA PUnit.unit
  invFun a := (fun _ => a) ⇆ (fun _ _ => PUnit.unit)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Constants are right adjoint on positions** (Spivak–Niu Thm 5.4,
`Poly(q, I) ≅ Set(q(1), I)`). A lens `p ⇆ C A` is exactly a function on
positions `p.A → A`; its backward map is forced since `C A` has no directions. -/
def homToConst {A : Type uA₂} : Lens p (C A : PFunctor.{uA₂, uB₁}) ≃ (p.A → A) where
  toFun l := l.toFunA
  invFun f := f ⇆ (fun _ => PEmpty.elim)
  left_inv l := by
    refine Lens.ext _ _ (fun a => rfl) (fun a => ?_)
    funext d
    exact d.elim
  right_inv _ := rfl

/-- **Principal monomial hom-iso** (Spivak–Niu Cor 5.15, at exponent `PUnit`).
A lens `p ⇆ A·y` is a function on positions `p.A → A` together with a section
`(a : p.A) → p.B a` of `p` (an element `Γ(p) = Poly(p, y)`), because the single
direction of `linear A` at each position is pulled back to a chosen direction
of `p`. -/
def homToLinear {A : Type uA₂} :
    Lens p (linear A : PFunctor.{uA₂, uB₁}) ≃ ((p.A → A) × ((a : p.A) → p.B a)) where
  toFun l := (l.toFunA, fun a => l.toFunB a PUnit.unit)
  invFun fg := fg.1 ⇆ (fun a _ => fg.2 a)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Tensor gluing (Spivak–Niu Proposition 5.49) -/

namespace Lens

/-- The canonical lens `p(1)y ⇆ p` from the linear, position-only shadow of a
polynomial into the polynomial itself. It preserves positions and forgets the
chosen direction. -/
def positionCounit (p : PFunctor.{uA, uB}) : Lens (linear p.A) p :=
  id ⇆ (fun _ _ => PUnit.unit)

@[simp] theorem positionCounit_toFunA (p : PFunctor.{uA, uB}) (a : p.A) :
    (positionCounit p).toFunA a = a := rfl

@[simp] theorem positionCounit_toFunB (p : PFunctor.{uA, uB}) (a : p.A)
    (d : p.B a) :
    (positionCounit p).toFunB a d = PUnit.unit := rfl

/-- Restrict a lens out of `p ⊗ q` to the view where the `q` factor retains
only its positions. -/
def tensorLeftView {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}} (l : Lens (p ⊗ q) r) :
    Lens (p ⊗ linear q.A) r :=
  l ∘ₗ (Lens.id p ⊗ₗ positionCounit q)

@[simp] theorem tensorLeftView_toFunA
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}} (l : Lens (p ⊗ q) r) (pq : p.A × q.A) :
    (tensorLeftView l).toFunA pq = l.toFunA pq := rfl

@[simp] theorem tensorLeftView_toFunB
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}} (l : Lens (p ⊗ q) r) (pq : p.A × q.A)
    (d : r.B (l.toFunA pq)) :
    (tensorLeftView l).toFunB pq d = ((l.toFunB pq d).1, PUnit.unit) := rfl

/-- Restrict a lens out of `p ⊗ q` to the view where the `p` factor retains
only its positions. -/
def tensorRightView {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}} (l : Lens (p ⊗ q) r) :
    Lens (linear p.A ⊗ q) r :=
  l ∘ₗ (positionCounit p ⊗ₗ Lens.id q)

@[simp] theorem tensorRightView_toFunA
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}} (l : Lens (p ⊗ q) r) (pq : p.A × q.A) :
    (tensorRightView l).toFunA pq = l.toFunA pq := rfl

@[simp] theorem tensorRightView_toFunB
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}} (l : Lens (p ⊗ q) r) (pq : p.A × q.A)
    (d : r.B (l.toFunA pq)) :
    (tensorRightView l).toFunB pq d = (PUnit.unit, (l.toFunB pq d).2) := rfl

/-- Glue two one-sided lenses whose position maps agree into a lens
`p ⊗ q ⇆ r` (Spivak–Niu Proposition 5.49). The result reuses the ordinary
`Lens` representation: no parallel “tensor views” structure is introduced. -/
def tensorGlue {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}}
    (left : Lens (p ⊗ linear q.A) r)
    (right : Lens (linear p.A ⊗ q) r)
    (positions : left.toFunA = right.toFunA) : Lens (p ⊗ q) r := by
  rcases left with ⟨leftA, leftB⟩
  rcases right with ⟨rightA, rightB⟩
  dsimp at positions
  subst rightA
  exact leftA ⇆ fun pq d => ((leftB pq d).1, (rightB pq d).2)

@[simp] theorem tensorGlue_toFunA
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}}
    (left : Lens (p ⊗ linear q.A) r)
    (right : Lens (linear p.A ⊗ q) r)
    (positions : left.toFunA = right.toFunA) (pq : p.A × q.A) :
    (tensorGlue left right positions).toFunA pq = left.toFunA pq := by
  rcases left with ⟨leftA, leftB⟩
  rcases right with ⟨rightA, rightB⟩
  dsimp at positions
  subst rightA
  rfl

@[simp] theorem tensorGlue_toFunB_fst
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}}
    (left : Lens (p ⊗ linear q.A) r)
    (right : Lens (linear p.A ⊗ q) r)
    (positions : left.toFunA = right.toFunA) (pq : p.A × q.A)
    (d : r.B ((tensorGlue left right positions).toFunA pq)) :
    ((tensorGlue left right positions).toFunB pq d).1 =
      (left.toFunB pq (tensorGlue_toFunA left right positions pq ▸ d)).1 := by
  rcases left with ⟨leftA, leftB⟩
  rcases right with ⟨rightA, rightB⟩
  dsimp at positions
  subst rightA
  rfl

@[simp] theorem tensorGlue_toFunB_snd
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}}
    (left : Lens (p ⊗ linear q.A) r)
    (right : Lens (linear p.A ⊗ q) r)
    (positions : left.toFunA = right.toFunA) (pq : p.A × q.A)
    (d : r.B ((tensorGlue left right positions).toFunA pq)) :
    ((tensorGlue left right positions).toFunB pq d).2 =
      (right.toFunB pq (positions ▸ tensorGlue_toFunA left right positions pq ▸ d)).2 := by
  rcases left with ⟨leftA, leftB⟩
  rcases right with ⟨rightA, rightB⟩
  dsimp at positions
  subst rightA
  rfl

/-- The left view of a glued lens is the supplied left lens. -/
@[simp] theorem tensorLeftView_tensorGlue
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}}
    (left : Lens (p ⊗ linear q.A) r)
    (right : Lens (linear p.A ⊗ q) r)
    (positions : left.toFunA = right.toFunA) :
    tensorLeftView (tensorGlue left right positions) = left := by
  rcases left with ⟨leftA, leftB⟩
  rcases right with ⟨rightA, rightB⟩
  dsimp at positions
  subst rightA
  refine Lens.ext _ _ (fun _ => rfl) (fun pq => ?_)
  funext d
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

/-- The right view of a glued lens is the supplied right lens. -/
@[simp] theorem tensorRightView_tensorGlue
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}}
    (left : Lens (p ⊗ linear q.A) r)
    (right : Lens (linear p.A ⊗ q) r)
    (positions : left.toFunA = right.toFunA) :
    tensorRightView (tensorGlue left right positions) = right := by
  rcases left with ⟨leftA, leftB⟩
  rcases right with ⟨rightA, rightB⟩
  dsimp at positions
  subst rightA
  refine Lens.ext _ _ (fun _ => rfl) (fun pq => ?_)
  funext d
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

/-- Gluing the two canonical one-sided views of a lens recovers that lens. -/
@[simp] theorem tensorGlue_leftView_rightView
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}}
    (l : Lens (p ⊗ q) r) :
    tensorGlue (tensorLeftView l) (tensorRightView l) rfl = l := by
  refine Lens.ext _ _ (fun _ => rfl) (fun pq => ?_)
  funext d
  exact Prod.eta (l.toFunB pq d)

/-- The tensor-gluing universal property as an equivalence: lenses out of a
tensor are exactly pairs of ordinary one-sided lenses whose position maps
agree. The compatibility object is written inline as a subtype, rather than
bundled into a second representation equivalent to `Lens (p ⊗ q) r`. -/
def tensorGlueEquiv {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₁, uB₁}}
    {r : PFunctor.{uA₂, uB₂}} :
    Lens (p ⊗ q) r ≃
      { views : Lens (p ⊗ linear q.A) r × Lens (linear p.A ⊗ q) r //
        views.1.toFunA = views.2.toFunA } where
  toFun l := ⟨(tensorLeftView l, tensorRightView l), rfl⟩
  invFun views := tensorGlue views.1.1 views.1.2 views.2
  left_inv := tensorGlue_leftView_rightView
  right_inv views := by
    apply Subtype.ext
    apply Prod.ext
    · exact tensorLeftView_tensorGlue views.1.1 views.1.2 views.2
    · exact tensorRightView_tensorGlue views.1.1 views.1.2 views.2

end Lens

end PFunctor
