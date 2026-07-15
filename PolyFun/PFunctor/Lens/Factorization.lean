/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Cartesian
import Batteries.Tactic.Lint

/-!
# Vertical–cartesian factorization of lenses

Following Spivak–Niu, *Polynomial Functors: A Mathematical Theory of Interaction*
(§5.5, Prop 5.51–5.53), this file constructs the vertical–cartesian
factorization of a lens and proves the corresponding lifting law. The two
classes are:

* **cartesian** lenses — every backward fiber `toFunB a` is a bijection
  (already `PFunctor.Lens.IsCartesian`); and
* **vertical** lenses — the forward map on positions `toFunA` is a bijection
  (`IsVertical`).

Every lens `l : Lens P Q` factors as a vertical lens followed by a cartesian
lens through the middle object `factorMid l = Σ_{i} y^{Q[l.toFunA i]}`:

`P --factorVert--> factorMid l --factorCart--> Q`, with the composite equal to `l`.

The two classes meet in the isomorphisms: a lens is a `PFunctor.Lens.Equiv`
exactly when it is both vertical (`toFunA` bijective) and cartesian (`toFunB a`
bijective), as recorded in `PFunctor/Lens/Cartesian.lean`. That equivalence is
built here as `equivOfVerticalCartesian`, by packaging the position bijection
and the fiber bijections into a `PFunctor.Equiv` and pushing through
`PFunctor.Equiv.toLensEquiv`.

Both classes are closed under the polynomial operations (Spivak–Niu Prop 5.63,
6.88): `IsVertical.sumMap` / `prodMap` / `tensorMap` and `IsCartesian.prodMap`
/ `tensorMap` / `compMap` witness closure under `+`, `×`, `⊗`, and `◃`. Vertical
lenses are *not* closed under the copairing `sumPair` (a `Sum.elim` of two
bijections into a shared codomain need not be injective), so no such witness is
provided.

Finally, `verticalCartesianDiagonal` constructs the unique diagonal in every
commutative square whose left edge is vertical and whose right edge is
cartesian.  Thus the two classes are orthogonal, not merely complementary
classes through which every lens happens to factor.

The downstream consumer is the `LawfulSubSpec` theory in VCVio, where the
cartesian leg is the probability-preserving part of a sub-spec embedding.
-/

@[expose] public section

universe u v w z uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

namespace PFunctor

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- A lens `l : Lens P Q` is **vertical** when its forward map on positions
`l.toFunA` is a bijection. Together with `IsCartesian`, the two classes meet in
the isomorphisms. -/
def IsVertical (l : Lens P Q) : Prop :=
  Function.Bijective l.toFunA

namespace IsVertical

@[simp]
theorem id (P : PFunctor.{uA, uB}) : (Lens.id P).IsVertical :=
  Function.bijective_id

theorem comp {l₁ : Lens Q R} {l₂ : Lens P Q}
    (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) : (l₁ ∘ₗ l₂).IsVertical :=
  show Function.Bijective (l₁.toFunA ∘ l₂.toFunA) from Function.Bijective.comp h₁ h₂

/-- Verticality is closed under the coproduct `⊎ₗ`: the position map of
`l₁ ⊎ₗ l₂` is `Sum.map l₁.toFunA l₂.toFunA`, bijective when both legs are. -/
theorem sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) : (l₁ ⊎ₗ l₂).IsVertical :=
  Function.Bijective.sumMap h₁ h₂

/-- Verticality is closed under the categorical product `×ₗ`: the position map of
`l₁ ×ₗ l₂` is `Prod.map l₁.toFunA l₂.toFunA`, bijective when both legs are. -/
theorem prodMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₄}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) : (l₁ ×ₗ l₂).IsVertical :=
  Function.Bijective.prodMap h₁ h₂

/-- Verticality is closed under the tensor product `⊗ₗ`: the position map of
`l₁ ⊗ₗ l₂` agrees with that of `l₁ ×ₗ l₂` (`Prod.map` on positions), so it is
bijective when both legs are. -/
theorem tensorMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₄}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) : (l₁ ⊗ₗ l₂).IsVertical :=
  Function.Bijective.prodMap h₁ h₂

end IsVertical

/-! ## The factorization -/

/-- The middle object of the vertical–cartesian factorization of `l`:
`Σ_{i : P.A} y^{Q.B (l.toFunA i)}`. It shares the positions of `P` and the
directions of `Q` (pulled along `l.toFunA`). -/
def factorMid (l : Lens P Q) : PFunctor.{uA₁, uB₂} :=
  ⟨P.A, fun i => Q.B (l.toFunA i)⟩

/-- The vertical leg `P ⇆ factorMid l`: identity on positions, `l.toFunB` on
directions. -/
def factorVert (l : Lens P Q) : Lens P (factorMid l) :=
  id ⇆ l.toFunB

/-- The cartesian leg `factorMid l ⇆ Q`: `l.toFunA` on positions, identity on
each direction fiber. -/
def factorCart (l : Lens P Q) : Lens (factorMid l) Q :=
  l.toFunA ⇆ fun _ => id

/-- The factorization recovers the original lens. -/
@[simp]
theorem factorCart_comp_factorVert (l : Lens P Q) :
    factorCart l ∘ₗ factorVert l = l := rfl

/-- The vertical leg is vertical. -/
theorem factorVert_isVertical (l : Lens P Q) : (factorVert l).IsVertical :=
  Function.bijective_id

/-- The cartesian leg is cartesian. -/
theorem factorCart_isCartesian (l : Lens P Q) : (factorCart l).IsCartesian :=
  fun _ => Function.bijective_id

/-! ## Orthogonality

Given a commutative square

```
P ---f---> R
|          |
v          c
|          |
V          V
Q ---g---> S
```

with `v` vertical and `c` cartesian, there is a unique diagonal `d : Q ⇆ R`.
Surjectivity of the position map of `v` determines the forward map of `d`;
bijectivity of each backward fiber of `c` determines its backward map. -/

/-- A diagonal filler for a commutative lens square. -/
structure DiagonalFiller {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S) where
  /-- The diagonal lens from the lower-left to the upper-right corner. -/
  diagonal : Lens Q R
  /-- The upper triangle commutes. -/
  comp_left : diagonal ∘ₗ v = f
  /-- The lower triangle commutes. -/
  comp_right : c ∘ₗ diagonal = g

/-- The position equivalence carried by a vertical lens. -/
noncomputable def verticalPositionEquiv (v : Lens P Q) (hv : v.IsVertical) : P.A ≃ Q.A :=
  _root_.Equiv.ofBijective v.toFunA hv

@[simp] theorem verticalPositionEquiv_apply (v : Lens P Q) (hv : v.IsVertical) (p : P.A) :
    verticalPositionEquiv v hv p = v.toFunA p := rfl

@[simp] theorem verticalPositionEquiv_symm_toFunA (v : Lens P Q) (hv : v.IsVertical)
    (p : P.A) : (verticalPositionEquiv v hv).symm (v.toFunA p) = p :=
  (verticalPositionEquiv v hv).symm_apply_apply p

/-- The backward-fiber equivalence carried by a cartesian lens at a position. -/
noncomputable def cartesianDirectionEquiv (c : Lens P Q) (hc : c.IsCartesian) (p : P.A) :
    Q.B (c.toFunA p) ≃ P.B p :=
  _root_.Equiv.ofBijective (c.toFunB p) (hc p)

@[simp] theorem cartesianDirectionEquiv_apply (c : Lens P Q) (hc : c.IsCartesian)
    (p : P.A) (q : Q.B (c.toFunA p)) :
    cartesianDirectionEquiv c hc p q = c.toFunB p q := rfl

@[simp] theorem cartesianDirectionEquiv_symm_toFunB (c : Lens P Q) (hc : c.IsCartesian)
    (p : P.A) (q : Q.B (c.toFunA p)) :
    (cartesianDirectionEquiv c hc p).symm (c.toFunB p q) = q :=
  (cartesianDirectionEquiv c hc p).left_inv q

@[simp] theorem cartesianDirectionEquiv_toFunB_symm (c : Lens P Q) (hc : c.IsCartesian)
    (p : P.A) (r : P.B p) :
    c.toFunB p ((cartesianDirectionEquiv c hc p).symm r) = r :=
  (cartesianDirectionEquiv c hc p).apply_symm_apply r

/-- The position component of the lower triangle for the canonical diagonal. -/
theorem verticalCartesianDiagonal_pos_comm
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (comm : c ∘ₗ f = g ∘ₗ v) (q : Q.A) :
    c.toFunA (f.toFunA ((verticalPositionEquiv v hv).symm q)) = g.toFunA q := by
  have h := congrFun (congrArg Lens.toFunA comm) ((verticalPositionEquiv v hv).symm q)
  change c.toFunA (f.toFunA ((verticalPositionEquiv v hv).symm q)) =
    g.toFunA (verticalPositionEquiv v hv ((verticalPositionEquiv v hv).symm q)) at h
  simpa using h

private theorem transport_inverse_comp {I : Type u} (B : I → Type v) {x y : I}
    (h : x = y) {A : Type w} {C : Type z} (e : B x ≃ A) (k : B y → C) :
    (fun a => k (h ▸ e.symm a)) ∘ e = h.symm ▸ k := by
  cases h
  funext a
  exact congrArg k (e.symm_apply_apply a)

private theorem toFunB_heq_of_eq {P : PFunctor.{uA₁, uB₁}}
    {Q : PFunctor.{uA₂, uB₂}} {l₁ l₂ : Lens P Q} (h : l₁ = l₂) (p : P.A) :
    l₁.toFunB p ≍ l₂.toFunB p := by
  cases h
  rfl

/-- The canonical diagonal in a vertical-left/cartesian-right square.

The definition uses the inverse of the vertical position bijection and the
inverse of the cartesian backward-fiber bijections. -/
noncomputable def verticalCartesianDiagonal
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) : Lens Q R := by
  let toA : Q.A → R.A := fun q => f.toFunA ((verticalPositionEquiv v hv).symm q)
  have hpos (q : Q.A) : c.toFunA (toA q) = g.toFunA q :=
    verticalCartesianDiagonal_pos_comm v f c g hv comm q
  exact toA ⇆ fun q rb =>
    g.toFunB q (hpos q ▸
      (cartesianDirectionEquiv c hc (toA q)).symm rb)

/-- The canonical diagonal fills the left triangle. -/
@[simp] theorem verticalCartesianDiagonal_comp_left
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    verticalCartesianDiagonal v f c g hv hc comm ∘ₗ v = f := by
  let hA : ∀ p, (verticalCartesianDiagonal v f c g hv hc comm ∘ₗ v).toFunA p =
      f.toFunA p := fun p => by
    change f.toFunA ((verticalPositionEquiv v hv).symm (v.toFunA p)) = f.toFunA p
    rw [verticalPositionEquiv_symm_toFunA]
  apply Lens.ext _ _ hA
  intro p
  apply eq_of_heq
  have hp : c.toFunA (f.toFunA p) = g.toFunA (v.toFunA p) := by
    exact congrFun (congrArg Lens.toFunA comm) p
  let e := cartesianDirectionEquiv c hc (f.toFunA p)
  have hnorm : (verticalCartesianDiagonal v f c g hv hc comm ∘ₗ v).toFunB p ≍
      v.toFunB p ∘ fun rb => g.toFunB (v.toFunA p) (hp ▸ e.symm rb) := by
    let p' := (verticalPositionEquiv v hv).symm (v.toFunA p)
    have hpp : p' = p := verticalPositionEquiv_symm_toFunA v hv p
    change (v.toFunB p ∘ fun rb => g.toFunB (v.toFunA p)
      (verticalCartesianDiagonal_pos_comm v f c g hv comm (v.toFunA p) ▸
        (cartesianDirectionEquiv c hc (f.toFunA p')).symm rb)) ≍ _
    apply Function.hfunext (congrArg R.B (congrArg f.toFunA hpp))
    intro rb' rb hrb
    apply heq_of_eq
    apply congrArg (v.toFunB p)
    apply congrArg (g.toFunB (v.toFunA p))
    let invPacked : (Σ x, R.B (f.toFunA x)) → (Σ x, S.B (c.toFunA (f.toFunA x))) :=
      fun x => ⟨x.1, (cartesianDirectionEquiv c hc (f.toFunA x.1)).symm x.2⟩
    have hz : (⟨p', rb'⟩ : Σ x, R.B (f.toFunA x)) = ⟨p, rb⟩ := Sigma.ext hpp hrb
    have hout := congrArg invPacked hz
    have hs : (cartesianDirectionEquiv c hc (f.toFunA p')).symm rb' ≍
        e.symm rb := congr_arg_heq Sigma.snd hout
    exact eq_of_heq ((eqRec_heq _ _).trans (hs.trans (eqRec_heq _ _).symm))
  have hnormEq : (v.toFunB p ∘ fun rb =>
      g.toFunB (v.toFunA p) (hp ▸ e.symm rb)) = f.toFunB p := by
    funext rb
    have hfun := toFunB_heq_of_eq comm p
    have harg : e.symm rb ≍ hp ▸ e.symm rb := (eqRec_heq _ _).symm
    have hsquare := congr_heq hfun harg
    simpa [comp, Function.comp_apply, e] using hsquare.symm
  have hcast : (hA p ▸ f.toFunB p) ≍ f.toFunB p := by
    exact eqRec_heq_self _ _
  exact hnorm.trans ((heq_of_eq hnormEq).trans hcast.symm)

/-- The canonical diagonal fills the right triangle. -/
@[simp] theorem verticalCartesianDiagonal_comp_right
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    c ∘ₗ verticalCartesianDiagonal v f c g hv hc comm = g := by
  refine Lens.ext _ _ (verticalCartesianDiagonal_pos_comm v f c g hv comm) ?_
  intro q
  exact transport_inverse_comp S.B
    (verticalCartesianDiagonal_pos_comm v f c g hv comm q)
    (cartesianDirectionEquiv c hc _) (g.toFunB q)

/-- Vertical lenses have the left lifting property with respect to cartesian
lenses. The returned filler carries both commuting triangle equations. -/
noncomputable def verticalCartesianFiller
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    DiagonalFiller v f c g where
  diagonal := verticalCartesianDiagonal v f c g hv hc comm
  comp_left := verticalCartesianDiagonal_comp_left v f c g hv hc comm
  comp_right := verticalCartesianDiagonal_comp_right v f c g hv hc comm

/-- Existence form of vertical/cartesian orthogonality. -/
theorem exists_verticalCartesianDiagonal
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    Nonempty (DiagonalFiller v f c g) :=
  ⟨verticalCartesianFiller v f c g hv hc comm⟩

/-- The forward map of a diagonal filler is forced by the left triangle and
the vertical position bijection. -/
theorem diagonalFiller_toFunA_unique
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v)
    (d : DiagonalFiller v f c g) (q : Q.A) :
    d.diagonal.toFunA q =
      (verticalCartesianDiagonal v f c g hv hc comm).toFunA q := by
  have h := congrFun (congrArg Lens.toFunA d.comp_left) ((verticalPositionEquiv v hv).symm q)
  change d.diagonal.toFunA
      (verticalPositionEquiv v hv ((verticalPositionEquiv v hv).symm q)) =
    f.toFunA ((verticalPositionEquiv v hv).symm q) at h
  rw [_root_.Equiv.apply_symm_apply] at h
  exact h

private theorem eq_of_comp_cartesian_eq_of_toFunA_eq
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} (l₁ l₂ : Lens P Q) (c : Lens Q R)
    (hc : c.IsCartesian) (hA : ∀ p, l₁.toFunA p = l₂.toFunA p)
    (hcomp : c ∘ₗ l₁ = c ∘ₗ l₂) : l₁ = l₂ := by
  apply Lens.ext _ _ hA
  intro p
  apply eq_of_heq
  have hfun := toFunB_heq_of_eq hcomp p
  have hcancel : l₁.toFunB p ≍ l₂.toFunB p := by
    apply Function.hfunext (congrArg Q.B (hA p))
    intro r₁ r₂ hr
    let invPacked : (Σ q, Q.B q) → (Σ q, R.B (c.toFunA q)) :=
      fun x => ⟨x.1, (cartesianDirectionEquiv c hc x.1).symm x.2⟩
    have hz : (⟨l₁.toFunA p, r₁⟩ : Σ q, Q.B q) = ⟨l₂.toFunA p, r₂⟩ :=
      Sigma.ext (hA p) hr
    have hout := congrArg invPacked hz
    have hs : (cartesianDirectionEquiv c hc (l₁.toFunA p)).symm r₁ ≍
        (cartesianDirectionEquiv c hc (l₂.toFunA p)).symm r₂ :=
      congr_arg_heq Sigma.snd hout
    have happ := congr_heq hfun hs
    simpa [comp, Function.comp_apply] using happ
  have hcast : (hA p ▸ l₂.toFunB p) ≍ l₂.toFunB p := by
    exact eqRec_heq_self _ _
  exact hcancel.trans hcast.symm

/-- The vertical/cartesian diagonal is unique. Consequently the bundled type
of fillers of such a square is a subsingleton. -/
theorem verticalCartesianDiagonal_unique
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v)
    (d : DiagonalFiller v f c g) :
    d.diagonal = verticalCartesianDiagonal v f c g hv hc comm := by
  apply eq_of_comp_cartesian_eq_of_toFunA_eq _ _ c hc
    (diagonalFiller_toFunA_unique v f c g hv hc comm d)
  rw [d.comp_right, verticalCartesianDiagonal_comp_right v f c g hv hc comm]

/-- Orthogonality in bundled form: a vertical/cartesian square has exactly one
diagonal filler. -/
theorem subsingleton_verticalCartesianFillers
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    Subsingleton (DiagonalFiller v f c g) where
  allEq d₁ d₂ := by
    cases d₁ with
    | mk diagonal₁ left₁ right₁ =>
      cases d₂ with
      | mk diagonal₂ left₂ right₂ =>
        have h₁ := verticalCartesianDiagonal_unique v f c g hv hc comm
          ⟨diagonal₁, left₁, right₁⟩
        have h₂ := verticalCartesianDiagonal_unique v f c g hv hc comm
          ⟨diagonal₂, left₂, right₂⟩
        change diagonal₁ = _ at h₁
        change diagonal₂ = _ at h₂
        cases h₁
        cases h₂
        rfl

/-! ## Closure of cartesian lenses under the polynomial operations

The cartesian analogues of the verticality closure lemmas (Spivak–Niu Prop 5.63,
6.88). Unlike positions, the fiber of a product / tensor / composition splits as
a `Sum.map` / `Prod.map` / dependent `Sigma`-map of the leg fibers, so each is a
bijection when both legs are cartesian. -/

namespace IsCartesian

/-- Cartesianness is closed under the categorical product `×ₗ`: the fiber of
`l₁ ×ₗ l₂` at `pq` is `Sum.map (l₁.toFunB pq.1) (l₂.toFunB pq.2)`. -/
theorem prodMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₄}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) : (l₁ ×ₗ l₂).IsCartesian := fun pq => by
  have hfib : (l₁ ×ₗ l₂).toFunB pq = Sum.map (l₁.toFunB pq.1) (l₂.toFunB pq.2) := by
    funext d; cases d <;> rfl
  rw [hfib]
  exact Function.Bijective.sumMap (h₁ pq.1) (h₂ pq.2)

/-- Cartesianness is closed under the tensor product `⊗ₗ`: the fiber of
`l₁ ⊗ₗ l₂` at `pq` is `Prod.map (l₁.toFunB pq.1) (l₂.toFunB pq.2)`. -/
theorem tensorMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₄}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) : (l₁ ⊗ₗ l₂).IsCartesian := fun pq =>
  Function.Bijective.prodMap (h₁ pq.1) (h₂ pq.2)

/-- Cartesianness is closed under the composition `◃ₗ` (Spivak–Niu Prop 6.88):
the fiber of `l₁ ◃ₗ l₂` at `⟨pa, pq⟩` sends `⟨rb, wc⟩` to
`⟨l₁.toFunB pa rb, l₂.toFunB (pq (l₁.toFunB pa rb)) wc⟩`, a dependent
`Sigma`-congruence built from the base bijection `l₁.toFunB pa` and the fiber
bijections `l₂.toFunB _`. -/
theorem compMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₄}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) : (l₁ ◃ₗ l₂).IsCartesian := by
  rintro ⟨pa, pq⟩
  exact (_root_.Equiv.sigmaCongr (β₂ := fun pb => Q.B (pq pb))
    (_root_.Equiv.ofBijective _ (h₁ pa))
    (fun rb => _root_.Equiv.ofBijective _ (h₂ (pq (l₁.toFunB pa rb))))).bijective

end IsCartesian

/-! ## The intersection: vertical ∩ cartesian = iso -/

namespace Equiv

/-- The forward lens of a lens equivalence is vertical: its inverse lens
supplies the inverse of its position map. -/
@[simp] theorem toLens_isVertical (e : P ≃ₗ Q) : e.toLens.IsVertical := by
  apply Function.bijective_iff_has_inverse.mpr
  exact ⟨e.invLens.toFunA,
    fun a => congrFun (congrArg Lens.toFunA e.left_inv) a,
    fun b => congrFun (congrArg Lens.toFunA e.right_inv) b⟩

/-- The forward lens of a lens equivalence is cartesian. The two inverse lens
laws make each backward fiber map bijective. -/
@[simp] theorem toLens_isCartesian (e : P ≃ₗ Q) : e.toLens.IsCartesian := by
  intro a
  have hleft : (e.invLens ∘ₗ e.toLens).IsCartesian := by
    rw [e.left_inv]
    exact IsCartesian.id P
  have hright : (e.toLens ∘ₗ e.invLens).IsCartesian := by
    rw [e.right_inv]
    exact IsCartesian.id Q
  constructor
  · have hinj : Function.Injective
        (e.toLens.toFunB (e.invLens.toFunA (e.toLens.toFunA a))) :=
      Function.Injective.of_comp (hright (e.toLens.toFunA a)).1
    have hA : e.invLens.toFunA (e.toLens.toFunA a) = a :=
      congrFun (congrArg Lens.toFunA e.left_inv) a
    exact hA ▸ hinj
  · exact Function.Surjective.of_comp (hleft a).2

/-- The inverse lens of a lens equivalence is vertical. -/
@[simp] theorem invLens_isVertical (e : P ≃ₗ Q) : e.invLens.IsVertical :=
  e.symm.toLens_isVertical

/-- The inverse lens of a lens equivalence is cartesian. -/
@[simp] theorem invLens_isCartesian (e : P ≃ₗ Q) : e.invLens.IsCartesian :=
  e.symm.toLens_isCartesian

end Equiv

/-- A lens that is both **vertical** (position map bijective) and **cartesian**
(every fiber bijective) is an isomorphism `P ≃ₗ Q`. This realizes the meeting of
the two factorization classes: the position bijection and the fiber bijections
assemble into a `PFunctor.Equiv`, which `PFunctor.Equiv.toLensEquiv` turns into a
lens equivalence. -/
noncomputable def equivOfVerticalCartesian (l : Lens P Q)
    (hv : l.IsVertical) (hc : l.IsCartesian) : P ≃ₗ Q :=
  PFunctor.Equiv.toLensEquiv
    { equivA := _root_.Equiv.ofBijective l.toFunA hv
      equivB := fun a => (_root_.Equiv.ofBijective (l.toFunB a) (hc a)).symm }

@[simp] theorem equivOfVerticalCartesian_toLens (l : Lens P Q)
    (hv : l.IsVertical) (hc : l.IsCartesian) :
    (equivOfVerticalCartesian l hv hc).toLens = l := by
  ext <;> rfl

/-- A lens is the forward map of a lens equivalence exactly when it is both
vertical and cartesian. -/
theorem exists_equiv_toLens_iff (l : Lens P Q) :
    (∃ e : P ≃ₗ Q, e.toLens = l) ↔ l.IsVertical ∧ l.IsCartesian := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.toLens_isVertical, e.toLens_isCartesian⟩
  · rintro ⟨hv, hc⟩
    exact ⟨equivOfVerticalCartesian l hv hc, equivOfVerticalCartesian_toLens l hv hc⟩

end Lens

end PFunctor
