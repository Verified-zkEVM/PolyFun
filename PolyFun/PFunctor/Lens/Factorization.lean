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

Following Spivak–Niu, *Polynomial Functors: A General Theory of Interaction*
(§5.5, Prop 5.51–5.53), this file constructs the vertical–cartesian
factorization of a lens. The orthogonality and lifting laws needed to package a
factorization system are not formalized here. The two classes are:

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

The downstream consumer is the `LawfulSubSpec` theory in VCVio, where the
cartesian leg is the probability-preserving part of a sub-spec embedding.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

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
  (fun i => i) ⇆ l.toFunB

/-- The cartesian leg `factorMid l ⇆ Q`: `l.toFunA` on positions, identity on
each direction fiber. -/
def factorCart (l : Lens P Q) : Lens (factorMid l) Q :=
  l.toFunA ⇆ (fun _ d => d)

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
theorem toLens_isVertical (e : P ≃ₗ Q) : e.toLens.IsVertical := by
  apply Function.bijective_iff_has_inverse.mpr
  exact ⟨e.invLens.toFunA,
    fun a => congrFun (congrArg Lens.toFunA e.left_inv) a,
    fun b => congrFun (congrArg Lens.toFunA e.right_inv) b⟩

/-- The forward lens of a lens equivalence is cartesian. The two inverse lens
laws make each backward fiber map bijective. -/
theorem toLens_isCartesian (e : P ≃ₗ Q) : e.toLens.IsCartesian := by
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
