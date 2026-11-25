/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Cartesian Lenses Between Polynomial Functors

A `Lens P Q` between polynomial functors carries a forward map on positions
(`toFunA : P.A → Q.A`) and, for each position `a : P.A`, a backward map on
directions (`toFunB a : Q.B (toFunA a) → P.B a`). We say the lens is
**cartesian** when every backward map `toFunB a` is a bijection.

In the language of the fibration `Poly → Set` that sends a polynomial
functor to its set of positions, cartesian lenses are exactly the
cartesian morphisms: the type-square underlying each fiber is a pullback.
A cartesian lens is a *fiberwise isomorphism* over an arbitrary forward
map on positions.

The two classes in the orthogonal factorization system on `Poly` are captured
separately:

* a **vertical** lens has bijective `toFunA` (it changes position coordinates
  without losing or adding positions); and
* a **cartesian** lens has each `toFunB a` a bijection (each direction fiber is
  rigid over an arbitrary position map).

The canonical vertical leg in the factorization is identity on positions, but
identity is a chosen representative of the more general bijective-on-positions
class. See `PFunctor.Lens.IsVertical` in `Lens/Factorization.lean`.

A `PFunctor.Lens.Equiv` (a categorical isomorphism in the lens category)
is the intersection of the two: `toFunA` is a bijection AND every
`toFunB a` is a bijection. Thus *every* `Equiv` is cartesian, but a
cartesian lens whose position map is not a bijection (e.g.
`Lens.inl : Lens P (P + Q)`) is not an `Equiv`.

In VCVio, `LawfulSubSpec` supplies a bijective backward map at each query.
Its underlying lens is therefore cartesian, so the uniform distribution on
each finite response type pulls back to the uniform distribution on the source responses.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

namespace PFunctor

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- A lens `l : Lens P Q` is **cartesian** when every backward fiber
`l.toFunB a : Q.B (l.toFunA a) → P.B a` is a bijection. Equivalently,
`l` is a cartesian morphism in the fibration `Poly → Set` of polynomial
functors over their position sets. -/
class IsCartesian (l : Lens P Q) : Prop where
  /-- The backward map is bijective at each source position. -/
  bijective (a : P.A) : Function.Bijective (l.toFunB a)

namespace IsCartesian

@[simp]
instance id (P : PFunctor.{uA, uB}) : (Lens.id P).IsCartesian where
  bijective _ := Function.bijective_id

theorem comp {l₁ : Lens Q R} {l₂ : Lens P Q}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (l₁ ∘ₗ l₂).IsCartesian where
  bijective a := (h₂.bijective a).comp (h₁.bijective (l₂.toFunA a))

instance {l₁ : Lens Q R} {l₂ : Lens P Q}
    [h₁ : l₁.IsCartesian] [h₂ : l₂.IsCartesian] :
    (l₁ ∘ₗ l₂).IsCartesian :=
  comp h₁ h₂

end IsCartesian

/-! ## Cartesianness of canonical lens constructors

Most "embedding-shaped" lenses produced by the lens algebra are cartesian.
We collect the witnesses here so that downstream classes (notably
`LawfulSubSpec`) can be discharged uniformly. -/

namespace IsCartesian

instance inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    (Lens.inl : Lens.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q)).IsCartesian where
  bijective _ := Function.bijective_id

instance inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    (Lens.inr : Lens.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q)).IsCartesian where
  bijective _ := Function.bijective_id

theorem sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (l₁ ⊎ₗ l₂).IsCartesian where
  bijective
    | Sum.inl a => h₁.bijective a
    | Sum.inr a => h₂.bijective a

instance {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    [h₁ : l₁.IsCartesian] [h₂ : l₂.IsCartesian] :
    (l₁ ⊎ₗ l₂).IsCartesian :=
  sumMap h₁ h₂

theorem sumPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB₃}} {l₁ : Lens P R} {l₂ : Lens Q R}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (Lens.sumPair l₁ l₂).IsCartesian where
  bijective
    | Sum.inl a => h₁.bijective a
    | Sum.inr a => h₂.bijective a

instance {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB₃}} {l₁ : Lens P R} {l₂ : Lens Q R}
    [h₁ : l₁.IsCartesian] [h₂ : l₂.IsCartesian] :
    (Lens.sumPair l₁ l₂).IsCartesian :=
  sumPair h₁ h₂

theorem sigmaMap {I : Type v}
    {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    {l : ∀ i, Lens (F i) (G i)} (hl : ∀ i, (l i).IsCartesian) :
    (Lens.sigmaMap l).IsCartesian where
  bijective | ⟨i, fa⟩ => (hl i).bijective fa

instance {I : Type v}
    {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    {l : ∀ i, Lens (F i) (G i)} [hl : ∀ i, (l i).IsCartesian] :
    (Lens.sigmaMap l).IsCartesian :=
  sigmaMap hl

theorem sigmaExists {I : Type v}
    {F : I → PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}}
    {l : ∀ i, Lens (F i) R} (hl : ∀ i, (l i).IsCartesian) :
    (Lens.sigmaExists l).IsCartesian where
  bijective | ⟨i, fa⟩ => (hl i).bijective fa

instance {I : Type v}
    {F : I → PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}}
    {l : ∀ i, Lens (F i) R} [hl : ∀ i, (l i).IsCartesian] :
    (Lens.sigmaExists l).IsCartesian :=
  sigmaExists hl

end IsCartesian

/-! ## Sigma injection

The natural inclusion of the `j`-th summand into a `sigma`: the unique
lens whose forward action picks the `j`-th tag and whose backward action
is the identity on directions. This is the `Lens` whose corresponding
`MonadLift` underlies `OracleSpec.subSpec_sigma`. -/

/-- Lens injection `Lens (F j) (sigma F)` for a fixed index `j : I`. -/
def sigmaInj {I : Type v} {F : I → PFunctor.{uA, uB}} (j : I) :
    Lens (F j) (sigma F) :=
  (fun fa => sigma.mk j fa) ⇆ fun _ => id

namespace IsCartesian

instance sigmaInj {I : Type v} {F : I → PFunctor.{uA, uB}} (j : I) :
    (Lens.sigmaInj (F := F) j).IsCartesian where
  bijective _ := Function.bijective_id

end IsCartesian

end Lens

end PFunctor
