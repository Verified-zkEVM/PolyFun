/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Category
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The weighted exponential on lenses

At each position `a`, the directions of `bangW S P` are finitely supported weights
`P.B a →₀ S`. When the weights form an additive commutative monoid, a lens sends each
output weight back to the input direction it reads, adding weights that reach the same input.
`Lens.liftAddHom_bangWMap` relates this operation to the forward action on labels.

For commutative semiring weights, the counit places a weight of one on a direction and the
comultiplication takes a weighted sum of weightings. These operations give a comonad. The
lens laws hold for weights in any universe. The bundled functor and comonad take weights
in the universe of directions so their target is the same lens category.

## Main definitions

* `bangW` — the weighted exponential;
* `Lens.bangWMap`, `Lens.bangWCounit`, `Lens.bangWComult` — its action on lenses, counit and
  comultiplication;
* `LensCat.bangWFunctor`, `LensCat.bangWComonad` — the comonad on `LensCat`, for `S` in the
  universe of directions.

## Main results

* `Lens.bangWMap_id`, `Lens.bangWMap_comp`, `Lens.bangWCounit_natural`,
  `Lens.bangWComult_natural`, `Lens.bangWCounit_comult`, `Lens.bangWMap_counit_comult`,
  `Lens.bangWComult_coassoc` — the comonad laws.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ w

open CategoryTheory

namespace PFunctor

variable (S : Type w)

/-- The weighted exponential: the positions of `P`, and at a position the finitely supported
weightings of the directions of `P` at it. Its directions live in `max uB w`, where `S : Type w`;
the comonad on `LensCat.{uA, uB}` therefore requires `S` in the universe of directions `uB`. -/
abbrev bangW [Zero S] (P : PFunctor.{uA, uB}) : PFunctor.{uA, max uB w} :=
  ⟨P.A, fun a => P.B a →₀ S⟩

namespace Lens

variable {S}
section Additive

variable [AddCommMonoid S]
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- The action of the weighted exponential on a lens: the weights are pushed along the backward
map. -/
noncomputable def bangWMap (l : Lens P Q) : Lens (bangW S P) (bangW S Q) :=
  l.toFunA ⇆ fun a w => Finsupp.mapDomain (l.toFunB a) w

/-- The weighted exponential preserves identities. -/
theorem bangWMap_id : bangWMap (S := S) (Lens.id P) = Lens.id (bangW S P) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Finsupp.mapDomain_id

/-- The weighted exponential preserves composition. -/
theorem bangWMap_comp (m : Lens Q R) (l : Lens P Q) :
    bangWMap (S := S) (m ∘ₗ l) = bangWMap (S := S) m ∘ₗ bangWMap (S := S) l :=
  Lens.ext _ _ (fun _ => rfl) fun a =>
    funext fun (w : R.B (m.toFunA (l.toFunA a)) →₀ S) => by
    change Finsupp.mapDomain (l.toFunB a ∘ m.toFunB (l.toFunA a)) w =
      Finsupp.mapDomain (l.toFunB a) (Finsupp.mapDomain (m.toFunB (l.toFunA a)) w)
    exact Finsupp.mapDomain_comp

/-- Evaluating additive labels on the accumulated input weights gives the same total as
evaluating the labels transported by `mapObj` on the output weights. -/
theorem liftAddHom_bangWMap {T : Type*} [AddCommMonoid T]
    (l : Lens P Q) (x : P.Obj (S →+ T)) (w : Q.B (l.toFunA x.fst) →₀ S) :
    Finsupp.liftAddHom x.snd ((bangWMap (S := S) l).toFunB x.fst w) =
      Finsupp.liftAddHom (l.mapObj x).snd w :=
  Finsupp.sum_mapDomain_index_addMonoidHom x.snd

end Additive

variable [CommSemiring S]
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

variable (S) in
/-- The counit of the weighted exponential: a direction demands itself with weight one. -/
noncomputable def bangWCounit (P : PFunctor.{uA, uB}) : Lens (bangW S P) P :=
  id ⇆ fun _ d => Finsupp.single d 1

variable (S) in
/-- The comultiplication of the weighted exponential: a weighting of weightings demands their
weighted sum. -/
noncomputable def bangWComult (P : PFunctor.{uA, uB}) :
    Lens (bangW S P) (bangW S (bangW S P)) :=
  id ⇆ fun _ ww => Finsupp.linearCombination S id ww

/-- The counit of the weighted exponential is natural. -/
theorem bangWCounit_natural (l : Lens P Q) :
    bangWCounit S Q ∘ₗ bangWMap l = l ∘ₗ bangWCounit S P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Finsupp.mapDomain_single

/-- The comultiplication of the weighted exponential is natural. -/
theorem bangWComult_natural (l : Lens P Q) :
    bangWComult S Q ∘ₗ bangWMap l = bangWMap (bangWMap l) ∘ₗ bangWComult S P :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (ww : (Q.B (l.toFunA a) →₀ S) →₀ S) => by
    change Finsupp.mapDomain (l.toFunB a) (Finsupp.linearCombination S id ww) =
      Finsupp.linearCombination S id (Finsupp.mapDomain (Finsupp.mapDomain (l.toFunB a)) ww)
    rw [Finsupp.linearCombination_mapDomain]
    exact Finsupp.apply_linearCombination_id S (Finsupp.lmapDomain S S (l.toFunB a)) ww

/-- Left counit law of the weighted exponential. -/
theorem bangWCounit_comult (P : PFunctor.{uA, uB}) :
    bangWCounit S (bangW S P) ∘ₗ bangWComult S P = Lens.id (bangW S P) :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (w : P.B a →₀ S) => by
    change Finsupp.linearCombination S id (Finsupp.single w (1 : S)) = w
    simp [Finsupp.linearCombination_single]

/-- Right counit law of the weighted exponential. -/
theorem bangWMap_counit_comult (P : PFunctor.{uA, uB}) :
    bangWMap (bangWCounit S P) ∘ₗ bangWComult S P = Lens.id (bangW S P) :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (w : P.B a →₀ S) => by
    change Finsupp.linearCombination S id
      (Finsupp.mapDomain (fun d => Finsupp.single d (1 : S)) w) = w
    rw [Finsupp.linearCombination_mapDomain]
    induction w using Finsupp.induction_linear <;> simp_all [Finsupp.linearCombination_single]

/-- Coassociativity of the comultiplication of the weighted exponential. -/
theorem bangWComult_coassoc (P : PFunctor.{uA, uB}) :
    bangWComult S (bangW S P) ∘ₗ bangWComult S P =
      bangWMap (bangWComult S P) ∘ₗ bangWComult S P :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext
    fun (www : ((P.B a →₀ S) →₀ S) →₀ S) => by
    change Finsupp.linearCombination S id (Finsupp.linearCombination S id www) =
      Finsupp.linearCombination S id (Finsupp.mapDomain (Finsupp.linearCombination S id) www)
    rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_linearCombination]
    rfl

end Lens

namespace LensCat

/-- The weighted exponential as an endofunctor of the category of lenses, for weights in the
universe of directions. -/
noncomputable def bangWFunctor (S : Type uB) [AddCommMonoid S] :
    LensCat.{uA, uB} ⥤ LensCat.{uA, uB} where
  obj X := LensCat.of (bangW S X.toPFunctor)
  map f := Lens.bangWMap f
  map_id _ := Lens.bangWMap_id
  map_comp f g := Lens.bangWMap_comp g f

/-- The weighted exponential as a comonad on the category of lenses, for weights in the universe
of directions. -/
noncomputable def bangWComonad (S : Type uB) [CommSemiring S] : Comonad LensCat.{uA, uB} where
  toFunctor := bangWFunctor S
  ε := { app X := Lens.bangWCounit S X.toPFunctor, naturality _ _ f := Lens.bangWCounit_natural f }
  δ := { app X := Lens.bangWComult S X.toPFunctor, naturality _ _ f := Lens.bangWComult_natural f }
  coassoc X := (Lens.bangWComult_coassoc X.toPFunctor).symm
  left_counit X := Lens.bangWCounit_comult X.toPFunctor
  right_counit X := Lens.bangWMap_counit_comult X.toPFunctor

end LensCat

end PFunctor
