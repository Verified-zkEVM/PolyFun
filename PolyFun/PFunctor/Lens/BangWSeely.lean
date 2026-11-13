/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Lens.Bang
public import PolyFun.PFunctor.Lens.BangW
public import Mathlib.Data.Finsupp.Multiset

/-!
# Weakening, contraction and the Seely isomorphisms for the weighted exponential

For a commutative semiring `S`, the weighted exponential `bangW S P` is a commutative comonoid for
the parallel product `⊗`: weakening demands the zero weighting and contraction demands the sum of
two weightings. The functor `bangW S` sends the categorical product `*` to the parallel product and
the terminal object `1` to the unit `y`; these are the Seely isomorphisms, and contraction is the
Seely image of the weighted exponential of the diagonal.

At `S = ℕ` the weighted exponential is the multiset exponential `bang`: a multiset is the
weighting that counts its elements (`Multiset.toFinsupp`). The lens equivalence
`bang P ≃ₗ bangW ℕ P` is natural in `P` and carries the counit, the comultiplication, weakening
and contraction of `bang` to those of `bangW ℕ`. The multiset exponential stays the computable
form; the weighted one at `ℕ` is related to it by this equivalence.

The comonoid instances on `TensorCat.of (bangW S P)` require `S` in the universe of directions of
`P`, as `LensCat.bangWComonad` does; the lens-level laws hold for every universe of `S`.

## Main definitions

* `Lens.bangWWeak`, `Lens.bangWContr` — weakening and contraction;
* `Lens.Equiv.seelyW`, `Lens.Equiv.seelyWUnit` — the Seely isomorphisms
  `bangW S (P * Q) ≃ₗ bangW S P ⊗ bangW S Q` and `bangW S 1 ≃ₗ y`;
* `Lens.Equiv.bangEquivBangW` — the equivalence `bang P ≃ₗ bangW ℕ P`.

## Main results

* `Lens.bangWContr_weak_left`, `Lens.bangWContr_weak_right`, `Lens.bangWContr_assoc`,
  `Lens.bangWContr_comm` and the instances `ComonObj`, `IsCommComonObj` on
  `TensorCat.of (bangW S P)` — the commutative comonoid;
* `Lens.bangWWeak_natural`, `Lens.bangWContr_natural`, `Lens.Equiv.seelyW_natural` — naturality;
* `Lens.Equiv.seelyW_contr` — contraction is the Seely image of the exponential of the diagonal;
* `Lens.Equiv.bangEquivBangW_natural`, `Lens.Equiv.bangEquivBangW_counit`,
  `Lens.Equiv.bangEquivBangW_comult`, `Lens.Equiv.bangEquivBangW_weak`,
  `Lens.Equiv.bangEquivBangW_contr` — the comparison with `bang`.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ w

open CategoryTheory

namespace PFunctor

variable {S : Type w} [CommSemiring S]

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

/-! ## Weakening and contraction -/

variable (S) in
/-- Weakening of the weighted exponential: the zero weighting is demanded. -/
noncomputable def bangWWeak (P : PFunctor.{uA, uB}) : Lens (bangW S P) y.{uA, max uB w} :=
  (fun _ => PUnit.unit) ⇆ fun _ _ => 0

variable (S) in
/-- Contraction of the weighted exponential: a position is duplicated, and a pair of weightings
demands their sum. -/
noncomputable def bangWContr (P : PFunctor.{uA, uB}) :
    Lens (bangW S P) (bangW S P ⊗ bangW S P) :=
  (fun a => (a, a)) ⇆ fun _ m => m.1 + m.2

/-- Weakening on the left after contraction is the inverse of the left unitor. -/
theorem bangWContr_weak_left (P : PFunctor.{uA, uB}) :
    (bangWWeak S P ⊗ₗ Lens.id (bangW S P)) ∘ₗ bangWContr S P = Lens.Equiv.yTensor.invLens :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => zero_add m.2

/-- Weakening on the right after contraction is the inverse of the right unitor. -/
theorem bangWContr_weak_right (P : PFunctor.{uA, uB}) :
    (Lens.id (bangW S P) ⊗ₗ bangWWeak S P) ∘ₗ bangWContr S P = Lens.Equiv.tensorY.invLens :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => add_zero m.1

/-- Contraction of the weighted exponential is coassociative. -/
theorem bangWContr_assoc (P : PFunctor.{uA, uB}) :
    (Lens.id (bangW S P) ⊗ₗ bangWContr S P) ∘ₗ bangWContr S P =
      Lens.comp (Lens.comp Lens.Equiv.tensorAssoc.toLens
        (bangWContr S P ⊗ₗ Lens.id (bangW S P))) (bangWContr S P) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => (add_assoc _ _ _).symm

/-- Contraction of the weighted exponential is cocommutative. -/
theorem bangWContr_comm (P : PFunctor.{uA, uB}) :
    (Lens.Equiv.tensorComm (bangW S P) (bangW S P)).toLens ∘ₗ bangWContr S P = bangWContr S P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => add_comm _ _

/-- Weakening is natural. -/
theorem bangWWeak_natural {P Q : PFunctor.{uA, uB}} (l : Lens P Q) :
    bangWWeak S Q ∘ₗ bangWMap l = bangWWeak S P :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun _ => Finsupp.mapDomain_zero (f := l.toFunB a)

/-- Contraction is natural. -/
theorem bangWContr_natural (l : Lens P Q) :
    bangWContr S Q ∘ₗ bangWMap l = (bangWMap l ⊗ₗ bangWMap l) ∘ₗ bangWContr S P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Finsupp.mapDomain_add

end Lens

/-! ## The Seely isomorphisms -/

namespace Lens.Equiv

variable (S) in
/-- The Seely isomorphism of the weighted exponential: the weighted exponential of a categorical
product is the parallel product of the weighted exponentials. -/
noncomputable def seelyW (P Q : PFunctor.{uA, uB}) : bangW S (P * Q) ≃ₗ bangW S P ⊗ bangW S Q where
  toLens := id ⇆ fun _ st => Finsupp.sumFinsuppEquivProdFinsupp.symm st
  invLens := id ⇆ fun _ m => Finsupp.sumFinsuppEquivProdFinsupp m
  left_inv := Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m =>
    Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply m
  right_inv := Lens.ext _ _ (fun _ => rfl) fun _ => funext fun st =>
    Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply st

variable (S) in
/-- The Seely isomorphism of the weighted exponential at the unit: the weighted exponential of the
terminal object is the unit of the parallel product. -/
noncomputable def seelyWUnit : bangW S (1 : PFunctor.{uA, uB}) ≃ₗ y.{uA, max uB w} where
  toLens := (fun _ => PUnit.unit) ⇆ fun _ _ => 0
  invLens := (fun _ => PUnit.unit) ⇆ fun _ _ => PUnit.unit
  left_inv := Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ =>
    Finsupp.ext fun x => PEmpty.elim x
  right_inv := rfl

/-- The Seely isomorphism is natural in both factors. -/
theorem seelyW_natural {P P' Q Q' : PFunctor.{uA, uB}} (l : Lens P P') (m : Lens Q Q') :
    (bangWMap l ⊗ₗ bangWMap m) ∘ₗ (seelyW S P Q).toLens =
      (seelyW S P' Q').toLens ∘ₗ bangWMap (l ×ₗ m) :=
  Lens.ext _ _ (fun _ => rfl) fun ab => funext
    fun (st : (P'.B (l.toFunA ab.1) →₀ S) × (Q'.B (m.toFunA ab.2) →₀ S)) => by
    change Finsupp.sumElim (Finsupp.mapDomain (l.toFunB ab.1) st.1)
        (Finsupp.mapDomain (m.toFunB ab.2) st.2) =
      Finsupp.mapDomain (Sum.elim (Sum.inl ∘ l.toFunB ab.1) (Sum.inr ∘ m.toFunB ab.2))
        (Finsupp.sumElim st.1 st.2)
    rw [Finsupp.sumElim_eq_add, Finsupp.sumElim_eq_add, Finsupp.mapDomain_add,
      ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp,
      ← Finsupp.mapDomain_comp]
    rfl

/-- Contraction is the Seely image of the weighted exponential of the diagonal. -/
theorem seelyW_contr (P : PFunctor.{uA, uB}) :
    (seelyW S P P).toLens ∘ₗ Lens.bangWMap (Lens.prodPair (Lens.id P) (Lens.id P)) =
      Lens.bangWContr S P :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (m : (P.B a →₀ S) × (P.B a →₀ S)) => by
    change Finsupp.mapDomain (Sum.elim id id) (Finsupp.sumElim m.1 m.2) = m.1 + m.2
    rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp,
      ← Finsupp.mapDomain_comp]
    simp [Function.comp_def]

/-! ## The multiset exponential as the weighted exponential at `ℕ` -/

open Classical in
/-- The multiset exponential is the weighted exponential at `ℕ`: a multiset is the weighting that
counts its elements. -/
noncomputable def bangEquivBangW (P : PFunctor.{uA, uB}) : bang P ≃ₗ bangW ℕ P where
  toLens := id ⇆ fun _ f => Finsupp.toMultiset f
  invLens := id ⇆ fun _ m => Multiset.toFinsupp m
  left_inv := Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m =>
    Multiset.toFinsupp_toMultiset m
  right_inv := Lens.ext _ _ (fun _ => rfl) fun _ => funext fun f =>
    Finsupp.toMultiset_toFinsupp f

/-- The comparison of the multiset and the weighted exponential is natural. -/
theorem bangEquivBangW_natural {P Q : PFunctor.{uA, uB}} (l : Lens P Q) :
    bangWMap l ∘ₗ (bangEquivBangW P).toLens = (bangEquivBangW Q).toLens ∘ₗ bangMap l :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun f => (Finsupp.toMultiset_map f (l.toFunB a)).symm

/-- The comparison carries the counit of `bang` to the counit of `bangW ℕ`. -/
theorem bangEquivBangW_counit (P : PFunctor.{uA, uB}) :
    bangWCounit ℕ P ∘ₗ (bangEquivBangW P).toLens = bangCounit P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun d =>
    (Finsupp.toMultiset_single d 1).trans (one_nsmul _)

/-- The comparison carries the comultiplication of `bang` to the comultiplication of
`bangW ℕ`. -/
theorem bangEquivBangW_comult (P : PFunctor.{uA, uB}) :
    bangWComult ℕ P ∘ₗ (bangEquivBangW P).toLens =
      Lens.comp (Lens.comp (bangWMap (bangEquivBangW P).toLens) (bangEquivBangW (bang P)).toLens)
        (bangComult P) :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (ww : (P.B a →₀ ℕ) →₀ ℕ) => by
    change Finsupp.toMultiset (Finsupp.linearCombination ℕ id ww) =
      Multiset.join (Finsupp.toMultiset (Finsupp.mapDomain Finsupp.toMultiset ww))
    induction ww using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp_all [Finsupp.mapDomain_add]
    | single f n =>
      simp only [Finsupp.linearCombination_single, Finsupp.mapDomain_single,
        Finsupp.toMultiset_single, map_nsmul]
      induction n with
      | zero => simp
      | succ n ih => simp_all [succ_nsmul, Multiset.join_add]

/-- The comparison carries weakening of `bang` to weakening of `bangW ℕ`. -/
theorem bangEquivBangW_weak (P : PFunctor.{uA, uB}) :
    bangWWeak ℕ P ∘ₗ (bangEquivBangW P).toLens = bangWeak P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => map_zero Finsupp.toMultiset

/-- The comparison carries contraction of `bang` to contraction of `bangW ℕ`. -/
theorem bangEquivBangW_contr (P : PFunctor.{uA, uB}) :
    bangWContr ℕ P ∘ₗ (bangEquivBangW P).toLens =
      ((bangEquivBangW P).toLens ⊗ₗ (bangEquivBangW P).toLens) ∘ₗ bangContr P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => map_add Finsupp.toMultiset m.1 m.2

end Lens.Equiv

/-! ## The commutative comonoid structure -/

namespace TensorCat

/-- `bangW S P` is a comonoid for the parallel product, by weakening and contraction. -/
noncomputable instance instComonObjBangW (S : Type uB) [CommSemiring S]
    (P : PFunctor.{uA, uB}) : ComonObj (TensorCat.of.{uA, uB} (bangW S P)) where
  counit := Lens.bangWWeak S P
  comul := Lens.bangWContr S P
  counit_comul := Lens.bangWContr_weak_left P
  comul_counit := Lens.bangWContr_weak_right P
  comul_assoc := Lens.bangWContr_assoc P

/-- The comonoid `bangW S P` is commutative. -/
instance instIsCommComonObjBangW (S : Type uB) [CommSemiring S] (P : PFunctor.{uA, uB}) :
    IsCommComonObj (TensorCat.of.{uA, uB} (bangW S P)) where
  comul_comm := Lens.bangWContr_comm (S := S) P

end TensorCat

end PFunctor
