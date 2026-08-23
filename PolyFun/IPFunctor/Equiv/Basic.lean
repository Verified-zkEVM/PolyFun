/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Chart.Basic
public import PolyFun.IPFunctor.Lens.Basic

/-!
# Structural Equivalences Between Indexed Polynomial Functors

This file defines `IPFunctor.Equiv P Q`, the structural equivalence between two indexed
polynomial functors `P Q : IPFunctor I J`: a fiberwise equivalence of `A`-types, a fiberwise
equivalence of `B`-types compatible with the `A`-equivalence, and a source-index preservation
law `src_eq`.

This is the indexed analogue of [`PFunctor.Equiv`](../../PFunctor/Equiv/Basic.lean). Like the
non-indexed version, it is strictly stronger than lens or chart equivalence.

Every structural equivalence has canonical images in the indexed lens and chart
categories, exposed by `IPFunctor.Equiv.toLensEquiv` and
`IPFunctor.Equiv.toChartEquiv`.
-/

@[expose] public section

universe uI uJ uK uL uA uA₁ uA₂ uA₃ uB uB₁ uB₂ uB₃

namespace IPFunctor

variable {I : Type uI} {J : Type uJ}

/-- A **structural equivalence** between indexed polynomial functors `P Q : IPFunctor I J`:
fiberwise type equivalences on positions and responses, plus a source-index preservation
law. -/
@[ext]
protected structure Equiv (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J)
                          (Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J) where
  /-- A fiberwise equivalence on positions. -/
  equivA : ∀ j, P.A j ≃ Q.A j
  /-- A fiberwise equivalence on responses, compatible with `equivA`. -/
  equivB : ∀ j a, P.B j a ≃ Q.B j (equivA j a)
  /-- Source-index preservation. -/
  src_eq : ∀ j a b, P.src j a b = Q.src j (equivA j a) (equivB j a b)

@[inherit_doc] scoped infixl:25 " ≃ₚ " => IPFunctor.Equiv

namespace Equiv

variable {P : IPFunctor.{uI, uJ, uA₁, uB₁} I J}
  {Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J}
  {R : IPFunctor.{uI, uJ, uA₃, uB₃} I J}

/-- The identity equivalence. -/
@[refl]
def refl (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J) : P ≃ₚ P where
  equivA _ := _root_.Equiv.refl _
  equivB _ _ := _root_.Equiv.refl _
  src_eq _ _ _ := rfl

/-- The inverse of a structural equivalence. The response side is built by
pulling `d : Q.B j a'` back through the round-trip cast and then taking the
symm of `e.equivB` at the preimage `(e.equivA j).symm a'`. Mirrors
[`PFunctor.Equiv.symm`](../../PFunctor/Equiv/Basic.lean) fiberwise, with the
extra `src_eq` discharged by applying `e.src_eq` at the preimage and
collapsing the round-trip via `Equiv.apply_symm_apply` and `cast_heq`. -/
@[symm]
def symm (e : P ≃ₚ Q) : Q ≃ₚ P where
  equivA j := (e.equivA j).symm
  equivB j a :=
    (_root_.Equiv.cast
        (congrArg (Q.B j) ((_root_.Equiv.symm_apply_eq (e.equivA j)).mp rfl))).trans
      (e.equivB j ((e.equivA j).symm a)).symm
  src_eq j a d := by
    apply Eq.symm
    simp only [_root_.Equiv.trans_apply]
    rw [e.src_eq j ((e.equivA j).symm a)
      ((e.equivB j ((e.equivA j).symm a)).symm
        (_root_.Equiv.cast
          (congrArg (Q.B j) ((_root_.Equiv.symm_apply_eq (e.equivA j)).mp rfl)) d))]
    simp only [_root_.Equiv.apply_symm_apply]
    congr 1
    · exact (e.equivA j).apply_symm_apply a
    · exact cast_heq _ d

/-- Composition of structural equivalences. Both `equivA` and `equivB` compose
diagrammatically; the `src_eq` chains by transitivity. Mirrors
[`PFunctor.Equiv.trans`](../../PFunctor/Equiv/Basic.lean) fiberwise. -/
@[trans]
def trans (e₁ : P ≃ₚ Q) (e₂ : Q ≃ₚ R) : P ≃ₚ R where
  equivA j := (e₁.equivA j).trans (e₂.equivA j)
  equivB j a := (e₁.equivB j a).trans (e₂.equivB j (e₁.equivA j a))
  src_eq j a b :=
    (e₁.src_eq j a b).trans (e₂.src_eq j (e₁.equivA j a) (e₁.equivB j a b))

/-! ## Lens and chart equivalences -/

private theorem lens_ext (l₁ l₂ : Lens P Q)
    (hA : ∀ j a, l₁.toFunA j a = l₂.toFunA j a)
    (hB : ∀ j a, l₁.toFunB j a = (hA j a) ▸ l₂.toFunB j a) : l₁ = l₂ := by
  rcases l₁ with ⟨toFunA₁, toFunB₁, src_eq₁⟩
  rcases l₂ with ⟨toFunA₂, toFunB₂, src_eq₂⟩
  have h : toFunA₁ = toFunA₂ := funext fun j => funext (hA j)
  subst h
  have h' : toFunB₁ = toFunB₂ := by
    funext j a
    simpa using hB j a
  subst h'
  rfl

private theorem chart_ext (c₁ c₂ : Chart P Q)
    (hA : ∀ j a, c₁.toFunA j a = c₂.toFunA j a)
    (hB : ∀ j a, c₁.toFunB j a = (hA j a) ▸ c₂.toFunB j a) : c₁ = c₂ := by
  rcases c₁ with ⟨toFunA₁, toFunB₁, src_eq₁⟩
  rcases c₂ with ⟨toFunA₂, toFunB₂, src_eq₂⟩
  have h : toFunA₁ = toFunA₂ := funext fun j => funext (hA j)
  subst h
  have h' : toFunB₁ = toFunB₂ := by
    funext j a
    simpa using hB j a
  subst h'
  rfl

/-- The lens underlying a structural equivalence. Positions move forward through
`equivA`, while responses pull back through the inverse of `equivB`. -/
def toLens (e : P ≃ₚ Q) : Lens P Q where
  toFunA j := e.equivA j
  toFunB j a := (e.equivB j a).symm
  src_eq j a d := by
    simpa only [_root_.Equiv.apply_symm_apply] using
      e.src_eq j a ((e.equivB j a).symm d)

@[simp]
theorem toLens_toFunA (e : P ≃ₚ Q) (j : J) (a : P.A j) :
    e.toLens.toFunA j a = e.equivA j a := rfl

@[simp]
theorem toLens_toFunB (e : P ≃ₚ Q) (j : J) (a : P.A j)
    (d : Q.B j (e.equivA j a)) :
    e.toLens.toFunB j a d = (e.equivB j a).symm d := rfl

@[simp]
theorem toLens_refl (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J) :
    (refl P).toLens = Lens.id P := rfl

@[simp]
theorem toLens_trans (e₁ : P ≃ₚ Q) (e₂ : Q ≃ₚ R) :
    (e₁.trans e₂).toLens = Lens.comp e₂.toLens e₁.toLens := rfl

private theorem equivB_symm_apply_of_eq (e : P ≃ₚ Q) (j : J)
    {a a' : P.A j} (ha : e.equivA j a = e.equivA j a') (b : P.B j a') :
    (e.equivB j a).symm
        ((_root_.Equiv.cast (congrArg (Q.B j) ha)).symm ((e.equivB j a') b)) =
      _root_.cast (congrArg (P.B j) ((e.equivA j).injective ha).symm) b := by
  have ha' : a = a' := (e.equivA j).injective ha
  cases ha'
  simp

private theorem equivB_symm_apply (e : P ≃ₚ Q) (j : J) (a : P.A j)
    (b : P.B j ((e.equivA j).symm (e.equivA j a))) :
    (e.equivB j a).symm ((e.symm.equivB j (e.equivA j a)).symm b) =
      _root_.cast (congrArg (P.B j) ((e.equivA j).symm_apply_apply a)) b := by
  have hEqA :
      e.equivA j a = e.equivA j ((e.equivA j).symm (e.equivA j a)) := by
    simp
  simp only [IPFunctor.Equiv.symm]
  exact equivB_symm_apply_of_eq (e := e) (j := j)
    (a := a) (a' := (e.equivA j).symm (e.equivA j a))
    (ha := hEqA) (b := b)

private theorem symm_equivB_symm_apply (e : P ≃ₚ Q) (j : J) (a : Q.A j)
    (b : Q.B j (e.equivA j ((e.equivA j).symm a))) :
    (e.symm.equivB j a).symm ((e.equivB j ((e.equivA j).symm a)).symm b) =
      _root_.cast (congrArg (Q.B j) ((e.equivA j).apply_symm_apply a)) b := by
  change
    ((_root_.Equiv.cast
      (congrArg (Q.B j) ((_root_.Equiv.symm_apply_eq (e.equivA j)).mp rfl))).symm
      ((e.equivB j ((e.equivA j).symm a))
        ((e.equivB j ((e.equivA j).symm a)).symm b))) = _
  rw [_root_.Equiv.apply_symm_apply (e.equivB j ((e.equivA j).symm a)) b]
  change
    _root_.cast
        (congrArg (Q.B j) ((_root_.Equiv.symm_apply_eq (e.equivA j)).mp rfl)).symm b =
      _root_.cast (congrArg (Q.B j) ((e.equivA j).apply_symm_apply a)) b
  simp

private theorem eqRec_id_apply {A : Sort*} {B : A → Sort*}
    {a₁ a₀ : A} (h : a₁ = a₀) (x : B a₀) :
    Eq.rec (motive := fun a _ => B a → B a₁) id h x =
      _root_.cast (congrArg B h).symm x := by
  cases h
  rfl

/-- Pulling responses back through a structural equivalence and its inverse
is the identity indexed lens. -/
@[simp]
theorem symm_toLens_comp_toLens (e : P ≃ₚ Q) :
    Lens.comp e.symm.toLens e.toLens = Lens.id P := by
  refine lens_ext _ _ (fun j a => by
    change (e.symm.equivA j) (e.equivA j a) = a
    exact (e.equivA j).symm_apply_apply a) ?_
  intro j a
  funext b
  simp only [Lens.comp, Lens.id, toLens, Function.comp_apply, id_eq]
  have hb := equivB_symm_apply (e := e) (j := j) (a := a) (b := b)
  have h₀ : a = (e.equivA j).symm (e.equivA j a) :=
    ((e.equivA j).symm_apply_apply a).symm
  have hr := eqRec_id_apply (B := P.B j) (h := h₀) (x := b)
  exact hb.trans hr.symm

/-- Pulling responses back through the inverse and then the original structural
equivalence is the identity indexed lens. -/
@[simp]
theorem toLens_comp_symm_toLens (e : P ≃ₚ Q) :
    Lens.comp e.toLens e.symm.toLens = Lens.id Q := by
  refine lens_ext _ _ (fun j a => by
    change (e.equivA j) (e.symm.equivA j a) = a
    exact (e.equivA j).apply_symm_apply a) ?_
  intro j a
  funext b
  simp only [Lens.comp, Lens.id, toLens, Function.comp_apply, id_eq]
  have hb := symm_equivB_symm_apply (e := e) (j := j) (a := a) (b := b)
  have h₀ : a = e.equivA j ((e.equivA j).symm a) :=
    ((_root_.Equiv.symm_apply_eq (e.equivA j)).mp rfl)
  have hr := eqRec_id_apply (B := Q.B j) (h := h₀) (x := b)
  exact hb.trans hr.symm

/-- Convert a structural equivalence to an isomorphism in the indexed lens
category. -/
def toLensEquiv (e : P ≃ₚ Q) : Lens.Equiv P Q where
  toLens := e.toLens
  invLens := e.symm.toLens
  left_inv := symm_toLens_comp_toLens e
  right_inv := toLens_comp_symm_toLens e

@[simp]
theorem toLensEquiv_toLens (e : P ≃ₚ Q) : e.toLensEquiv.toLens = e.toLens := rfl

@[simp]
theorem toLensEquiv_invLens (e : P ≃ₚ Q) : e.toLensEquiv.invLens = e.symm.toLens := rfl

/-- The chart underlying a structural equivalence. Both positions and
responses move forward through their fiberwise equivalences. -/
def toChart (e : P ≃ₚ Q) : Chart P Q where
  toFunA j := e.equivA j
  toFunB j a := e.equivB j a
  src_eq j a b := (e.src_eq j a b).symm

@[simp]
theorem toChart_toFunA (e : P ≃ₚ Q) (j : J) (a : P.A j) :
    e.toChart.toFunA j a = e.equivA j a := rfl

@[simp]
theorem toChart_toFunB (e : P ≃ₚ Q) (j : J) (a : P.A j) (b : P.B j a) :
    e.toChart.toFunB j a b = e.equivB j a b := rfl

@[simp]
theorem toChart_refl (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J) :
    (refl P).toChart = Chart.id P := rfl

@[simp]
theorem toChart_trans (e₁ : P ≃ₚ Q) (e₂ : Q ≃ₚ R) :
    (e₁.trans e₂).toChart = Chart.comp e₂.toChart e₁.toChart := rfl

private theorem forward_equivB_roundtrip (e : P ≃ₚ Q) (j : J) (a : P.A j)
    (b : P.B j a) :
    e.symm.equivB j (e.equivA j a) (e.equivB j a b) =
      _root_.cast
        (congrArg (P.B j) ((e.equivA j).symm_apply_apply a).symm) b := by
  change
    (((_root_.Equiv.cast _).trans
      (e.equivB j ((e.equivA j).symm (e.equivA j a))).symm) (e.equivB j a b)) = _
  simp only [_root_.Equiv.trans_apply]
  exact equivB_symm_apply_of_eq e j
    (a := (e.equivA j).symm (e.equivA j a)) (a' := a)
    (ha := (e.equivA j).apply_symm_apply _) (b := b)

private theorem reverse_equivB_roundtrip (e : P ≃ₚ Q) (j : J) (a : Q.A j)
    (b : Q.B j a) :
    e.equivB j ((e.equivA j).symm a) (e.symm.equivB j a b) =
      _root_.cast
        (congrArg (Q.B j) ((e.equivA j).apply_symm_apply a).symm) b := by
  change
    (e.equivB j ((e.equivA j).symm a))
      (((_root_.Equiv.cast _).trans
        (e.equivB j ((e.equivA j).symm a)).symm) b) = _
  simp [_root_.Equiv.trans_apply]

private theorem eqRec_id_apply_codomain
    {A : Sort*} {B : A → Sort*} {a₀ a₁ : A}
    (h : a₀ = a₁) (x : B a₀) :
    Eq.rec (motive := fun a _ => B a₀ → B a) id h x =
      _root_.cast (congrArg B h) x := by
  subst h
  rfl

/-- Pushing responses forward through a structural equivalence and its inverse
is the identity indexed chart. -/
@[simp]
theorem symm_toChart_comp_toChart (e : P ≃ₚ Q) :
    Chart.comp e.symm.toChart e.toChart = Chart.id P := by
  refine chart_ext _ _ (fun j a => by
    change (e.symm.equivA j) (e.equivA j a) = a
    exact (e.equivA j).symm_apply_apply a) ?_
  intro j a
  funext b
  simp only [Chart.comp, Chart.id, toChart, Function.comp_apply]
  rw [forward_equivB_roundtrip]
  exact (eqRec_id_apply_codomain ((e.equivA j).symm_apply_apply a).symm b).symm

/-- Pushing responses forward through the inverse and then the original
structural equivalence is the identity indexed chart. -/
@[simp]
theorem toChart_comp_symm_toChart (e : P ≃ₚ Q) :
    Chart.comp e.toChart e.symm.toChart = Chart.id Q := by
  refine chart_ext _ _ (fun j a => by
    change (e.equivA j) (e.symm.equivA j a) = a
    exact (e.equivA j).apply_symm_apply a) ?_
  intro j a
  funext b
  simp only [Chart.comp, Chart.id, toChart, Function.comp_apply]
  change e.equivB j ((e.equivA j).symm a) (e.symm.equivB j a b) = _
  rw [reverse_equivB_roundtrip]
  exact (eqRec_id_apply_codomain ((e.equivA j).apply_symm_apply a).symm b).symm

/-- Convert a structural equivalence to an isomorphism in the indexed chart
category. -/
def toChartEquiv (e : P ≃ₚ Q) : Chart.Equiv P Q where
  toChart := e.toChart
  invChart := e.symm.toChart
  left_inv := symm_toChart_comp_toChart e
  right_inv := toChart_comp_symm_toChart e

@[simp]
theorem toChartEquiv_toChart (e : P ≃ₚ Q) : e.toChartEquiv.toChart = e.toChart := rfl

@[simp]
theorem toChartEquiv_invChart (e : P ≃ₚ Q) :
    e.toChartEquiv.invChart = e.symm.toChart := rfl

end Equiv

/-! ## Composition laws

`IPFunctor.X` (defined in `IPFunctor.Basic`) is the categorical identity for `IPFunctor.comp`
on `IPFunctor.Endo I`. Like the non-indexed `PFunctor` story, the left/right identity and
associativity laws hold up to `IPFunctor.Equiv` (i.e. `≃ₚ`) rather than definitional
equality, because the comp construction reshuffles Σ/Π factors. The extra `src_eq`
obligation closes by `rfl` in each case, since `X.src i _ _ = i` and the position /
response equivalences are direct projections. -/

section CompIdentity

variable (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J)

/-- `P ◃ X ≃ₚ P`: right identity for indexed composition. The right argument `X` is on
`IPFunctor.Endo I` (so its index matches `P`'s input). -/
def compX : P ◃ X ≃ₚ P where
  equivA j := _root_.Equiv.sigmaUnique (P.A j) (fun a => P.B j a → PUnit.{uA₁ + 1})
  equivB _ _ := _root_.Equiv.sigmaPUnit _
  src_eq _ _ _ := rfl

/-- `X ◃ P ≃ₚ P`: left identity for indexed composition. The left argument `X` is on
`IPFunctor.Endo J` (so its index matches `P`'s output). -/
def XComp : X ◃ P ≃ₚ P where
  equivA j :=
    (_root_.Equiv.uniqueSigma (fun _ : PUnit.{uA₁ + 1} => PUnit.{uA₁ + 1} → P.A j)).trans
      (_root_.Equiv.punitArrowEquiv (P.A j))
  equivB _ _ := _root_.Equiv.uniqueSigma _
  src_eq _ _ _ := rfl

end CompIdentity

section CompAssoc

variable {K : Type uK} {L : Type uL}
  (P : IPFunctor.{uK, uL, uA₁, uB₁} K L)
  (Q : IPFunctor.{uJ, uK, uA₂, uB₂} J K)
  (R : IPFunctor.{uI, uJ, uA₃, uB₃} I J)

/-- Associativity of indexed composition, up to `IPFunctor.Equiv`. With `R` innermost
(input index `I`), `Q` in the middle, and `P` outermost (output index `L`), the two
parenthesizations `(P ◃ Q) ◃ R` and `P ◃ (Q ◃ R)` are equivalent. -/
def compAssoc : (P ◃ Q) ◃ R ≃ₚ P ◃ (Q ◃ R) where
  equivA _ := {
    toFun := fun ⟨⟨pa, qf⟩, rf⟩ => ⟨pa, fun pb => ⟨qf pb, fun qb => rf ⟨pb, qb⟩⟩⟩
    invFun := fun ⟨pa, g⟩ => ⟨⟨pa, fun pb => (g pb).1⟩, fun ⟨pb, qb⟩ => (g pb).2 qb⟩
    left_inv := by rintro ⟨⟨pa, qf⟩, rf⟩; rfl
    right_inv := by rintro ⟨pa, g⟩; rfl
  }
  equivB l := fun ⟨⟨pa, qf⟩, rf⟩ =>
    _root_.Equiv.sigmaAssoc
      (fun pb qb => R.B (Q.src (P.src l pa pb) (qf pb) qb) (rf ⟨pb, qb⟩))
  src_eq _ _ _ := rfl

end CompAssoc

end IPFunctor
