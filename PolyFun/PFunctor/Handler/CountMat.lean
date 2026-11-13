/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Handler.CertifiedVec
public import PolyFun.PFunctor.Lens.BangLE

/-!
# Handlers certified by count matrices

A one-shape Diller–Nahm morphism is a lens `bang (y^ι') ⇆ y^ι` out of the exponential of a
polynomial with one position. Its backward map sends each `i : ι` to a finite multiset over `ι'`,
and at finite `ι'` it is determined by its count matrix `ι → ι' → ℕ` (`Lens.ofCountMat`,
`Lens.countMat_ofCountMat`, `Lens.ofCountMat_countMat`). Read with `ι` the resources of an
interface `P` and `ι'` the resources of an interface `Q`, the entry at `(i, j)` is the number of
units of `j` that one unit of `i` demands: the demands `d` of `Handler.Certified.ofDemand`, at
natural-number values.

A handler `P → FreeM Q` certified by such a morphism (`Handler.CountCertified`) is a certified
handler whose exchange is the demand map of the cast count matrix (`CountCertified.toCertified`),
which is the vector–matrix product (`CountCertified.toCertified_exchange_apply`). The lens points
from the resources of `Q` to those of `P`: the assignment is contravariant. The identity handler
is certified by the counit (`CountCertified.id`), and handlers compose with the co-Kleisli
composite of their lenses in the opposite order (`CountCertified.comp`). The assignment
`toCertified` preserves identities and composition (`CountCertified.toCertified_id`,
`CountCertified.toCertified_comp`): the composition of exchanges of `Handler.Certified.comp` at
demand maps is the product of count matrices of `Lens.countMat_bangComp`
(`Lens.demand_bangComp`). A program with use vector `u` runs through a composite with use vector
`u` times the product of the two count matrices (`CountCertified.isChargeBound_liftM_comp`).

The correspondence covers demand maps with natural-number entries, which are the count matrices
of one-shape morphisms (`CountCertified.ofNatDemand`). A demand map with entries outside the image
of `ℕ`, such as an expected demand in `ℝ≥0` or an unbounded demand `⊤` in `ℕ∞`, is not a count
matrix, and a certified handler whose exchange is not a demand map has no count matrix at all.
-/

@[expose] public section

universe uA uA₂ uA₃ uB uB₂ uB₃ u u' u'' w

open scoped BigOperators

namespace PFunctor

namespace Lens

variable {ι : Type u} {ι' : Type u'} {ι'' : Type u''}

/-! ## One-shape Diller–Nahm morphisms and their count matrices -/

/-- The one-shape Diller–Nahm morphism with count matrix `d`: the direction `i` demands each
direction `j` with multiplicity `d i j`. -/
def ofCountMat [Fintype ι'] (d : ι → ι' → ℕ) :
    Lens (bang (y^ι' : PFunctor.{0, u'})) (y^ι : PFunctor.{0, u}) :=
  (fun _ => PUnit.unit) ⇆ fun _ i => ∑ j, Multiset.replicate (d i j) j

/-- The count matrix of `ofCountMat d` is `d`. -/
@[simp]
theorem countMat_ofCountMat [Fintype ι'] [DecidableEq ι'] (d : ι → ι' → ℕ) :
    (ofCountMat d).countMat PUnit.unit = Matrix.of d := by
  ext i j
  simp [countMat, ofCountMat, Multiset.count_sum', Multiset.count_replicate]

/-- A one-shape Diller–Nahm morphism is the morphism of its count matrix. -/
theorem ofCountMat_countMat [Fintype ι'] [DecidableEq ι']
    (g : Lens (bang (y^ι' : PFunctor.{0, u'})) (y^ι : PFunctor.{0, u})) :
    ofCountMat (fun i j => g.countMat PUnit.unit i j) = g := by
  obtain ⟨fA, fB⟩ := g
  have hA : fA = fun _ => PUnit.unit := funext fun _ => rfl
  subst hA
  simp only [ofCountMat]
  congr 1
  funext a i
  cases a
  ext j
  simp [countMat, Multiset.count_sum', Multiset.count_replicate]

/-- The demand matrix of a one-shape Diller–Nahm morphism: its count matrix, cast to `ω`. -/
def demand (ω : Type w) [NatCast ω] [DecidableEq ι']
    (g : Lens (bang (y^ι' : PFunctor.{0, u'})) (y^ι : PFunctor.{0, u})) : ι → ι' → ω :=
  fun i j => (g.countMat PUnit.unit i j : ω)

variable {ω : Type w} [CommSemiring ω] [PartialOrder ω] [IsOrderedRing ω]

/-- Demand matrices are nonnegative. -/
theorem demand_nonneg [DecidableEq ι']
    (g : Lens (bang (y^ι' : PFunctor.{0, u'})) (y^ι : PFunctor.{0, u})) : 0 ≤ g.demand ω :=
  fun _ _ => Nat.cast_nonneg' _

/-- The demand map of a demand matrix is the vector–matrix product. -/
theorem demandHom_demand [Fintype ι] [DecidableEq ι']
    (g : Lens (bang (y^ι' : PFunctor.{0, u'})) (y^ι : PFunctor.{0, u})) (u : ι → ω) :
    demandHom (g.demand ω) g.demand_nonneg u = Matrix.vecMul u (Matrix.of (g.demand ω)) := by
  funext j
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

omit [PartialOrder ω] [IsOrderedRing ω] in
/-- The demand matrix of the counit is the identity matrix. -/
theorem demand_bangCounit [DecidableEq ι] :
    (bangCounit (y^ι : PFunctor.{0, u})).demand ω = fun i => Pi.single i 1 := by
  funext i j
  simp [demand, countMat_bangCounit, Matrix.one_apply, Pi.single_apply, eq_comm]

omit [PartialOrder ω] [IsOrderedRing ω] in
/-- **Composition agrees.** The demand matrix of a co-Kleisli composite is the product of the
demand matrices. -/
theorem demand_bangComp_eq_mul [Fintype ι'] [DecidableEq ι'] [DecidableEq ι'']
    (g : Lens (bang (y^ι' : PFunctor.{0, u'})) (y^ι : PFunctor.{0, u}))
    (f : Lens (bang (y^ι'' : PFunctor.{0, u''})) (y^ι' : PFunctor.{0, u'})) :
    Matrix.of ((bangComp g f).demand ω) = Matrix.of (g.demand ω) * Matrix.of (f.demand ω) := by
  ext i k
  simp [demand, countMat_bangComp, Matrix.mul_apply]

/-- The demand matrix of a co-Kleisli composite is the composite demand of
`Handler.isChargeBound_liftM_demand_comp`: the demand map of `f` applied to each row of `g`. -/
theorem demand_bangComp [Fintype ι'] [DecidableEq ι'] [DecidableEq ι'']
    (g : Lens (bang (y^ι' : PFunctor.{0, u'})) (y^ι : PFunctor.{0, u}))
    (f : Lens (bang (y^ι'' : PFunctor.{0, u''})) (y^ι' : PFunctor.{0, u'})) :
    (bangComp g f).demand ω = fun i => demandHom (f.demand ω) f.demand_nonneg (g.demand ω i) := by
  funext i k
  have h := congrFun (congrFun (demand_bangComp_eq_mul (ω := ω) g f) i) k
  simp only [Matrix.of_apply] at h
  rw [h]
  simp [Matrix.mul_apply, Finset.sum_apply]

end Lens

/-! ## Handlers certified by count matrices -/

namespace Handler

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {ι : Type u} {ι' : Type u'} {ι'' : Type u''} [Fintype ι] [DecidableEq ι']
  {ω : Type w} [CommSemiring ω] [PartialOrder ω] [IsOrderedRing ω]

/-- A handler implementing `P` by programs over `Q`, certified by a one-shape Diller–Nahm morphism
from the resources `ι'` of `Q` to the resources `ι` of `P`: each call at `a` is implemented with
use vector at most `∑ i, c a i • lens.demand ω i`. -/
structure CountCertified (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂}) (c : P.A → ι → ω)
    (e : Q.A → ι' → ω) where
  /-- The implementation of each call. -/
  handler : Handler (FreeM Q) P
  /-- The demand of one unit of each resource of `P` in resources of `Q`. -/
  lens : Lens (bang (y^ι' : PFunctor.{0, u'})) (y^ι : PFunctor.{0, u})
  /-- Each call is implemented within its demand. -/
  certificate : ∀ a, (handler a).IsChargeBound e (∑ i, c a i • lens.demand ω i)

namespace CountCertified

variable {c : P.A → ι → ω} {e : Q.A → ι' → ω}

/-- The certified handler with the demand map of the count matrix as its exchange. -/
def toCertified (D : CountCertified P Q c e) : Certified P Q c e :=
  Certified.ofDemand D.handler (D.lens.demand ω) D.lens.demand_nonneg D.certificate

@[simp]
theorem toCertified_handler (D : CountCertified P Q c e) : D.toCertified.handler = D.handler :=
  rfl

/-- The exchange of a handler certified by a count matrix is the vector–matrix product. -/
theorem toCertified_exchange_apply (D : CountCertified P Q c e) (u : ι → ω) :
    D.toCertified.exchange u = Matrix.vecMul u (Matrix.of (D.lens.demand ω)) :=
  D.lens.demandHom_demand u

/-- **Use bounds through a handler certified by a count matrix.** A program with use vector `u`
runs with use vector `u` times the demand matrix. -/
theorem isChargeBound_liftM (D : CountCertified P Q c e) {α : Type uB} {x : FreeM P α}
    {u : ι → ω} (hx : x.IsChargeBound c u) :
    (x.liftM D.handler).IsChargeBound e (Matrix.vecMul u (Matrix.of (D.lens.demand ω))) := by
  rw [← D.lens.demandHom_demand u]
  exact Handler.isChargeBound_liftM_demand D.lens.demand_nonneg D.certificate hx

/-- A handler certified by a demand map with natural-number entries, certified by the one-shape
Diller–Nahm morphism of that matrix. -/
def ofNatDemand [Fintype ι'] (h : Handler (FreeM Q) P) (d : ι → ι' → ℕ)
    (hh : ∀ a, (h a).IsChargeBound e (∑ i, c a i • fun j => (d i j : ω))) :
    CountCertified P Q c e where
  handler := h
  lens := Lens.ofCountMat d
  certificate a := by
    have : (Lens.ofCountMat d).demand ω = fun i j => (d i j : ω) := by
      funext i j
      simp [Lens.demand]
    rw [this]
    exact hh a

omit [IsOrderedRing ω] in
/-- The count matrix of `ofNatDemand h d hh` is `d`. -/
theorem countMat_ofNatDemand [Fintype ι'] (h : Handler (FreeM Q) P) (d : ι → ι' → ℕ)
    (hh : ∀ a, (h a).IsChargeBound e (∑ i, c a i • fun j => (d i j : ω))) :
    (ofNatDemand h d hh).lens.countMat PUnit.unit = Matrix.of d :=
  Lens.countMat_ofCountMat d

/-- The identity handler, certified by the counit. -/
def id [DecidableEq ι] (P : PFunctor.{uA, uB}) (c : P.A → ι → ω) : CountCertified P P c c where
  handler := Handler.id P
  lens := Lens.bangCounit _
  certificate a := by
    have h : ∑ i, c a i • (Lens.bangCounit (y^ι : PFunctor.{0, u})).demand ω i = c a := by
      rw [Lens.demand_bangCounit]
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [h]
    exact withinCharge_id c a

/-- The identity handler's certificate is the identity certificate. -/
theorem toCertified_id [DecidableEq ι] (P : PFunctor.{uA, uB}) (c : P.A → ι → ω) :
    (id P c).toCertified = Certified.id P c := by
  simp only [toCertified, id, Certified.ofDemand, Certified.id]
  congr 1
  refine OrderAddMonoidHom.ext fun u => ?_
  rw [demandHom_apply, Lens.demand_bangCounit]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

variable [Fintype ι'] {f : R.A → ι'' → ω}

/-- Handlers certified by count matrices compose, with the co-Kleisli composite of their lenses in
the opposite order. -/
def comp [DecidableEq ι''] {Q : PFunctor.{uA₂, uB}} {e : Q.A → ι' → ω}
    (D₂ : CountCertified Q R e f) (D₁ : CountCertified P Q c e) : CountCertified P R c f where
  handler := D₂.handler.comp D₁.handler
  lens := Lens.bangComp D₁.lens D₂.lens
  certificate a := by
    have h := (D₂.toCertified.comp D₁.toCertified).certificate a
    have hx : (D₂.toCertified.comp D₁.toCertified).exchange (c a) =
        ∑ i, c a i • (Lens.bangComp D₁.lens D₂.lens).demand ω i := by
      rw [Certified.comp_exchange, OrderAddMonoidHom.comp_apply]
      simp only [toCertified, Certified.ofDemand]
      rw [demandHom_demandHom, Lens.demand_bangComp]
    rw [← hx]
    exact h

/-- **Composition agrees.** The certified handler of a composite is the composite of the certified
handlers: composing exchanges of demand maps is the product of count matrices. -/
theorem toCertified_comp [DecidableEq ι''] {Q : PFunctor.{uA₂, uB}} {e : Q.A → ι' → ω}
    (D₂ : CountCertified Q R e f) (D₁ : CountCertified P Q c e) :
    (D₂.comp D₁).toCertified = D₂.toCertified.comp D₁.toCertified := by
  simp only [toCertified, comp, Certified.ofDemand, Certified.comp, Certified.mk.injEq, true_and]
  refine OrderAddMonoidHom.ext fun u => ?_
  rw [OrderAddMonoidHom.comp_apply, demandHom_demandHom, demandHom_apply, Lens.demand_bangComp]

/-- **Use bounds through two handlers.** A program with use vector `u` runs through the composite
with use vector `u` times the product of the two demand matrices. -/
theorem isChargeBound_liftM_comp [DecidableEq ι''] {Q : PFunctor.{uA₂, uB}} {e : Q.A → ι' → ω}
    (D₂ : CountCertified Q R e f) (D₁ : CountCertified P Q c e) {α : Type uB} {x : FreeM P α}
    {u : ι → ω} (hx : x.IsChargeBound c u) :
    (x.liftM (D₂.handler.comp D₁.handler)).IsChargeBound f
      (Matrix.vecMul u (Matrix.of (D₁.lens.demand ω) * Matrix.of (D₂.lens.demand ω))) := by
  rw [← Lens.demand_bangComp_eq_mul]
  exact (D₂.comp D₁).isChargeBound_liftM hx

end CountCertified

end Handler

end PFunctor
