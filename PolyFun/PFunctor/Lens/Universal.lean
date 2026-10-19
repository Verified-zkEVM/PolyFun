/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Cartesian
public import PolyFun.PFunctor.Lens.Distributivity

/-!
# Universal properties of sums and products, and lenses into special polynomials

Sums and products of polynomials are coproducts and products in `Poly`, and they agree with the
pointwise sums and products of their actions (Niu–Spivak Prop 3.3, p. 42, and Prop 3.56, p. 57).

* `Obj.sigmaEquiv`, `Obj.piEquiv`, `Obj.sumEquiv`, `Obj.prodEquiv`: the action of a sum or
  product is the sum or product of the actions. `Obj.piEquiv` is the instance of pushing `Π`
  past `Σ` (Prop 1.27) that Prop 3.56 uses.
* `Lens.sigmaEquiv`, `Lens.piEquiv`, `Lens.sumEquiv`, `Lens.prodEquiv`: the universal
  properties as hom-set equivalences, with the projections `Lens.piProj`.

Lenses into and out of the special polynomials of Niu–Spivak §5.1 (pp. 145–148) reduce to
functions between positions and directions:

* `Lens.linearEquiv : Lens (linear I) p ≃ (I → p.A)` and
  `Lens.constEquiv : Lens (C I) p ≃ (I → p.Obj PEmpty)`, two of the hom-isomorphisms of the
  adjoint quadruple of Thm 5.4. The third, `Poly(p, I) ≅ Set(p(1), I)`, is `homToConst`.
* `Lens.sectionEquiv : Lens p y ≃ ((a : p.A) → p.B a)`, the sections `Γ(p)` (Def 3.36).
* `Lens.toPurePowerEquiv : Lens p (y^A) ≃ (A → (a : p.A) → p.B a)`, the adjunction `Γ ⊣ y^(−)`
  (Prop 5.12).
* `Lens.toMonomialEquiv`, the principal-monomial hom-isomorphism (Cor 5.15).
* `Lens.sectionTensorEquiv`, the sections of a parallel product (Prop 4.54).

Prop 5.8 is the constant-family case of `sigmaEquiv` and `piEquiv`. Each equivalence comes with
its naturality in the polynomial that varies. All of them except the binary `+` and `*` cases
are definitional in both directions.
-/

@[expose] public section

universe v w uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor

/-! ## Sums and products of actions -/

namespace Obj

/-- The action of an indexed sum is the sum of the actions (Niu–Spivak Prop 3.3). -/
def sigmaEquiv {I : Type v} (F : I → PFunctor.{uA, uB}) (X : Type w) :
    (sigma F).Obj X ≃ Σ i, (F i).Obj X where
  toFun x := ⟨sigma.fst x.fst, Obj.mk (sigma.snd x.fst) x.snd⟩
  invFun s := Obj.mk (sigma.mk s.1 s.2.fst) s.2.snd
  left_inv _ := rfl
  right_inv _ := rfl

/-- The action of an indexed product is the product of the actions (Niu–Spivak Prop 3.56): an
element is a choice of position in every factor together with labels for all their directions,
which is a family of elements by pushing `Π` past `Σ` (Prop 1.27). -/
def piEquiv {I : Type v} (F : I → PFunctor.{uA, uB}) (X : Type w) :
    (pi F).Obj X ≃ ∀ i, (F i).Obj X where
  toFun x i := Obj.mk (x.fst i) fun b => x.snd ⟨i, b⟩
  invFun g := Obj.mk (fun i => (g i).fst) fun d => (g d.1).snd d.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The action of a binary sum is the sum of the actions. -/
def sumEquiv (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (X : Type w) :
    (P + Q).Obj X ≃ P.Obj X ⊕ Q.Obj X where
  toFun x :=
    match (motive := ∀ s : P.A ⊕ Q.A, ((P + Q).B s → X) → P.Obj X ⊕ Q.Obj X) x.fst, x.snd with
    | Sum.inl a, f => Sum.inl (Obj.mk a f)
    | Sum.inr b, f => Sum.inr (Obj.mk b f)
  invFun s := match s with
    | Sum.inl x => Obj.mk (Sum.inl x.fst : (P + Q).A) x.snd
    | Sum.inr x => Obj.mk (Sum.inr x.fst : (P + Q).A) x.snd
  left_inv x := by
    induction x using Obj.rec with
    | mk s f => cases s <;> rfl
  right_inv s := by cases s <;> rfl

/-- The action of a binary product is the product of the actions. -/
def prodEquiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (X : Type w) :
    (P * Q).Obj X ≃ P.Obj X × Q.Obj X where
  toFun x := (Obj.mk x.fst.1 (x.snd ∘ Sum.inl), Obj.mk x.fst.2 (x.snd ∘ Sum.inr))
  invFun xy := Obj.mk (xy.1.fst, xy.2.fst) (Sum.elim xy.1.snd xy.2.snd)
  left_inv x := by
    induction x using Obj.rec with
    | mk a f => exact Obj.ext rfl (heq_of_eq (funext fun d => by cases d <;> rfl))
  right_inv _ := rfl

end Obj

namespace Lens

/-! ## Indexed coproducts and products -/

section Sigma

variable {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}}

@[simp] theorem sigmaExists_comp_sigmaInj (l : ∀ i, Lens (F i) R) (i : I) :
    sigmaExists l ∘ₗ sigmaInj i = l i := rfl

/-- Lenses out of an indexed sum are families of lenses out of its members: `sigma F` is the
coproduct of `F` in `Poly` (Niu–Spivak Prop 3.3). -/
def sigmaEquiv : Lens (sigma F) R ≃ ∀ i, Lens (F i) R where
  toFun l i := l ∘ₗ sigmaInj i
  invFun := sigmaExists
  left_inv _ := rfl
  right_inv _ := rfl

/-- The copairing `sigmaExists l` is the only lens out of `sigma F` that restricts to `l`. -/
theorem eq_sigmaExists {l : ∀ i, Lens (F i) R} {h : Lens (sigma F) R}
    (hh : ∀ i, h ∘ₗ sigmaInj i = l i) : h = sigmaExists l :=
  sigmaEquiv.injective (funext hh)

end Sigma

section Pi

variable {I : Type v} {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}}

/-- The projection from an indexed product onto its `i`-th factor. -/
def piProj (i : I) : Lens (pi F) (F i) :=
  (fun f => f i) ⇆ fun _ b => ⟨i, b⟩

@[simp] theorem piProj_comp_piForall (l : ∀ i, Lens P (F i)) (i : I) :
    piProj i ∘ₗ piForall l = l i := rfl

/-- Lenses into an indexed product are families of lenses into its factors: `pi F` is the
product of `F` in `Poly` (Niu–Spivak Prop 3.56). -/
def piEquiv : Lens P (pi F) ≃ ∀ i, Lens P (F i) where
  toFun l i := piProj i ∘ₗ l
  invFun := piForall
  left_inv l := by
    ext a d
    · rfl
    · cases d
      rfl
  right_inv _ := rfl

/-- The pairing `piForall l` is the only lens into `pi F` whose projections are `l`. -/
theorem eq_piForall {l : ∀ i, Lens P (F i)} {h : Lens P (pi F)}
    (hh : ∀ i, piProj i ∘ₗ h = l i) : h = piForall l :=
  piEquiv.injective (funext hh)

end Pi

/-! ## Binary coproducts and products -/

/-- Lenses out of a binary sum are pairs of lenses (Niu–Spivak Prop 3.3). -/
def sumEquiv {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}} {R : PFunctor.{uA₃, uB₃}} :
    Lens.{max uA₁ uA₂, uB₁, uA₃, uB₃} (P + Q) R ≃ Lens P R × Lens Q R where
  toFun l := (l ∘ₗ inl, l ∘ₗ inr)
  invFun fg := sumPair fg.1 fg.2
  left_inv := comp_inl_inr
  right_inv _ := rfl

/-- Lenses into a binary product are pairs of lenses (Niu–Spivak Prop 3.56). -/
def prodEquiv {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}} :
    Lens.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q * R) ≃ Lens P Q × Lens P R where
  toFun l := (fst ∘ₗ l, snd ∘ₗ l)
  invFun fg := prodPair fg.1 fg.2
  left_inv := comp_fst_snd
  right_inv _ := rfl

/-! ## Lenses into and out of special polynomials (Niu–Spivak §5.1) -/

section Special

variable {p : PFunctor.{uA₁, uB₁}} {q : PFunctor.{uA₃, uB₃}}

/-- `Poly(I y, p) ≅ Set(I, p(1))`: a lens out of a linear polynomial is a family of positions
(Niu–Spivak Thm 5.4, `linear ⊣ (−)(1)`). -/
def linearEquiv {I : Type uA₂} : Lens (linear I : PFunctor.{uA₂, uB₂}) p ≃ (I → p.A) where
  toFun l := l.toFunA
  invFun f := f ⇆ fun _ _ => PUnit.unit
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Poly(I, p) ≅ Set(I, p(0))`: a lens out of a constant polynomial is a family of elements of
`p.Obj PEmpty`, i.e. of positions without directions (Niu–Spivak Thm 5.4, `C ⊣ (−)(0)`; see
`Obj.pemptyEquiv`). -/
def constEquiv {I : Type uA₂} :
    Lens (C I : PFunctor.{uA₂, uB₂}) p ≃ (I → p.Obj PEmpty.{uB₂ + 1}) :=
  homMonomialEquiv

/-- A lens into `y` is a **section**: a choice of direction at every position, `Γ(p) = Poly(p, y)
≅ Π_{a ∈ p(1)} p[a]` (Niu–Spivak Def 3.36). -/
def sectionEquiv : Lens p (y : PFunctor.{uA₂, uB₂}) ≃ ((a : p.A) → p.B a) where
  toFun l a := l.toFunB a PUnit.unit
  invFun s := (fun _ => PUnit.unit) ⇆ fun a _ => s a
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Poly(p, y^A) ≅ Set(A, Γ(p))`: the adjunction between the sections functor and the Yoneda
embedding (Niu–Spivak Prop 5.12). -/
def toPurePowerEquiv {A : Type uB₂} :
    Lens p (y^A : PFunctor.{uA₂, uB₂}) ≃ (A → (a : p.A) → p.B a) where
  toFun l x a := l.toFunB a x
  invFun g := (fun _ => PUnit.unit) ⇆ fun a x => g x a
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Poly(p, I y^A) ≅ Set(p(1), I) × Set(A, Γ(p))`: the principal-monomial adjunction (Niu–Spivak
Cor 5.15). -/
def toMonomialEquiv {I : Type uA₂} {A : Type uB₂} :
    Lens p (I y^ A) ≃ (p.A → I) × (A → (a : p.A) → p.B a) where
  toFun l := (l.toFunA, fun x a => l.toFunB a x)
  invFun fg := fg.1 ⇆ fun a x => fg.2 x a
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Γ(p ⊗ q) ≅ Set(q(1), Γ(p)) × Set(p(1), Γ(q))`: a section of a parallel product is a
section of `p` for every position of `q` together with a section of `q` for every position of
`p` (Niu–Spivak Prop 4.54). -/
def sectionTensorEquiv :
    Lens (p ⊗ q) (y : PFunctor.{uA₂, uB₂}) ≃
      (q.A → (a : p.A) → p.B a) × (p.A → (b : q.A) → q.B b) where
  toFun l := (fun b a => (l.toFunB (a, b) PUnit.unit).1, fun a b => (l.toFunB (a, b) PUnit.unit).2)
  invFun st := (fun _ => PUnit.unit) ⇆ fun ab _ => (st.1 ab.2 ab.1, st.2 ab.1 ab.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Naturality -/

/-- `linearEquiv` is natural in the target. -/
theorem linearEquiv_comp {I : Type uA₂} (f : Lens p q)
    (l : Lens (linear I : PFunctor.{uA₂, uB₂}) p) :
    linearEquiv (f ∘ₗ l) = f.toFunA ∘ linearEquiv l := rfl

/-- `constEquiv` is natural in the target. -/
theorem constEquiv_comp {I : Type uA₂} (f : Lens p q) (l : Lens (C I : PFunctor.{uA₂, uB₂}) p) :
    constEquiv (f ∘ₗ l) = f.mapObj ∘ constEquiv l := rfl

/-- `sectionEquiv` is natural in the source: precomposing a section with a lens pulls it back. -/
theorem sectionEquiv_comp (s : Lens q (y : PFunctor.{uA₂, uB₂})) (f : Lens p q) :
    sectionEquiv (s ∘ₗ f) = fun a => f.toFunB a (sectionEquiv s (f.toFunA a)) := rfl

/-- `toPurePowerEquiv` is natural in the source. -/
theorem toPurePowerEquiv_comp {A : Type uB₂} (g : Lens q (y^A : PFunctor.{uA₂, uB₂}))
    (f : Lens p q) :
    toPurePowerEquiv (g ∘ₗ f) = fun x a => f.toFunB a (toPurePowerEquiv g x (f.toFunA a)) := rfl

/-- `toMonomialEquiv` is natural in the source. -/
theorem toMonomialEquiv_comp {I : Type uA₂} {A : Type uB₂} (g : Lens q (I y^ A)) (f : Lens p q) :
    toMonomialEquiv (g ∘ₗ f) =
      ((toMonomialEquiv g).1 ∘ f.toFunA,
        fun x a => f.toFunB a ((toMonomialEquiv g).2 x (f.toFunA a))) := rfl

end Special

end Lens

end PFunctor
