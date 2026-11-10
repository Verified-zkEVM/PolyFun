/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Lens.Bang
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ENat.Monoid

/-!
# The graded exponential on lenses and count matrices

The graded exponential `bangLE n P` of a polynomial functor `P`, at a grade `n : ℕ∞`, has the
positions of `P` and, at a position `a`, the finite multisets of at most `n` directions of `P` at
`a` as directions: the exponential `!ₙ` of bounded linear logic (Girard, Scedrov and Scott,
*Bounded linear logic*, Theoret. Comput. Sci. 97, 1992). With the counit at grade `1`, the
comultiplication at grade `m * n`, weakening at grade `0` and contraction at grade `m + n` it is a
graded linear exponential comonad on lenses in the sense of Katsumata (*A double category
theoretic analysis of graded linear exponential comonads*, FoSSaCS 2018). The grades are related
by the inclusions `Lens.bangLESub`, and each `bangLE n P` includes into the exponential `bang P`
(`Lens.bangLEIncl`); at grade `⊤` the inclusion is an isomorphism.

A lens `bang P ⇆ Q` is a morphism of the Diller–Nahm category, composed in the co-Kleisli
category of `bang` (`Lens.bangComp`). It has grade `n` when each direction of `Q` demands at most
`n a` directions of `P` (`Lens.IsGraded`), and grades multiply along composition. At finite
directions the count matrix of such a lens at a position records the multiplicity of each
direction of `P` in the demand of each direction of `Q` (`Lens.countMat`). Composition is the
product of count matrices, and the lens `bangLE (m * n) P ⇆ bangLE m Q` that a lens of grade `n`
induces between graded exponentials (`Lens.bangLEPromote`) acts on multiplicities as the
vector–matrix product with its count matrix.

## Main definitions

* `bangLE` — the graded exponential;
* `Lens.bangLEMap`, `Lens.bangLESub`, `Lens.bangLEIncl`, `Lens.bangLECounit`,
  `Lens.bangLEComult`, `Lens.bangLEWeak`, `Lens.bangLEContr` — its action on lenses, the
  inclusions of grades, the inclusion into `bang`, counit, comultiplication, weakening and
  contraction;
* `Lens.Equiv.bangLETop` — `bangLE ⊤ P ≃ₗ bang P`;
* `LensCat.bangLEFunctor` — the graded exponential at a fixed grade as an endofunctor of `LensCat`;
* `Lens.bangComp`, `Lens.IsGraded`, `Lens.countMat`, `Lens.bangLEPromote` — co-Kleisli
  composition, grades and count matrices of lenses out of `bang`, and the induced maps between
  graded exponentials.

## Main results

* `Lens.bangLEMap_id`, `Lens.bangLEMap_comp`, `Lens.bangLECounit_natural`,
  `Lens.bangLEComult_natural`, `Lens.bangLECounit_comult`, `Lens.bangLEMap_counit_comult`,
  `Lens.bangLEComult_coassoc` — the graded comonad laws;
* `Lens.bangLEContr_natural`, `Lens.bangLEContr_weak_left`, `Lens.bangLEContr_weak_right`,
  `Lens.bangLEContr_comm`, `Lens.bangLEContr_assoc` — the graded comonoid laws;
* `Lens.bangLECounit_incl`, `Lens.bangLEComult_incl`, `Lens.bangLEContr_incl` — the graded
  structure is the structure of `bang` along the inclusions;
* `Lens.IsGraded.bangComp`, `Lens.isGraded_const_iff` — grades multiply along composition, and a
  lens of constant grade `n` factors through `bangLE n`;
* `Lens.countMat_bangComp`, `Lens.countMat_bangCounit`, `Lens.count_bangLEPromote` — composition
  is the product of count matrices, the counit has the identity matrix, and the induced map
  between graded exponentials is the vector–matrix product.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ u v

open CategoryTheory

namespace Multiset

/-- The size of a bind is at most the size of the multiset times a bound on the sizes of the
multisets it binds. -/
theorem card_bind_le_mul {α : Type u} {β : Type v} {s : Multiset α} {k : α → Multiset β}
    {n : ℕ∞} (h : ∀ x ∈ s, ((k x).card : ℕ∞) ≤ n) : ((s.bind k).card : ℕ∞) ≤ s.card * n := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have hx := h x (Multiset.mem_cons_self x s)
    have hs := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.cons_bind, Multiset.card_add, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul]
    rw [add_comm ((s.card : ℕ∞) * n)]
    exact add_le_add hx hs

/-- The sum of a function over a multiset of elements of a finite type is the sum over the type
weighted by the multiplicities. -/
theorem sum_map_eq_sum_count {β : Type v} {M : Type u} [Fintype β] [DecidableEq β]
    [AddCommMonoid M] (s : Multiset β) (f : β → M) :
    (s.map f).sum = ∑ y, s.count y • f y := by
  rw [Finset.sum_multiset_map_count]
  exact Finset.sum_subset (Finset.subset_univ _) fun y _ hy => by
    simp [Multiset.count_eq_zero.2 (by simpa using hy)]

/-- The multiplicity of `x` in a bind is the sum over the elements `y` of their multiplicity
times the multiplicity of `x` in the multiset bound to `y`. -/
theorem count_bind_eq_sum {α : Type u} {β : Type v} [Fintype β] [DecidableEq β] [DecidableEq α]
    (s : Multiset β) (k : β → Multiset α) (x : α) :
    (s.bind k).count x = ∑ y, s.count y * (k y).count x := by
  rw [Multiset.count_bind, sum_map_eq_sum_count]
  simp [smul_eq_mul]

end Multiset

namespace PFunctor

/-- The graded exponential: the positions of `P`, and at a position the finite multisets of at
most `n` directions of `P` at it. -/
abbrev bangLE (n : ℕ∞) (P : PFunctor.{uA, uB}) : PFunctor.{uA, uB} :=
  ⟨P.A, fun a => {m : Multiset (P.B a) // (m.card : ℕ∞) ≤ n}⟩

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-! ## The graded comonad structure -/

/-- The action of the graded exponential on a lens: the backward map acts on each element of a
multiset. -/
def bangLEMap (n : ℕ∞) (l : Lens P Q) : Lens (bangLE n P) (bangLE n Q) :=
  l.toFunA ⇆ fun a m => ⟨m.1.map (l.toFunB a), by simpa using m.2⟩

/-- The inclusion of grades: a multiset of at most `n` directions has at most `m ≥ n`. -/
def bangLESub {m n : ℕ∞} (h : n ≤ m) (P : PFunctor.{uA, uB}) : Lens (bangLE m P) (bangLE n P) :=
  id ⇆ fun _ s => ⟨s.1, s.2.trans h⟩

/-- The inclusion of the graded exponential into the exponential: a bounded multiset is a
multiset. -/
def bangLEIncl (n : ℕ∞) (P : PFunctor.{uA, uB}) : Lens (bang P) (bangLE n P) :=
  id ⇆ fun _ s => s.1

/-- The counit at grade `1` (dereliction): a direction demands itself once. -/
def bangLECounit (P : PFunctor.{uA, uB}) : Lens (bangLE 1 P) P :=
  id ⇆ fun _ d => ⟨{d}, by simp⟩

/-- The comultiplication at grade `m * n` (digging): at most `m` multisets of at most `n`
directions demand their sum. -/
def bangLEComult (m n : ℕ∞) (P : PFunctor.{uA, uB}) :
    Lens (bangLE (m * n) P) (bangLE m (bangLE n P)) :=
  id ⇆ fun _ M => ⟨M.1.bind Subtype.val,
    (Multiset.card_bind_le_mul fun x _ => x.2).trans (mul_le_mul' M.2 le_rfl)⟩

/-- The graded exponential preserves identities. -/
theorem bangLEMap_id (n : ℕ∞) : bangLEMap n (Lens.id P) = Lens.id (bangLE n P) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun s => Subtype.ext (Multiset.map_id s.1)

/-- The graded exponential preserves composition. -/
theorem bangLEMap_comp (n : ℕ∞) (m : Lens Q R) (l : Lens P Q) :
    bangLEMap n (m ∘ₗ l) = bangLEMap n m ∘ₗ bangLEMap n l :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun s => Subtype.ext
    (Multiset.map_map (l.toFunB a) (m.toFunB (l.toFunA a)) s.1).symm

/-- The inclusion of a grade in itself is the identity. -/
theorem bangLESub_refl (n : ℕ∞) (P : PFunctor.{uA, uB}) :
    bangLESub (le_refl n) P = Lens.id (bangLE n P) :=
  rfl

/-- Inclusions of grades compose. -/
theorem bangLESub_comp {k m n : ℕ∞} (h₁ : n ≤ m) (h₂ : m ≤ k) (P : PFunctor.{uA, uB}) :
    bangLESub h₁ P ∘ₗ bangLESub h₂ P = bangLESub (h₁.trans h₂) P :=
  rfl

/-- The inclusions of grades are natural. -/
theorem bangLESub_natural {m n : ℕ∞} (h : n ≤ m) (l : Lens P Q) :
    bangLESub h Q ∘ₗ bangLEMap m l = bangLEMap n l ∘ₗ bangLESub h P :=
  rfl

/-- The inclusions of grades commute with the inclusion into the exponential. -/
theorem bangLESub_incl {m n : ℕ∞} (h : n ≤ m) (P : PFunctor.{uA, uB}) :
    bangLESub h P ∘ₗ bangLEIncl m P = bangLEIncl n P :=
  rfl

/-- The inclusion into the exponential is natural. -/
theorem bangLEIncl_natural (n : ℕ∞) (l : Lens P Q) :
    bangLEIncl n Q ∘ₗ bangMap l = bangLEMap n l ∘ₗ bangLEIncl n P :=
  rfl

/-- The counit is natural. -/
theorem bangLECounit_natural (l : Lens P Q) :
    bangLECounit Q ∘ₗ bangLEMap 1 l = l ∘ₗ bangLECounit P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext (Multiset.map_singleton _ _)

/-- The comultiplication is natural. -/
theorem bangLEComult_natural (m n : ℕ∞) (l : Lens P Q) :
    bangLEComult m n Q ∘ₗ bangLEMap (m * n) l =
      bangLEMap m (bangLEMap n l) ∘ₗ bangLEComult m n P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext (by
    dsimp only [Lens.comp, bangLEComult, bangLEMap, Function.comp]
    simp [Multiset.map_bind, Multiset.bind_map])

/-- Left counit law: the counit after the comultiplication at grades `1` and `n` is the inclusion
of `1 * n` in `n`. -/
theorem bangLECounit_comult (n : ℕ∞) (P : PFunctor.{uA, uB}) :
    bangLECounit (bangLE n P) ∘ₗ bangLEComult 1 n P = bangLESub (one_mul n).ge P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ =>
    Subtype.ext (Multiset.singleton_bind _ _)

/-- Right counit law: the graded exponential of the counit after the comultiplication at grades
`n` and `1` is the inclusion of `n * 1` in `n`. -/
theorem bangLEMap_counit_comult (n : ℕ∞) (P : PFunctor.{uA, uB}) :
    bangLEMap n (bangLECounit P) ∘ₗ bangLEComult n 1 P = bangLESub (mul_one n).ge P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext (by
    dsimp only [Lens.comp, bangLEMap, bangLEComult, bangLECounit, bangLESub, Function.comp]
    simp only [Multiset.bind_map]
    exact (Multiset.bind_singleton _ fun y => y).trans (Multiset.map_id' _))

/-- Coassociativity of the comultiplication, up to the inclusion of `m * n * k` in
`m * (n * k)`. -/
theorem bangLEComult_coassoc (m n k : ℕ∞) (P : PFunctor.{uA, uB}) :
    bangLEComult m n (bangLE k P) ∘ₗ bangLEComult (m * n) k P =
      bangLEMap m (bangLEComult n k P) ∘ₗ bangLEComult m (n * k) P ∘ₗ
        bangLESub (mul_assoc m n k).ge P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext (by
    dsimp only [Lens.comp, bangLEMap, bangLEComult, bangLESub, Function.comp]
    simp [Multiset.bind_assoc, Multiset.bind_map])

/-- The graded counit is the counit of the exponential. -/
theorem bangLECounit_incl (P : PFunctor.{uA, uB}) :
    bangLECounit P ∘ₗ bangLEIncl 1 P = bangCounit P :=
  rfl

/-- The graded comultiplication is the comultiplication of the exponential. -/
theorem bangLEComult_incl (m n : ℕ∞) (P : PFunctor.{uA, uB}) :
    bangLEComult m n P ∘ₗ bangLEIncl (m * n) P =
      bangLEMap m (bangLEIncl n P) ∘ₗ bangLEIncl m (bang P) ∘ₗ bangComult P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => by
    dsimp only [Lens.comp, bangLEComult, bangLEIncl, bangLEMap, bangComult, Function.comp]
    simp [Multiset.bind]

/-! ## Weakening and contraction -/

/-- Weakening at grade `0`: no direction is demanded. -/
def bangLEWeak (P : PFunctor.{uA, uB}) : Lens (bangLE 0 P) y.{uA, uB} :=
  (fun _ => PUnit.unit) ⇆ fun _ _ => ⟨0, by simp⟩

/-- Contraction at grade `m + n`: a position is duplicated, and a pair of multisets demands their
sum. -/
def bangLEContr (m n : ℕ∞) (P : PFunctor.{uA, uB}) :
    Lens (bangLE (m + n) P) (bangLE m P ⊗ bangLE n P) :=
  (fun a => (a, a)) ⇆ fun _ s => ⟨s.1.1 + s.2.1, by simpa using add_le_add s.1.2 s.2.2⟩

/-- Contraction is natural. -/
theorem bangLEContr_natural (m n : ℕ∞) (l : Lens P Q) :
    (bangLEMap m l ⊗ₗ bangLEMap n l) ∘ₗ bangLEContr m n P =
      bangLEContr m n Q ∘ₗ bangLEMap (m + n) l :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext (Multiset.map_add _ _ _).symm

/-- Weakening on the left after contraction is the inverse of the left unitor, up to the
inclusion of `0 + n` in `n`. -/
theorem bangLEContr_weak_left (n : ℕ∞) (P : PFunctor.{uA, uB}) :
    (bangLEWeak P ⊗ₗ Lens.id (bangLE n P)) ∘ₗ bangLEContr 0 n P =
      Lens.Equiv.yTensor.invLens ∘ₗ bangLESub (zero_add n).ge P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun s => Subtype.ext (zero_add s.2.1)

/-- Weakening on the right after contraction is the inverse of the right unitor, up to the
inclusion of `n + 0` in `n`. -/
theorem bangLEContr_weak_right (n : ℕ∞) (P : PFunctor.{uA, uB}) :
    (Lens.id (bangLE n P) ⊗ₗ bangLEWeak P) ∘ₗ bangLEContr n 0 P =
      Lens.Equiv.tensorY.invLens ∘ₗ bangLESub (add_zero n).ge P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun s => Subtype.ext (add_zero s.1.1)

/-- Contraction is cocommutative, up to the inclusion of `m + n` in `n + m`. -/
theorem bangLEContr_comm (m n : ℕ∞) (P : PFunctor.{uA, uB}) :
    (Lens.Equiv.tensorComm (bangLE m P) (bangLE n P)).toLens ∘ₗ bangLEContr m n P =
      bangLEContr n m P ∘ₗ bangLESub (add_comm n m).le P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext (add_comm _ _)

/-- Contraction is coassociative, up to the inclusion of `k + (m + n)` in `k + m + n`. -/
theorem bangLEContr_assoc (k m n : ℕ∞) (P : PFunctor.{uA, uB}) :
    (Lens.id (bangLE k P) ⊗ₗ bangLEContr m n P) ∘ₗ bangLEContr k (m + n) P =
      Lens.Equiv.tensorAssoc.toLens ∘ₗ (bangLEContr k m P ⊗ₗ Lens.id (bangLE n P)) ∘ₗ
        bangLEContr (k + m) n P ∘ₗ bangLESub (add_assoc k m n).le P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext (add_assoc _ _ _).symm

/-- Graded contraction is the contraction of the exponential. -/
theorem bangLEContr_incl (m n : ℕ∞) (P : PFunctor.{uA, uB}) :
    bangLEContr m n P ∘ₗ bangLEIncl (m + n) P =
      (bangLEIncl m P ⊗ₗ bangLEIncl n P) ∘ₗ bangContr P :=
  rfl

end Lens

/-- The graded exponential at grade `⊤` is the exponential. -/
def Lens.Equiv.bangLETop (P : PFunctor.{uA, uB}) : bangLE ⊤ P ≃ₗ bang P where
  toLens := id ⇆ fun _ s => ⟨s, le_top⟩
  invLens := Lens.bangLEIncl ⊤ P
  left_inv := rfl
  right_inv := rfl

namespace LensCat

/-- The graded exponential at a fixed grade as an endofunctor of the category of lenses. -/
def bangLEFunctor (n : ℕ∞) : LensCat.{uA, uB} ⥤ LensCat.{uA, uB} where
  obj X := LensCat.of (bangLE n X.toPFunctor)
  map f := Lens.bangLEMap n f
  map_id _ := Lens.bangLEMap_id n
  map_comp f g := Lens.bangLEMap_comp n g f

end LensCat

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-! ## Grades of lenses out of the exponential -/

/-- Composition in the co-Kleisli category of the exponential: the composite of `g : bang Q ⇆ R`
and `f : bang P ⇆ Q` sends a direction of `R` to the sum of the demands of `f` at the directions
that `g` demands. -/
def bangComp (g : Lens (bang Q) R) (f : Lens (bang P) Q) : Lens (bang P) R :=
  g ∘ₗ bangMap f ∘ₗ bangComult P

/-- The backward map of a co-Kleisli composite is the bind of the backward maps. -/
@[simp]
theorem bangComp_toFunB (g : Lens (bang Q) R) (f : Lens (bang P) Q) (a : P.A)
    (z : R.B (g.toFunA (f.toFunA a))) :
    (bangComp g f).toFunB a z = (g.toFunB (f.toFunA a) z).bind (f.toFunB a) :=
  rfl

/-- A lens out of the exponential has grade `n` when each direction of the target at the image of
`a` demands at most `n a` directions of the source. -/
def IsGraded (n : P.A → ℕ∞) (g : Lens (bang P) Q) : Prop :=
  ∀ a y, ((g.toFunB a y).card : ℕ∞) ≤ n a

/-- A grade can be raised. -/
theorem IsGraded.mono {n n' : P.A → ℕ∞} {g : Lens (bang P) Q} (hg : g.IsGraded n)
    (h : ∀ a, n a ≤ n' a) : g.IsGraded n' :=
  fun a y => (hg a y).trans (h a)

/-- The counit of the exponential has grade `1`. -/
theorem isGraded_bangCounit (P : PFunctor.{uA, uB}) : (bangCounit P).IsGraded fun _ => 1 :=
  fun _ d => (congrArg (Nat.cast : ℕ → ℕ∞) (Multiset.card_singleton d)).le.trans (by simp)

/-- Grades multiply along co-Kleisli composition. -/
theorem IsGraded.bangComp {g : Lens (bang Q) R} {f : Lens (bang P) Q} {m : Q.A → ℕ∞}
    {n : P.A → ℕ∞} (hg : g.IsGraded m) (hf : f.IsGraded n) :
    IsGraded (P := P) (fun a => m (f.toFunA a) * n a) (Lens.bangComp g f) :=
  fun a z => (Multiset.card_bind_le_mul fun x _ => hf a x).trans (mul_le_mul' (hg _ z) le_rfl)

/-- A lens out of the exponential has constant grade `n` exactly when it factors through the
inclusion of the graded exponential `bangLE n`. -/
theorem isGraded_const_iff (n : ℕ∞) (g : Lens (bang P) Q) :
    g.IsGraded (fun _ => n) ↔ ∃ l : Lens (bangLE n P) Q, l ∘ₗ bangLEIncl n P = g := by
  constructor
  · intro h
    exact ⟨g.toFunA ⇆ fun a y => ⟨g.toFunB a y, h a y⟩, rfl⟩
  · rintro ⟨l, rfl⟩ a y
    exact (l.toFunB a y).2

/-- The lens between graded exponentials induced by a lens of grade `n`: at most `m` directions
of `Q` demand the sum of their demands, at most `m * n` directions of `P`. -/
def bangLEPromote (m : ℕ∞) {n : ℕ∞} (l : Lens (bangLE n P) Q) :
    Lens (bangLE (m * n) P) (bangLE m Q) :=
  bangLEMap m l ∘ₗ bangLEComult m n P

/-- Graded co-Kleisli composition through the induced lens is co-Kleisli composition of the
exponential, along the inclusions. -/
theorem bangLEPromote_incl {m n : ℕ∞} (g : Lens (bangLE m Q) R) (f : Lens (bangLE n P) Q) :
    (g ∘ₗ bangLEPromote m f) ∘ₗ bangLEIncl (m * n) P =
      bangComp (g ∘ₗ bangLEIncl m Q) (f ∘ₗ bangLEIncl n P) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => by
    dsimp only [Lens.comp, bangLEPromote, bangComp, bangLEMap, bangLEComult, bangLEIncl, bangMap,
      bangComult, Function.comp]
    simp [Multiset.bind]

/-! ## Count matrices -/

/-- The count matrix of a lens out of the exponential at a position: the multiplicity of the
direction `x` of the source in the demand of the direction `y` of the target. -/
def countMat [∀ a, DecidableEq (P.B a)] (g : Lens (bang P) Q) (a : P.A) :
    Matrix (Q.B (g.toFunA a)) (P.B a) ℕ :=
  Matrix.of fun y x => (g.toFunB a y).count x

/-- Co-Kleisli composition is the product of count matrices. -/
theorem countMat_bangComp [∀ b, Fintype (Q.B b)] [∀ a, DecidableEq (P.B a)]
    [∀ b, DecidableEq (Q.B b)] (g : Lens (bang Q) R) (f : Lens (bang P) Q) (a : P.A) :
    (bangComp g f).countMat a = g.countMat (f.toFunA a) * f.countMat a := by
  ext z x
  simp only [countMat, Matrix.of_apply]
  exact Multiset.count_bind_eq_sum _ _ _

/-- The count matrix of the counit of the exponential is the identity matrix. -/
theorem countMat_bangCounit [∀ a, DecidableEq (P.B a)] (a : P.A) :
    (bangCounit P).countMat a = (1 : Matrix (P.B a) (P.B a) ℕ) := by
  refine Matrix.ext fun (y : P.B a) x => ?_
  change Multiset.count x {y} = _
  simp [Matrix.one_apply, Multiset.count_singleton, eq_comm]

/-- The number of directions demanded is the row sum of the count matrix. -/
theorem card_eq_sum_countMat [∀ a, Fintype (P.B a)] [∀ a, DecidableEq (P.B a)]
    (g : Lens (bang P) Q) (a : P.A) (y : Q.B (g.toFunA a)) :
    (g.toFunB a y).card = ∑ x, g.countMat a y x := by
  simp [countMat]

/-- The lens induced between graded exponentials acts on multiplicities as the vector–matrix
product with the count matrix. -/
theorem count_bangLEPromote [∀ b, Fintype (Q.B b)] [∀ a, DecidableEq (P.B a)]
    [∀ b, DecidableEq (Q.B b)] (m : ℕ∞) {n : ℕ∞} (l : Lens (bangLE n P) Q) (a : P.A)
    (s : (bangLE m Q).B (l.toFunA a)) (x : P.B a) :
    ((bangLEPromote m l).toFunB a s).1.count x =
      Matrix.vecMul (fun y : Q.B (l.toFunA a) => s.1.count y)
        ((l ∘ₗ bangLEIncl n P).countMat a) x := by
  change Multiset.count x ((s.1.map (l.toFunB a)).bind Subtype.val) = _
  rw [Multiset.bind_map]
  exact Multiset.count_bind_eq_sum s.1 _ x

end Lens

end PFunctor
