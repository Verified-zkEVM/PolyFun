/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.Equiv.Basic
import Batteries.Tactic.Lint

/-!
# Charts between polynomial functors

A `Chart P Q` is a pair `(toFunA, toFunB)` where

* `toFunA : P.A → Q.A` is a forward map on positions, and
* `toFunB : ∀ a, P.B a → Q.B (toFunA a)` is a forward map on directions.

While **lenses** make `Poly` into a 2-category whose categorical product is
`*` (positions ×, directions Σ), **charts** make `Poly` into a different
category that is isomorphic to the arrow category `Set^→` (squares
`B → A → B' → A'`). A consequence is that the chart category has a
*different* monoidal structure from the lens category.

## Comparison with `Lens`

|              | Lens                                     | Chart                            |
|--------------|------------------------------------------|----------------------------------|
| Coproduct    | `+`                                      | `+` (same)                       |
| Product      | `*` (positions ×, directions ⊕)          | `⊗` (positions ×, directions ×)  |
| Terminal     | `1` (positions = 1, no directions)       | `X = y` (positions = 1, dir = 1) |
| Composition  | `compMap` is natural                     | `compMap` is **not** natural     |
| Sigma        | `sigmaExists`, `sigmaMap`                | `sigmaExists`, `sigmaMap`        |
| Pi           | `piForall`, `piMap`                      | only `piMap`                     |

The operations missing from charts (`compMap`, `piForall`, projections from
`*`, `sigmaForall`) all require contravariance and so are intrinsically
lens-side. What charts do have, they have cleanly: `+` is the coproduct
with `inl`/`inr`/`sumPair`, and `⊗` is the categorical product with
`fst`/`snd`/`tensorPair`.

## Layout

This file mirrors `PolyFun/PFunctor/Lens/Basic.lean` for ease of
cross-reference. Each section header that overlaps with `Lens` is named
identically; the chart-specific sections (`Tensor` for the categorical
product, `Prod` for the polynomial product) are documented inline.

## Downstream consumers

`Interface.Hom`, `Interface.Hom.mapPacket`, and the boundary-side composition
operators are intentionally thin wrappers around this file. New downstream
operators on packet/index transport (e.g. parallel composition, sum routing)
should be defined as wrappers, not re-implemented.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆

namespace PFunctor

namespace Chart

@[ext (iff := false)]
theorem ext {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (c₁ c₂ : Chart P Q)
    (h₁ : ∀ a, c₁.toFunA a = c₂.toFunA a) (h₂ : ∀ a, c₁.toFunB a = (h₁ a) ▸ c₂.toFunB a) :
    c₁ = c₂ := by
  rcases c₁ with ⟨toFunA₁, toFunB₁⟩
  rcases c₂ with ⟨toFunA₂, toFunB₂⟩
  have h : toFunA₁ = toFunA₂ := funext h₁
  subst h
  have hB : toFunB₁ = toFunB₂ := by
    funext a
    simpa using h₂ a
  subst hB
  rfl

/-! ### Identity and composition -/

/-- The identity chart -/
protected def id (P : PFunctor.{uA, uB}) : Chart P P := id ⇉ fun _ => id

/-- Composition of charts -/
def comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (c' : Chart Q R) (c : Chart P Q) : Chart P R where
  toFunA := c'.toFunA ∘ c.toFunA
  toFunB := fun i => c'.toFunB (c.toFunA i) ∘ c.toFunB i

/-- Infix notation for chart composition `c' ∘c c` -/
infixl:75 " ∘c " => comp

@[simp]
theorem id_comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Chart P Q) :
    (Chart.id Q) ∘c f = f := rfl

@[simp]
theorem comp_id {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Chart P Q) :
    f ∘c (Chart.id P) = f := rfl

theorem comp_assoc {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {S : PFunctor.{uA₄, uB₄}} (c : Chart R S) (c' : Chart Q R) (c'' : Chart P Q) :
    (c ∘c c') ∘c c'' = c ∘c (c' ∘c c'') := rfl

/-! ### Equivalences -/

/-- An equivalence between two polynomial functors `P` and `Q`, using charts.
    This corresponds to an isomorphism in the category `PFunctor` with `Chart` morphisms. -/
@[ext]
protected structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward chart of the equivalence, from `P` to `Q`. -/
  toChart : Chart P Q
  /-- The backward chart of the equivalence, from `Q` to `P`. -/
  invChart : Chart Q P
  left_inv : comp invChart toChart = Chart.id P := by simp
  right_inv : comp toChart invChart = Chart.id Q := by simp

/-- Infix notation for chart equivalence `P ≃c Q` -/
infix:50 " ≃c " => Chart.Equiv

namespace Equiv

/-- The identity equivalence on `P`, built from the identity chart in both directions. -/
@[refl]
def refl (P : PFunctor.{uA, uB}) : P ≃c P :=
  ⟨Chart.id P, Chart.id P, rfl, rfl⟩

/-- The inverse equivalence, swapping the forward and backward charts of `e`. -/
@[symm]
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : P ≃c Q) : Q ≃c P :=
  ⟨e.invChart, e.toChart, e.right_inv, e.left_inv⟩

/-- The composite equivalence `P ≃c R` obtained by chaining `e₁ : P ≃c Q` and `e₂ : Q ≃c R`. -/
@[trans]
def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (e₁ : P ≃c Q) (e₂ : Q ≃c R) : P ≃c R :=
  ⟨e₂.toChart ∘c e₁.toChart, e₁.invChart ∘c e₂.invChart,
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.left_inv, e₂.left_inv],
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.right_inv, e₂.right_inv]⟩

end Equiv

/-! ### Initial and terminal -/

/-- The (unique) initial chart from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{uA, uB}} : Chart 0 P :=
  PEmpty.elim ⇉ fun _ => PEmpty.elim

/-- The (unique) terminal chart from any functor `P` to `X = y`.

`X` is the terminal object of the chart category — a single position with a
single direction — corresponding to the identity arrow `1 → 1` in `Set^→`.
This differs from the lens-side terminal `1` (positions `1`, no directions). -/
def terminal {P : PFunctor.{uA, uB}} : Chart P X :=
  (fun _ => PUnit.unit) ⇉ (fun _ _ => PUnit.unit)

alias fromZero := initial
alias toOne := terminal

/-! ### Coproduct (`+`)

`+` is the coproduct in the chart category (as it is in the lens category).
The two inclusions `inl`/`inr` plus the copairing `sumPair` realise the
universal property of `+`. The parallel-sum `sumMap` is then a derived
construction. -/

/-- Left injection chart `inl : P → P + Q`. -/
def inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Chart.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q) :=
  Sum.inl ⇉ (fun _ d => d)

/-- Right injection chart `inr : Q → P + Q`. -/
def inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Chart.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q) :=
  Sum.inr ⇉ (fun _ d => d)

/-- Copairing of charts `[c₁, c₂]c : P + Q → R`. -/
def sumPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB₃}}
    (c₁ : Chart P R) (c₂ : Chart Q R) :
    Chart.{max uA₁ uA₂, uB, uA₃, uB₃} (P + Q) R :=
  (Sum.elim c₁.toFunA c₂.toFunA) ⇉
    (fun a d => match a with
      | Sum.inl pa => c₁.toFunB pa d
      | Sum.inr qa => c₂.toFunB qa d)

/-- Parallel application of charts for coproduct `c₁ ⊎c c₂ : P + Q → R + W`. -/
def sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₃}} (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.{max uA₁ uA₂, uB₁, max uA₃ uA₄, uB₃} (P + Q) (R + W) :=
  (Sum.map c₁.toFunA c₂.toFunA) ⇉
    (fun psum => match psum with
      | Sum.inl pa => c₁.toFunB pa
      | Sum.inr qa => c₂.toFunB qa)

/-! ### Tensor (`⊗`) — the chart category's binary product

`⊗` is the **categorical** binary product in the chart category, with
projections `fst`/`snd` and pairing `tensorPair`. (For lenses, the
categorical product is `*`, not `⊗`.) -/

/-- Projection chart `fst : P ⊗ Q → P`. -/
def fst {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P ⊗ Q) P :=
  Prod.fst ⇉ (fun _ => Prod.fst)

/-- Projection chart `snd : P ⊗ Q → Q`. -/
def snd {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, uA₂, uB₂} (P ⊗ Q) Q :=
  Prod.snd ⇉ (fun _ => Prod.snd)

/-- Pairing of charts `⟨c₁, c₂⟩c : P → Q ⊗ R`. -/
def tensorPair {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (c₁ : Chart P Q) (c₂ : Chart P R) :
    Chart.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q ⊗ R) :=
  (fun pa => (c₁.toFunA pa, c₂.toFunA pa)) ⇉
    (fun pa pb => (c₁.toFunB pa pb, c₂.toFunB pa pb))

/-- Parallel application of charts for tensor `c₁ ⊗c c₂ : P ⊗ Q → R ⊗ W`. -/
def tensorMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P ⊗ Q) (R ⊗ W) :=
  (Prod.map c₁.toFunA c₂.toFunA) ⇉
    (fun pq pb => (c₁.toFunB pq.1 pb.1, c₂.toFunB pq.2 pb.2))

/-! ### Polynomial product (`*`) — *not* the chart categorical product

The polynomial product `*` is **not** the categorical product in the chart
category: there is no natural chart `P * Q → P` because the source has
direction type `P.B a₁ ⊕ Q.B a₂` and we cannot project a `Q.B a₂` to a
`P.B a₁`. We provide only the parallel-map operation.

For categorical projections / pairing, use `⊗` instead. -/

/-- Parallel application of charts for polynomial product `c₁ ×c c₂ : P * Q → R * W`. -/
def prodMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P * Q) (R * W) :=
  (Prod.map c₁.toFunA c₂.toFunA) ⇉
    (fun pq psum => match psum with
      | Sum.inl pb => Sum.inl (c₁.toFunB pq.1 pb)
      | Sum.inr qb => Sum.inr (c₂.toFunB pq.2 qb))

/-! ### Indexed colimits and limits

The chart category has Sigma-eliminations (`sigmaExists`/`sigmaMap`) but
only the parametric Pi-map (`piMap`); `piForall` is intrinsically a
lens-side construction because it requires "choosing an index" in the
chart direction, which has no canonical choice in `Set^→`. -/

/-- Dependent copairing of charts over `sigma`: `(Σ i, F i) → R`. -/
def sigmaExists {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}}
    (c : ∀ i, Chart (F i) R) :
    Chart (sigma F) R :=
  (fun ⟨i, fa⟩ => (c i).toFunA fa) ⇉
    (fun ⟨i, fa⟩ => (c i).toFunB fa)

/-- Pointwise mapping of charts over `sigma`. -/
def sigmaMap {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    (c : ∀ i, Chart (F i) (G i)) :
    Chart (sigma F) (sigma G) :=
  (fun ⟨i, fa⟩ => ⟨i, (c i).toFunA fa⟩) ⇉
    (fun ⟨i, fa⟩ => (c i).toFunB fa)

/-- Pointwise mapping of charts over `pi`. -/
def piMap {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    (c : ∀ i, Chart (F i) (G i)) :
    Chart (pi F) (pi G) :=
  (fun fa i => (c i).toFunA (fa i)) ⇉
    (fun fa ⟨i, fb⟩ => ⟨i, (c i).toFunB (fa i) fb⟩)

/-! ### Action on indices

A chart `φ : P → Q` acts on `Idx P = Σ a : P.A, P.B a` by sending
`⟨a, b⟩ ↦ ⟨φ.toFunA a, φ.toFunB a b⟩`. This is the underlying function on
positions; `Trace.mapChart` (in `PolyFun.PFunctor.Trace`) uses it to push
event traces along charts. -/

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- Push an `Idx P` along a chart `P → Q` to an `Idx Q`. -/
def mapIdx (φ : Chart P Q) (i : Idx P) : Idx Q :=
  ⟨φ.toFunA i.1, φ.toFunB i.1 i.2⟩

@[simp] theorem mapIdx_id (i : Idx P) : mapIdx (Chart.id P) i = i := rfl

@[simp] theorem mapIdx_comp (g : Chart Q R) (f : Chart P Q) (i : Idx P) :
    mapIdx (g ∘c f) i = mapIdx g (mapIdx f i) := rfl

/-! ### Special charts -/

/-- The type of charts from a polynomial functor `P` to `X`.

A chart `P → X` is equivalent to a function `(a : P.A) → P.B a → PUnit`,
i.e. a boundary valuation that picks out a single direction at every
position. Analogous to `Lens.enclose`. -/
-- `Chart.enclose`'s two universe pairs are the independent domain (`uA`/`uB`) and
-- codomain (`uA₁`/`uB₁`) position/direction universes, kept independent.
@[nolint checkUnivs]
def enclose (P : PFunctor.{uA, uB}) : Type max uA uA₁ uB uB₁ :=
  Chart P X.{uA₁, uB₁}

/-! ### Notations for binary operations -/

@[inherit_doc] infixl:75 " ⊎c " => sumMap
@[inherit_doc] infixl:75 " ⊗c " => tensorMap
@[inherit_doc] infixl:75 " ×c " => prodMap
/-- Notation for the copairing `sumPair c₁ c₂` of two charts out of a sum. -/
notation "[" c₁ "," c₂ "]c" => sumPair c₁ c₂
/-- Notation for the pairing `tensorPair c₁ c₂` of two charts into a tensor. -/
notation "⟨" c₁ "," c₂ "⟩c" => tensorPair c₁ c₂

/-! ### Coproduct coherence -/

section Sum

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
  {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}} {S : PFunctor.{uA₅, uB₅}}

@[simp]
theorem sumMap_comp_inl (c₁ : Chart P R) (c₂ : Chart Q W) :
    ((c₁ ⊎c c₂) ∘c Chart.inl) = (Chart.inl ∘c c₁) := rfl

@[simp]
theorem sumMap_comp_inr (c₁ : Chart P R) (c₂ : Chart Q W) :
    ((c₁ ⊎c c₂) ∘c Chart.inr) = (Chart.inr ∘c c₂) := rfl

theorem sumPair_comp_sumMap (c₁ : Chart P R) (c₂ : Chart Q W)
    (f : Chart R S) (g : Chart W S) :
    Chart.sumPair f g ∘c (c₁ ⊎c c₂) = Chart.sumPair (f ∘c c₁) (g ∘c c₂) := by
  ext a <;> rcases a with a | a <;> rfl

@[simp]
theorem sumPair_comp_inl (f : Chart P R) (g : Chart Q R) :
    Chart.sumPair f g ∘c Chart.inl = f := rfl

@[simp]
theorem sumPair_comp_inr (f : Chart P R) (g : Chart Q R) :
    Chart.sumPair f g ∘c Chart.inr = g := rfl

theorem comp_inl_inr (h : Chart.{max uA₁ uA₂, uB, uA₃, uB₃} (P + Q) R) :
    Chart.sumPair (h ∘c Chart.inl) (h ∘c Chart.inr) = h := by
  ext a <;> rcases a <;> rfl

@[simp]
theorem sumMap_id :
    Chart.sumMap (Chart.id P) (Chart.id Q) = Chart.id.{max uA₁ uA₂, uB} (P + Q) := by
  ext a <;> rcases a <;> rfl

@[simp]
theorem sumPair_inl_inr :
    Chart.sumPair Chart.inl Chart.inr = Chart.id.{max uA₁ uA₂, uB} (P + Q) := by
  ext a <;> rcases a <;> rfl

theorem sumMap_comp_sumMap {S : PFunctor.{uA₅, uB₅}} {T : PFunctor.{uA₆, uB₅}}
    (c₁ : Chart P R) (c₂ : Chart Q W)
    (c₁' : Chart R S) (c₂' : Chart W T) :
    (c₁' ⊎c c₂') ∘c (c₁ ⊎c c₂) = (c₁' ∘c c₁) ⊎c (c₂' ∘c c₂) := by
  ext a <;> rcases a <;> rfl

namespace Equiv

/-- Commutativity of coproduct -/
def sumComm (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    Chart.Equiv.{max uA₁ uA₂, uB, max uA₁ uA₂, uB} (P + Q) (Q + P) where
  toChart := Chart.sumPair Chart.inr Chart.inl
  invChart := Chart.sumPair Chart.inr Chart.inl
  left_inv := by ext a <;> rcases a with a | a <;> rfl
  right_inv := by ext a <;> rcases a with a | a <;> rfl

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}

@[simp]
theorem sumComm_symm :
    (sumComm P Q).symm = sumComm Q P := rfl

/-- Associativity of coproduct -/
def sumAssoc :
    Chart.Equiv.{max uA₁ uA₂ uA₃, uB, max uA₁ uA₂ uA₃, uB} ((P + Q) + R) (P + (Q + R)) where
  toChart :=
    Chart.sumPair
      (Chart.sumPair
        Chart.inl
        (Chart.inr ∘c Chart.inl))
      (Chart.inr ∘c Chart.inr)
  invChart :=
    Chart.sumPair
      (Chart.inl ∘c Chart.inl)
      (Chart.sumPair
        (Chart.inl ∘c Chart.inr)
        Chart.inr)
  left_inv := by ext a <;> rcases a with (a | a) | a <;> rfl
  right_inv := by ext a <;> rcases a with a | (a | a) <;> rfl

/-- Coproduct with `0` is identity (right) -/
def sumZero :
    Chart.Equiv.{max uA uA₁, uB, uA₁, uB} (P + (0 : PFunctor.{uA, uB})) P where
  toChart := Chart.sumPair (Chart.id P) Chart.initial
  invChart := Chart.inl
  left_inv := by
    ext a <;> rcases a with a | a
    · rfl
    · exact PEmpty.elim a
    · rfl
    · exact PEmpty.elim a
  right_inv := by ext <;> rfl

/-- Coproduct with `0` is identity (left) -/
def zeroSum :
    Chart.Equiv.{max uA uA₁, uB, uA₁, uB} ((0 : PFunctor.{uA, uB}) + P) P where
  toChart := Chart.sumPair Chart.initial (Chart.id P)
  invChart := Chart.inr
  left_inv := by
    ext a <;> rcases a with a | a
    · exact PEmpty.elim a
    · rfl
    · exact PEmpty.elim a
    · rfl
  right_inv := by ext <;> rfl

/-- Coproduct preserves equivalences: `P ≃c P' → Q ≃c Q' → P + Q ≃c P' + Q'`. -/
def sumCongr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {P' : PFunctor.{uA₃, uB}} {Q' : PFunctor.{uA₄, uB}}
    (e₁ : P ≃c P') (e₂ : Q ≃c Q') :
    Chart.Equiv.{max uA₁ uA₂, uB, max uA₃ uA₄, uB} (P + Q) (P' + Q') where
  toChart := e₁.toChart ⊎c e₂.toChart
  invChart := e₁.invChart ⊎c e₂.invChart
  left_inv := by
    rw [Chart.sumMap_comp_sumMap, e₁.left_inv, e₂.left_inv, Chart.sumMap_id]
  right_inv := by
    rw [Chart.sumMap_comp_sumMap, e₁.right_inv, e₂.right_inv, Chart.sumMap_id]

end Equiv

end Sum

/-! ### Tensor coherence -/

section Tensor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {W : PFunctor.{uA₄, uB₄}} {S : PFunctor.{uA₅, uB₅}}

@[simp]
theorem fst_comp_tensorMap (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.fst ∘c (c₁ ⊗c c₂) = c₁ ∘c Chart.fst := rfl

@[simp]
theorem snd_comp_tensorMap (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.snd ∘c (c₁ ⊗c c₂) = c₂ ∘c Chart.snd := rfl

theorem tensorMap_comp_tensorPair (c₁ : Chart Q W) (c₂ : Chart R S)
    (f : Chart P Q) (g : Chart P R) :
    (c₁ ⊗c c₂) ∘c Chart.tensorPair f g = Chart.tensorPair (c₁ ∘c f) (c₂ ∘c g) := by
  ext _ _
  · rfl
  · rfl

@[simp]
theorem fst_comp_tensorPair (f : Chart P Q) (g : Chart P R) :
    Chart.fst ∘c Chart.tensorPair f g = f := rfl

@[simp]
theorem snd_comp_tensorPair (f : Chart P Q) (g : Chart P R) :
    Chart.snd ∘c Chart.tensorPair f g = g := rfl

theorem comp_fst_snd (h : Chart.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q ⊗ R)) :
    Chart.tensorPair (Chart.fst ∘c h) (Chart.snd ∘c h) = h := by
  ext _ _
  · rfl
  · rfl

@[simp]
theorem tensorMap_id : (Chart.id P) ⊗c (Chart.id Q) = Chart.id (P ⊗ Q) := rfl

theorem tensorMap_comp
    {P' : PFunctor.{uA₅, uB₅}} {Q' : PFunctor.{uA₆, uB₆}}
    (c₁ : Chart P P') (c₂ : Chart Q Q') (c₁' : Chart P' R) (c₂' : Chart Q' W) :
    (c₁' ∘c c₁) ⊗c (c₂' ∘c c₂) = (c₁' ⊗c c₂') ∘c (c₁ ⊗c c₂) := rfl

theorem tensorMap_comp_tensorMap
    {P' : PFunctor.{uA₅, uB₅}} {Q' : PFunctor.{uA₆, uB₆}}
    (c₁ : Chart P R) (c₂ : Chart Q W) (c₁' : Chart R P') (c₂' : Chart W Q') :
    (c₁' ⊗c c₂') ∘c (c₁ ⊗c c₂) = (c₁' ∘c c₁) ⊗c (c₂' ∘c c₂) := rfl

@[simp]
theorem tensorPair_fst_snd : Chart.tensorPair Chart.fst Chart.snd =
    Chart.id.{max uA₁ uA₂, max uB₁ uB₂} (P ⊗ Q) := by
  ext _ _
  · rfl
  · rfl

namespace Equiv

/-- Commutativity of tensor product -/
def tensorComm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) : P ⊗ Q ≃c Q ⊗ P where
  toChart := Prod.swap ⇉ (fun _ => Prod.swap)
  invChart := Prod.swap ⇉ (fun _ => Prod.swap)
  left_inv := rfl
  right_inv := rfl

@[simp]
theorem tensorComm_symm : (tensorComm P Q).symm = tensorComm Q P := rfl

/-- Associativity of tensor product -/
def tensorAssoc : (P ⊗ Q) ⊗ R ≃c P ⊗ (Q ⊗ R) where
  toChart := (_root_.Equiv.prodAssoc _ _ _).toFun ⇉
              (fun _ => (_root_.Equiv.prodAssoc _ _ _).toFun)
  invChart := (_root_.Equiv.prodAssoc _ _ _).invFun ⇉
              (fun _ => (_root_.Equiv.prodAssoc _ _ _).invFun)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `X` is identity (right) -/
def tensorX : P ⊗ X ≃c P where
  toChart := Prod.fst ⇉ (fun _ => Prod.fst)
  invChart := (fun p => (p, PUnit.unit)) ⇉ (fun _ b => (b, PUnit.unit))
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `X` is identity (left) -/
def xTensor : X ⊗ P ≃c P where
  toChart := Prod.snd ⇉ (fun _ => Prod.snd)
  invChart := (fun p => (PUnit.unit, p)) ⇉ (fun _ b => (PUnit.unit, b))
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `0` is zero (left) -/
def zeroTensor : 0 ⊗ P ≃c 0 where
  toChart := (fun a => PEmpty.elim a.1) ⇉ (fun a _ => PEmpty.elim a.1)
  invChart := PEmpty.elim ⇉ (fun a _ => PEmpty.elim a)
  left_inv := by ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by ext a <;> exact PEmpty.elim a

/-- Tensor product with `0` is zero (right) -/
def tensorZero : P ⊗ 0 ≃c 0 where
  toChart := (fun a => PEmpty.elim a.2) ⇉ (fun a _ => PEmpty.elim a.2)
  invChart := PEmpty.elim ⇉ (fun a _ => PEmpty.elim a)
  left_inv := by ext ⟨_, b⟩ <;> exact PEmpty.elim b
  right_inv := by ext a <;> exact PEmpty.elim a

/-- Tensor product preserves equivalences: `P ≃c P' → Q ≃c Q' → P ⊗ Q ≃c P' ⊗ Q'`. -/
def tensorCongr {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {P' : PFunctor.{uA₃, uB₃}} {Q' : PFunctor.{uA₄, uB₄}}
    (e₁ : P ≃c P') (e₂ : Q ≃c Q') :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄}
      (P ⊗ Q) (P' ⊗ Q') where
  toChart := e₁.toChart ⊗c e₂.toChart
  invChart := e₁.invChart ⊗c e₂.invChart
  left_inv := by
    rw [Chart.tensorMap_comp_tensorMap, e₁.left_inv, e₂.left_inv,
      Chart.tensorMap_id]
  right_inv := by
    rw [Chart.tensorMap_comp_tensorMap, e₁.right_inv, e₂.right_inv,
      Chart.tensorMap_id]

/-- Left distributivity of tensor product over coproduct.

`P ⊗ (Q + R) ≃c (P ⊗ Q) + (P ⊗ R)`. -/
def tensorSumDistrib {P : PFunctor.{uA₁, uB₁}} {Q R : PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂}
      (P ⊗ (Q + R)) ((P ⊗ Q) + (P ⊗ R)) where
  toChart :=
    (fun ⟨p, qr⟩ => match qr with
      | Sum.inl q => Sum.inl (p, q)
      | Sum.inr r => Sum.inr (p, r)) ⇉
    (fun ⟨_, qr⟩ pb => match qr with
      | Sum.inl _ => pb
      | Sum.inr _ => pb)
  invChart :=
    (Sum.elim
      (fun ⟨p, q⟩ => (p, Sum.inl q))
      (fun ⟨p, r⟩ => (p, Sum.inr r))) ⇉
    (fun pqpr pb => match pqpr with
      | Sum.inl _ => pb
      | Sum.inr _ => pb)
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro a; rcases a with ⟨_, _ | _⟩ <;> rfl
    · intro a; funext _; rcases a with ⟨_, _ | _⟩ <;> rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro a; rcases a <;> rfl
    · intro a; funext _; rcases a <;> rfl

/-- Right distributivity of tensor product over coproduct.

`(Q + R) ⊗ P ≃c (Q ⊗ P) + (R ⊗ P)`. -/
def sumTensorDistrib {P : PFunctor.{uA₁, uB₁}} {Q R : PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂}
      ((Q + R) ⊗ P) ((Q ⊗ P) + (R ⊗ P)) where
  toChart :=
    (fun ⟨qr, p⟩ => match qr with
      | Sum.inl q => Sum.inl (q, p)
      | Sum.inr r => Sum.inr (r, p)) ⇉
    (fun ⟨qr, _⟩ pb => match qr with
      | Sum.inl _ => pb
      | Sum.inr _ => pb)
  invChart :=
    (Sum.elim
      (fun ⟨q, p⟩ => (Sum.inl q, p))
      (fun ⟨r, p⟩ => (Sum.inr r, p))) ⇉
    (fun qprp pb => match qprp with
      | Sum.inl _ => pb
      | Sum.inr _ => pb)
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro a; rcases a with ⟨_ | _, _⟩ <;> rfl
    · intro a; funext _; rcases a with ⟨_ | _, _⟩ <;> rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro a; rcases a <;> rfl
    · intro a; funext _; rcases a <;> rfl

end Equiv

end Tensor

/-! ### Polynomial-product coherence

Even though `*` is *not* the categorical product in the chart category, it
is still a functor and admits coherent equivalences (commutativity,
associativity, units, zeros, congruence, distributivity over `+`). These
mirror the `PFunctor.Equiv.prod*` lemmas. -/

section Prod

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {W : PFunctor.{uA₄, uB₄}}

@[simp]
theorem prodMap_id :
    (Chart.id P) ×c (Chart.id Q) = Chart.id.{max uA₁ uA₂, max uB₁ uB₂} (P * Q) := by
  ext _ x
  · rfl
  · cases x <;> rfl

theorem prodMap_comp_prodMap {S : PFunctor.{uA₅, uB₅}} {T : PFunctor.{uA₆, uB₆}}
    (c₁ : Chart P R) (c₂ : Chart Q W) (c₁' : Chart R S) (c₂' : Chart W T) :
    (c₁' ×c c₂') ∘c (c₁ ×c c₂) = (c₁' ∘c c₁) ×c (c₂' ∘c c₂) := by
  refine Chart.ext _ _ ?_ ?_
  · intro _; rfl
  · intro _; funext psum; rcases psum <;> rfl

namespace Equiv

/-- Polynomial-product preserves equivalences: `P ≃c P' → Q ≃c Q' → P * Q ≃c P' * Q'`. -/
def prodCongr {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {P' : PFunctor.{uA₃, uB₃}} {Q' : PFunctor.{uA₄, uB₄}}
    (e₁ : P ≃c P') (e₂ : Q ≃c Q') :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄}
      (P * Q) (P' * Q') where
  toChart := e₁.toChart ×c e₂.toChart
  invChart := e₁.invChart ×c e₂.invChart
  left_inv := by
    rw [Chart.prodMap_comp_prodMap, e₁.left_inv, e₂.left_inv, Chart.prodMap_id]
  right_inv := by
    rw [Chart.prodMap_comp_prodMap, e₁.right_inv, e₂.right_inv, Chart.prodMap_id]

/-- Commutativity of the polynomial product. -/
def prodComm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂} (P * Q) (Q * P) where
  toChart := Prod.swap ⇉ (fun _ d => d.swap)
  invChart := Prod.swap ⇉ (fun _ d => d.swap)
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext d; rcases d <;> rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext d; rcases d <;> rfl

/-- Associativity of the polynomial product. -/
def prodAssoc :
    Chart.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃, max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}
      ((P * Q) * R) (P * (Q * R)) where
  toChart := (_root_.Equiv.prodAssoc _ _ _).toFun ⇉
    (fun _ d => (_root_.Equiv.sumAssoc _ _ _).toFun d)
  invChart := (_root_.Equiv.prodAssoc _ _ _).invFun ⇉
    (fun _ d => (_root_.Equiv.sumAssoc _ _ _).invFun d)
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext d; rcases d with d | d
      · rcases d with d | d <;> rfl
      · rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext d; rcases d with d | d
      · rfl
      · rcases d with d | d <;> rfl

/-- Polynomial-product with `0` is `0` (right). -/
def prodZero : P * 0 ≃c 0 where
  toChart := (fun a => PEmpty.elim a.2) ⇉ (fun a _ => PEmpty.elim a.2)
  invChart := PEmpty.elim ⇉ (fun a _ => PEmpty.elim a)
  left_inv := by ext ⟨_, b⟩ <;> exact PEmpty.elim b
  right_inv := by ext a <;> exact PEmpty.elim a

/-- Polynomial-product with `0` is `0` (left). -/
def zeroProd : 0 * P ≃c 0 where
  toChart := (fun a => PEmpty.elim a.1) ⇉ (fun a _ => PEmpty.elim a.1)
  invChart := PEmpty.elim ⇉ (fun a _ => PEmpty.elim a)
  left_inv := by ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by ext a <;> exact PEmpty.elim a

/-- Left distributivity of polynomial product over coproduct.

`P * (Q + R) ≃c (P * Q) + (P * R)`. -/
def prodSumDistrib {P : PFunctor.{uA₁, uB₁}} {Q R : PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂}
      (P * (Q + R)) ((P * Q) + (P * R)) where
  toChart :=
    (fun ⟨p, qr⟩ => match qr with
      | Sum.inl q => Sum.inl (p, q)
      | Sum.inr r => Sum.inr (p, r)) ⇉
    (fun ⟨_, qr⟩ d => match qr, d with
      | Sum.inl _, Sum.inl pb => Sum.inl pb
      | Sum.inl _, Sum.inr qb => Sum.inr qb
      | Sum.inr _, Sum.inl pb => Sum.inl pb
      | Sum.inr _, Sum.inr rb => Sum.inr rb)
  invChart :=
    (Sum.elim
      (fun ⟨p, q⟩ => (p, Sum.inl q))
      (fun ⟨p, r⟩ => (p, Sum.inr r))) ⇉
    (fun pqpr d => match pqpr, d with
      | Sum.inl _, Sum.inl pb => Sum.inl pb
      | Sum.inl _, Sum.inr qb => Sum.inr qb
      | Sum.inr _, Sum.inl pb => Sum.inl pb
      | Sum.inr _, Sum.inr rb => Sum.inr rb)
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro a; rcases a with ⟨_, _ | _⟩ <;> rfl
    · intro a; funext d
      rcases a with ⟨_, _ | _⟩ <;> rcases d <;> rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro a; rcases a <;> rfl
    · intro a; funext d
      rcases a <;> rcases d <;> rfl

/-- Right distributivity of polynomial product over coproduct.

`(Q + R) * P ≃c (Q * P) + (R * P)`. -/
def sumProdDistrib {P : PFunctor.{uA₁, uB₁}} {Q R : PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂}
      ((Q + R) * P) ((Q * P) + (R * P)) where
  toChart :=
    (fun ⟨qr, p⟩ => match qr with
      | Sum.inl q => Sum.inl (q, p)
      | Sum.inr r => Sum.inr (r, p)) ⇉
    (fun ⟨qr, _⟩ d => match qr, d with
      | Sum.inl _, Sum.inl qb => Sum.inl qb
      | Sum.inl _, Sum.inr pb => Sum.inr pb
      | Sum.inr _, Sum.inl rb => Sum.inl rb
      | Sum.inr _, Sum.inr pb => Sum.inr pb)
  invChart :=
    (Sum.elim
      (fun ⟨q, p⟩ => (Sum.inl q, p))
      (fun ⟨r, p⟩ => (Sum.inr r, p))) ⇉
    (fun qprp d => match qprp, d with
      | Sum.inl _, Sum.inl qb => Sum.inl qb
      | Sum.inl _, Sum.inr pb => Sum.inr pb
      | Sum.inr _, Sum.inl rb => Sum.inl rb
      | Sum.inr _, Sum.inr pb => Sum.inr pb)
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro a; rcases a with ⟨_ | _, _⟩ <;> rfl
    · intro a; funext d
      rcases a with ⟨_ | _, _⟩ <;> rcases d <;> rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro a; rcases a <;> rfl
    · intro a; funext d
      rcases a <;> rcases d <;> rfl

end Equiv

end Prod

/-! ### ULift -/

namespace Equiv

/-- ULift equivalence for charts. -/
def ulift {P : PFunctor.{uA, uB}} : P.ulift ≃c P where
  toChart := (fun a => ULift.down a) ⇉ (fun _ b => ULift.down b)
  invChart := (fun a => ULift.up a) ⇉ (fun _ b => ULift.up b)
  left_inv := rfl
  right_inv := rfl

end Equiv

end Chart

namespace Equiv

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

/-- Convert an equivalence between two polynomial functors `P` and `Q` to a chart. -/
def toChart (e : P ≃ₚ Q) : Chart P Q where
  toFunA := e.equivA
  toFunB := fun a => e.equivB a

/-! ### Bridge `PFunctor.Equiv → Chart.Equiv`

Every polynomial-functor equivalence yields a chart equivalence: the forward
chart uses `e.equivA` / `e.equivB`, and the inverse chart uses their symmetric
counterparts. The proofs of `left_inv` / `right_inv` need the cast
machinery from `forward_equivB_roundtrip` / `reverse_equivB_roundtrip` because
`e.symm.equivA (e.equivA a)` and `a` are only propositionally equal.

This is the chart analogue of `Equiv.toLensEquiv` and is the standard way to
derive sigma / distributivity equivalences from their `PFunctor.Equiv`
counterparts. -/

private theorem eqRec_id_apply_codomain
    {α : Sort*} {β : α → Sort*} {a₀ a₁ : α}
    (h : a₀ = a₁) (x : β a₀) :
    Eq.rec (motive := fun x _ => β a₀ → β x) id h x =
      _root_.cast (congrArg β h) x := by
  subst h; rfl

@[simp]
theorem symm_toChart_comp_toChart (e : P ≃ₚ Q) :
    e.symm.toChart ∘c e.toChart = Chart.id P := by
  refine Chart.ext _ _ (fun a => e.equivA.symm_apply_apply a) (fun a => ?_)
  funext b
  simp only [Chart.comp, Chart.id, toChart, Function.comp_apply]
  rw [forward_equivB_roundtrip]
  exact (eqRec_id_apply_codomain (e.equivA.symm_apply_apply a).symm b).symm

@[simp]
theorem toChart_comp_symm_toChart (e : P ≃ₚ Q) :
    e.toChart ∘c e.symm.toChart = Chart.id Q := by
  refine Chart.ext _ _ (fun a => e.equivA.apply_symm_apply a) (fun a => ?_)
  funext b
  simp only [Chart.comp, Chart.id, toChart, Function.comp_apply]
  change e.equivB (e.equivA.symm a) (e.symm.equivB a b) = _
  rw [reverse_equivB_roundtrip]
  exact (eqRec_id_apply_codomain (e.equivA.apply_symm_apply a).symm b).symm

/-- Convert an equivalence between two polynomial functors to a chart equivalence.

Chart-side analogue of `Equiv.toLensEquiv`. Together with `Chart.Equiv.refl`,
`symm`, and `trans`, this establishes a faithful functor
`PFunctor.Equiv → Chart.Equiv`. -/
def toChartEquiv (e : P ≃ₚ Q) : P ≃c Q where
  toChart := e.toChart
  invChart := e.symm.toChart
  left_inv := symm_toChart_comp_toChart e
  right_inv := toChart_comp_symm_toChart e

end Equiv

/-! ### Sigma equivalences

These are derived from `PFunctor.Equiv.toChartEquiv` applied to the
corresponding `PFunctor.Equiv` constructions. They mirror the
`PFunctor.Lens.Equiv.sigma*` family. -/

namespace Chart.Equiv

variable {I : Type v}

/-- Sigma of an empty family is the zero functor. -/
def sigmaEmpty [IsEmpty I] {F : I → PFunctor.{uA, uB}} : sigma F ≃c 0 :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.emptySigma (F := F))

/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself
    (up to `ulift`). -/
def sigmaUnit {F : PUnit → PFunctor.{uA, uB}} : sigma F ≃c (F PUnit.unit).ulift :=
  PFunctor.Equiv.toChartEquiv
    (PFunctor.Equiv.trans
      (PFunctor.Equiv.punitSigma (F := F))
      (PFunctor.Equiv.uliftEquiv (P := F PUnit.unit)))

/-- Sigma of a unique-indexed family is equivalent to the default fiber
    (up to `ulift`). -/
def sigmaOfUnique [Unique I] {F : I → PFunctor.{uA, uB}} : sigma F ≃c (F default).ulift :=
  PFunctor.Equiv.toChartEquiv
    (PFunctor.Equiv.trans
      (PFunctor.Equiv.uniqueSigma (F := F))
      (PFunctor.Equiv.uliftEquiv (P := F default)))

/-- Left distributivity of polynomial product over sigma. -/
def prodSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂ v, max uB₁ uB₂, max uA₁ uA₂ v, max uB₁ uB₂}
      (P * sigma F) (sigma (fun i => (P * F i : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}))) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.prodSigmaDistrib (P := P) (F := F))

/-- Right distributivity of polynomial product over sigma. -/
def sigmaProdDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂ v, max uB₁ uB₂, max uA₁ uA₂ v, max uB₁ uB₂}
      (sigma F * P) (sigma (fun i => (F i * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}))) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.sigmaProdDistrib (P := P) (F := F))

/-- Left distributivity of tensor product over sigma. -/
def tensorSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    P ⊗ sigma F ≃c sigma (fun i => P ⊗ F i) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.tensorSigmaDistrib (P := P) (F := F))

/-- Right distributivity of tensor product over sigma. -/
def sigmaTensorDistrib {P : PFunctor.{uA₂, uB₂}} {F : I → PFunctor.{uA₁, uB₁}} :
    sigma F ⊗ P ≃c sigma (fun i => F i ⊗ P) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.sigmaTensorDistrib (F := F) (P := P))

/-! ### Pi equivalences

`piMap` lives in the operations section, but unlike lenses, charts admit
no `piForall` (Pi-elimination requires direction-contravariance). What we
get cleanly here is `piUnit` and `piZero`. -/

/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def piUnit {P : PFunctor.{uA, uB}} : pi (fun (_ : PUnit) => P) ≃c P where
  toChart := (fun f => f PUnit.unit) ⇉ (fun _ s => s.2)
  invChart := (fun pa _ => pa) ⇉ (fun _ pb => ⟨PUnit.unit, pb⟩)
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro f; funext u; cases u; rfl
    · intro f; funext ⟨u, pb⟩; cases u; rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext _; rfl

/-- Pi of a family of zero functors over an inhabited type is the zero functor. -/
def piZero [Inhabited I] {F : I → PFunctor.{uA, uB}} (F_zero : ∀ i, F i = 0) :
    pi F ≃c 0 := by
  letI : IsEmpty (pi F).A := by
    refine ⟨fun f => ?_⟩
    have hf : (F default).A := f default
    rw [F_zero (default : I)] at hf
    exact hf.elim
  refine
    { toChart := isEmptyElim ⇉ (fun a _ => isEmptyElim a)
      invChart := PEmpty.elim ⇉ (fun a _ => PEmpty.elim a)
      left_inv := by
        refine Chart.ext _ _ ?_ ?_
        · intro a; exact isEmptyElim a
        · intro a; exact isEmptyElim a
      right_inv := by
        refine Chart.ext _ _ ?_ ?_
        · intro a; exact PEmpty.elim a
        · intro a; exact PEmpty.elim a }

end Chart.Equiv

end PFunctor
