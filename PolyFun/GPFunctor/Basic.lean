/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Basic

/-!
# Graded Polynomial Functors

This file defines `GPFunctor G`, a polynomial functor whose shapes carry grades in a type `G`:
a plain container `(A, B)` together with a labeling `grade : A → G`. Grading is **per shape**:
the grade depends only on the chosen position `a : A`, never on the response `b : B a`. This
matches the graded-theories literature, where each operation of a graded signature carries a
single grade, and contrasts with the response-dependent source map `src` of
[`IPFunctor`](../IPFunctor/Basic.lean).

No algebraic structure on `G` is required by the structure itself (mirroring how `IPFunctor`
puts no structure on its index types); `[Mul G]` / `[One G]` / `[Monoid G]` hypotheses appear
only on the constructions that need them. In particular the free graded monad on a
`GPFunctor G` — trees whose grades multiply along sequencing — lives in
[`PolyFun/GPFunctor/Free/Basic.lean`](Free/Basic.lean) and requires `[Monoid G]`; the
`GradedMonad` class it instantiates lives in
[`PolyFun/Control/Monad/Graded.lean`](../Control/Monad/Graded.lean).

## Connection to indexed polynomial functors

Over `[Mul G]`, a graded polynomial induces a state-indexed polynomial on `G` itself:
`toIPFunctor` has constant shape family `P.A` and source map `src g a b := g * P.grade a`,
reading the state as the *accumulated* grade. Because the grade is per-shape, the source map
is independent of the response — formally, `P.toIPFunctor` satisfies
`IPFunctor.DeterministicTransitions`. Per-shape grading thus embeds into the
deterministic-transitions fragment of the indexed theory.

## No composition product

Unlike `PFunctor` and `IPFunctor`, there is no composition `Q ◃ P` of graded polynomials:
a composite position `⟨a, f⟩` would have to carry the grade `Q.grade a * P.grade (f b)`,
which varies with the response `b` — per-shape grading is not closed under composition.
The composite does exist on the indexed images (`Q.toIPFunctor ◃ P.toIPFunctor`).

## Pointers

* The free graded monad `GFreeM` and its `GradedMonad` / `LawfulGradedMonad` instances live
  in [`PolyFun/GPFunctor/Free/Basic.lean`](Free/Basic.lean); its translation into the
  two-index indexed free monad lives in
  [`PolyFun/GPFunctor/Free/Indexed.lean`](Free/Indexed.lean).
* Graded lenses, charts, and structural equivalences (each carrying a grade-preservation
  law) live in [`PolyFun/GPFunctor/Lens/Basic.lean`](Lens/Basic.lean),
  [`PolyFun/GPFunctor/Chart/Basic.lean`](Chart/Basic.lean), and
  [`PolyFun/GPFunctor/Equiv/Basic.lean`](Equiv/Basic.lean).
-/

@[expose] public section

universe uG uH uA uB v

/-- A graded polynomial functor over a grading type `G`: a container `(A, B)` together with
a per-shape grade. The grade of a position is independent of the response, so a `GPFunctor`
is exactly a `PFunctor` whose shapes are labeled by `G`. -/
structure GPFunctor (G : Type uG) extends PFunctor.{uA, uB} where
  /-- The grade in `G` of each shape. -/
  grade : A → G

namespace GPFunctor

variable {G : Type uG} {H : Type uH}

/-! ## Basic instances -/

/-- The zero `GPFunctor`: no shapes (and hence no grades to assign). -/
instance (G : Type uG) : Zero (GPFunctor.{uG, uA, uB} G) where
  zero := { A := PEmpty, B := fun _ => PEmpty, grade := PEmpty.elim }

/-- The unit `GPFunctor`: a single shape at the trivial grade, with no continuation. -/
instance (G : Type uG) [One G] : One (GPFunctor.{uG, uA, uB} G) where
  one := { A := PUnit, B := fun _ => PEmpty, grade := fun _ => 1 }

instance : Inhabited (GPFunctor G) := ⟨0⟩

@[simp] lemma toPFunctor_zero :
    (0 : GPFunctor.{uG, uA, uB} G).toPFunctor = 0 := rfl

@[simp] lemma toPFunctor_one [One G] :
    (1 : GPFunctor.{uG, uA, uB} G).toPFunctor = 1 := rfl

@[simp] lemma grade_one [One G] (a : (1 : GPFunctor.{uG, uA, uB} G).A) :
    (1 : GPFunctor.{uG, uA, uB} G).grade a = 1 := rfl

/-! ## Constructors -/

/-- The graded monomial: head type `A`, constant response type `B`, every shape at grade `g`.
The underlying container is `PFunctor.monomial A B`. -/
def monomial (g : G) (A : Type uA) (B : Type uB) : GPFunctor.{uG, uA, uB} G where
  A := A
  B _ := B
  grade _ := g

@[simp] lemma toPFunctor_monomial (g : G) (A : Type uA) (B : Type uB) :
    (monomial g A B).toPFunctor = PFunctor.monomial A B := rfl

@[simp] lemma grade_monomial (g : G) (A : Type uA) (B : Type uB) (a : A) :
    (monomial g A B).grade a = g := rfl

/-- The graded variable `X`: a unique shape at the trivial grade with a single response.
The underlying container is the identity polynomial `PFunctor.X`. -/
@[reducible] def X [One G] : GPFunctor.{uG, uA, uB} G where
  A := PUnit
  B _ := PUnit
  grade _ := 1

@[simp] lemma toPFunctor_X [One G] :
    (X : GPFunctor.{uG, uA, uB} G).toPFunctor = PFunctor.X := rfl

@[simp] lemma grade_X [One G] (a : (X : GPFunctor.{uG, uA, uB} G).A) :
    (X : GPFunctor.{uG, uA, uB} G).grade a = 1 := rfl

/-- View a plain polynomial functor as a graded polynomial with every shape at the trivial
grade. A section of the grade-forgetting projection `toPFunctor`. -/
def ofPFunctor [One G] (P : PFunctor.{uA, uB}) : GPFunctor.{uG, uA, uB} G :=
  { P with grade := fun _ => 1 }

@[simp] lemma toPFunctor_ofPFunctor [One G] (P : PFunctor.{uA, uB}) :
    (ofPFunctor (G := G) P).toPFunctor = P := rfl

@[simp] lemma grade_ofPFunctor [One G] (P : PFunctor.{uA, uB}) (a : P.A) :
    (ofPFunctor (G := G) P).grade a = 1 := rfl

/-! ## Homogeneous components -/

/-- The grade-`g` homogeneous component of the action of `P` on a type `X`: positions are
shapes of grade exactly `g`. The full (grade-forgetting) action is `P.toPFunctor.Obj`. -/
def Obj (P : GPFunctor.{uG, uA, uB} G) (g : G) (X : Type v) : Type (max uA uB v) :=
  Σ a : { a : P.A // P.grade a = g }, P.B a.1 → X

/-- The homogeneous components decompose the full grade-forgetting action: a grade together
with a position of exactly that grade is the same data as a bare position of the underlying
container. -/
def sigmaObjEquiv (P : GPFunctor.{uG, uA, uB} G) (X : Type v) :
    (Σ g : G, P.Obj g X) ≃ P.toPFunctor.Obj X where
  toFun x := ⟨x.2.1.1, x.2.2⟩
  invFun y := ⟨P.grade y.1, ⟨y.1, rfl⟩, y.2⟩
  left_inv := fun ⟨g, ⟨a, h⟩, f⟩ => by subst h; rfl
  right_inv y := rfl

/-! ## Grade reindexing -/

/-- Relabel the grades of a graded polynomial along a function `φ : G → H`. The underlying
container is unchanged. No multiplicative structure is involved at this level; the
`MonoidHom`-aware action on the free graded monad lives in
[`PolyFun/GPFunctor/Free/MapGrade.lean`](Free/MapGrade.lean). -/
def mapGrade (φ : G → H) (P : GPFunctor.{uG, uA, uB} G) : GPFunctor.{uH, uA, uB} H where
  A := P.A
  B := P.B
  grade := φ ∘ P.grade

@[simp] lemma mapGrade_id (P : GPFunctor.{uG, uA, uB} G) :
    P.mapGrade id = P := rfl

@[simp] lemma mapGrade_mapGrade {K : Type*} (φ : G → H) (ψ : H → K)
    (P : GPFunctor.{uG, uA, uB} G) :
    (P.mapGrade φ).mapGrade ψ = P.mapGrade (ψ ∘ φ) := rfl

@[simp] lemma toPFunctor_mapGrade (φ : G → H) (P : GPFunctor.{uG, uA, uB} G) :
    (P.mapGrade φ).toPFunctor = P.toPFunctor := rfl

@[simp] lemma grade_mapGrade (φ : G → H) (P : GPFunctor.{uG, uA, uB} G) (a : P.A) :
    (P.mapGrade φ).grade a = φ (P.grade a) := rfl

/-! ## Connection to indexed polynomial functors -/

/-- View a graded polynomial as a state-indexed polynomial over `G` itself: from accumulated
grade `g`, taking shape `a` lands every response at `g * P.grade a`. The shape and response
families are constant in the state.

Because the grade is per-shape, the source map is independent of the response; see the
`IPFunctor.DeterministicTransitions` instance below. -/
def toIPFunctor [Mul G] (P : GPFunctor.{uG, uA, uB} G) : IPFunctor.Endo.{uG, uA, uB} G where
  A _ := P.A
  B _ a := P.B a
  src g a _ := g * P.grade a

@[simp] lemma toIPFunctor_A [Mul G] (P : GPFunctor.{uG, uA, uB} G) (g : G) :
    P.toIPFunctor.A g = P.A := rfl

@[simp] lemma toIPFunctor_B [Mul G] (P : GPFunctor.{uG, uA, uB} G) (g : G) (a : P.A) :
    P.toIPFunctor.B g a = P.B a := rfl

@[simp] lemma toIPFunctor_src [Mul G] (P : GPFunctor.{uG, uA, uB} G) (g : G) (a : P.A)
    (b : P.B a) :
    P.toIPFunctor.src g a b = g * P.grade a := rfl

/-- Per-shape grading makes the induced indexed transitions deterministic: the source index
`g * P.grade a` does not depend on the response. This instance is the formal content of
"per-shape grading embeds into the deterministic-transitions fragment of `IPFunctor`". -/
instance [Mul G] (P : GPFunctor.{uG, uA, uB} G) :
    IPFunctor.DeterministicTransitions P.toIPFunctor where
  next g a := g * P.grade a
  spec _ _ _ := rfl

end GPFunctor
