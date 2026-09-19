/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Image

/-!
# Description measures on quantitative realizers

A `QuantitativeStepClass` measures the size of values and the cost of runs but says nothing about
how large a piece of code is. `DescriptionMeasure` adds that third measure: a description size on
realizers together with, at every size bound and every pair of representations, a finite type of
canonical descriptions, such that a realizer within the bound has a description and two realizers
with the same description compute the same function whenever the codomain representation is
*faithful*.

Faithfulness is a parameter of the measure, not a field of the representation. For raw string
encodings it is injectivity. A consumer that leaves it unsatisfiable obtains a measure that proves
nothing: the counting separation in `PolyFun.Realizability.Quantitative.Counting` demands
faithfulness at every boundary it separates, and the regression tests record both the trivial
measure under an unsatisfiable predicate and the impossibility of any measure for the
everything-is-free backend under a trivial one.

The description type is indexed by the two representations so that backends whose realizers have
boundary-dependent shapes, such as circuits of a fixed width, count descriptions per boundary.
Nothing here mentions cost, time, or categorical structure.
-/

public section

universe u v w x

namespace PFunctor.QuantitativeStepClass

variable {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C)

/-- An abstract description-size measure on realizers with finite canonical descriptions at each
size bound and each pair of representations. Against a faithful codomain representation, a
description determines the realized function. -/
structure DescriptionMeasure (Faithful : ∀ {B : Type u}, C.Str B → Prop) where
  /-- Description size (program size) of a realizer. -/
  descSize : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}, Q.Realizer a b f → ℕ
  /-- Canonical descriptions of realizers between two representations, at a size bound. -/
  Desc : ∀ {A B : Type u}, C.Str A → C.Str B → ℕ → Type x
  /-- There are finitely many canonical descriptions at each bound. -/
  descFintype : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (d : ℕ), Fintype (Desc a b d)
  /-- Every realizer within a size bound has a canonical description at that bound. -/
  describe : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B} (r : Q.Realizer a b f)
    {d : ℕ}, descSize r ≤ d → Desc a b d
  /-- Against a faithful codomain representation, the description determines the function. -/
  describe_determines : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B}, Faithful b →
    ∀ {f f' : A → B} (r : Q.Realizer a b f) (r' : Q.Realizer a b f') {d : ℕ}
      (h : descSize r ≤ d) (h' : descSize r' ≤ d), describe r h = describe r' h' → f = f'

namespace DescriptionMeasure

variable {Q} {Faithful : ∀ {B : Type u}, C.Str B → Prop}
  (M : Q.DescriptionMeasure Faithful)

instance instFintypeDesc {A B : Type u} (a : C.Str A) (b : C.Str B) (d : ℕ) :
    Fintype (M.Desc a b d) :=
  M.descFintype a b d

/-- The functions realizable at description size at most `d` between pinned representations. -/
def RealizableLE {A B : Type u} (a : C.Str A) (b : C.Str B) (d : ℕ) : Set (A → B) :=
  {f | ∃ r : Q.Realizer a b f, M.descSize r ≤ d}

/-- Membership in `RealizableLE` is witnessed by a realizer within the description bound. -/
theorem mem_realizableLE {A B : Type u} {a : C.Str A} {b : C.Str B} {d : ℕ} {f : A → B} :
    f ∈ M.RealizableLE a b d ↔ ∃ r : Q.Realizer a b f, M.descSize r ≤ d :=
  Iff.rfl

/-- Realizability at a larger description size is a weaker requirement. -/
theorem realizableLE_mono {A B : Type u} {a : C.Str A} {b : C.Str B} {d d' : ℕ}
    (h : d ≤ d') : M.RealizableLE a b d ⊆ M.RealizableLE a b d' := by
  rintro f ⟨r, hr⟩
  exact ⟨r, hr.trans h⟩

/-- Against a faithful codomain representation, the functions realizable at description size at
most `d` are covered by a finite set of cardinality at most the number of canonical descriptions:
each description determines at most one realized function. -/
theorem exists_realizableLE_covering {A B : Type u} (a : C.Str A) {b : C.Str B}
    (hb : Faithful b) (d : ℕ) :
    ∃ s : Finset (A → B),
      M.RealizableLE a b d ⊆ ↑s ∧ s.card ≤ Fintype.card (M.Desc a b d) := by
  classical
  let Described : Set (M.Desc a b d) :=
    {t | ∃ (f : A → B) (r : Q.Realizer a b f) (h : M.descSize r ≤ d), M.describe r h = t}
  let pick : Described → (A → B) := fun t ↦ t.2.choose
  refine ⟨Finset.univ.image pick, ?_, ?_⟩
  · rintro f ⟨r, hr⟩
    have ht : M.describe r hr ∈ Described := ⟨f, r, hr, rfl⟩
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨_, ht⟩, Finset.mem_univ _, ?_⟩)
    obtain ⟨r', hr', heq⟩ := ht.choose_spec
    exact M.describe_determines hb r' r hr' hr heq
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ]
    exact Fintype.card_subtype_le _

end DescriptionMeasure

end PFunctor.QuantitativeStepClass
