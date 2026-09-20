/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Counting

/-!
# Description measures through ordinary imports

`RealizableLE` is opaque; `mem_realizableLE` is the membership API, and the counting separation is
applied by naming its threshold hypotheses. These spellings are what a backend in another package
uses.
-/

@[expose] public section

universe u v w x

namespace PolyFunTest.ModuleAPI.Realizability

open PFunctor PFunctor.QuantitativeStepClass Filter

variable {C : StepClass.{u, v}} {Q : QuantitativeStepClass.{u, v, w} C}
  {Faithful : ∀ {B : Type u}, C.Str B → Prop} (M : Q.DescriptionMeasure Faithful)

example {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B} (r : Q.Realizer a b f)
    (h : M.descSize r ≤ 3) : f ∈ M.RealizableLE a b 3 :=
  M.mem_realizableLE.mpr ⟨r, h⟩

example {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B} (h : f ∈ M.RealizableLE a b 3) :
    f ∈ M.RealizableLE a b 5 :=
  M.realizableLE_mono (by norm_num) h

example {D E : ℕ → Type u} [∀ n, Fintype (D n)] (a : ∀ n, C.Str (D n)) (b : ∀ n, C.Str (E n))
    (ι : ∀ n, Bool → E n) (hι : ∀ n, Function.Injective (ι n)) (hb : ∀ n, Faithful (b n))
    (ht_count : ∀ᶠ n in atTop,
      Fintype.card (M.Desc (a n) (b n) (2 ^ (n / 4))) < 2 ^ Fintype.card (D n)) :
    ∃ f : (n : ℕ) → D n → Bool, ¬ ∃ q : Polynomial ℕ,
      ∀ᶠ n in atTop, (ι n ∘ f n) ∈ M.RealizableLE (a n) (b n) (q.eval n) :=
  M.exists_not_realizableLE_poly_of_card_lt a b ι hι hb ht_count

end PolyFunTest.ModuleAPI.Realizability
