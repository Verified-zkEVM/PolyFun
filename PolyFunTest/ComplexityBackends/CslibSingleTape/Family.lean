/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Family

/-!
# The single-tape backend's families as generic families

`EncPolyTimeFam` and `FamRealizer` over the single-tape backend are the same structure: the round
trips hold by reflexivity, composition agrees member by member, and the finite-table primitive is
the finite-table machine.
-/

public section

open PFunctor PFunctor.QuantitativeStepClass.DescriptionMeasure
open ComplexityBackends.CslibSingleTape

namespace PolyFunTest.ComplexityBackends.CslibSingleTape.Family

variable {D E F : ℕ → Type} {ea : ∀ n, D n → List Bool} {eb : ∀ n, E n → List Bool}
  {ec : ∀ n, F n → List Bool} {f : ∀ n, D n → E n} {g : ∀ n, E n → F n}

example (h : EncPolyTimeFam ea eb f) : EncPolyTimeFam.ofFam h.toFam = h :=
  EncPolyTimeFam.ofFam_toFam h

example (X : Backend.description.FamRealizer Backend.polynomialBackend ea eb f) :
    (EncPolyTimeFam.ofFam X).toFam = X :=
  EncPolyTimeFam.toFam_ofFam X

/-- Generic composition of two backend families is per-parameter machine composition. -/
example (h : EncPolyTimeFam ea eb f) (h' : EncPolyTimeFam eb ec g) (n : ℕ) :
    (h.toFam.comp h'.toFam).wit n = (h.wit n).comp (h'.wit n) :=
  FamRealizer.wit_comp h.toFam h'.toFam n

/-- The generic composite's uniform time bound is the first machine's plus the second's at the
output envelope: this backend contributes no composition overhead, so the second machine's
polynomial appears once. -/
example (h : EncPolyTimeFam ea eb f) (h' : EncPolyTimeFam eb ec g) :
    (h.toFam.comp h'.toFam).time =
      h.time + h'.time.comp (Polynomial.X + (1 + Polynomial.X + h.time)) + 0 :=
  FamRealizer.time_comp h.toFam h'.toFam

/-- The generic composite's advice bound adds. -/
example (h : EncPolyTimeFam ea eb f) (h' : EncPolyTimeFam eb ec g) :
    (h.toFam.comp h'.toFam).desc = h.size + h'.size :=
  FamRealizer.desc_comp h.toFam h'.toFam

/-- The finite-table primitive is the finite-table machine. -/
example {A B : Type} [Fintype A] (a : A → List Bool) (ha : Function.Injective a)
    (b : B → List Bool) (f : A → B) :
    Backend.finiteTables.table a ha b f = EncPolyTime.ofFintype a ha b f :=
  rfl

/-- The canonical polynomial of a witness is its certified time. -/
example {A B : Type} {a : A → List Bool} {b : B → List Bool} {f : A → B}
    (r : EncPolyTime a b f) : Backend.polynomialBackend.timeOf r = r.time :=
  Backend.timeOf_eq r

/-! ## Composition certificates depend on association -/

/-- One fixed identity machine at every parameter. -/
@[expose] noncomputable def identityFamily :
    Backend.description.FamRealizer Backend.polynomialBackend
      (fun _ (_ : Unit) ↦ []) (fun _ (_ : Unit) ↦ []) (fun _ ↦ id) :=
  FamRealizer.id Backend.polynomialBackend _

/-- The same machines with a deliberately looser linear time certificate. -/
@[expose] noncomputable def linearIdentityFamily :
    Backend.description.FamRealizer Backend.polynomialBackend
      (fun _ (_ : Unit) ↦ []) (fun _ (_ : Unit) ↦ []) (fun _ ↦ id) :=
  identityFamily.weaken (1 + Polynomial.X) 1
    (fun _ ↦ by simp [identityFamily, Backend.polynomialBackend])
    (fun _ ↦ by simp [identityFamily, Backend.polynomialBackend])

/-- Both associations are valid realizers of identity, but their time certificates differ. -/
example :
    ((identityFamily.comp identityFamily).comp linearIdentityFamily).time.eval 0 = 6 ∧
      (identityFamily.comp (identityFamily.comp linearIdentityFamily)).time.eval 0 = 9 := by
  norm_num [identityFamily, linearIdentityFamily, FamRealizer.comp, FamRealizer.weaken,
    FamRealizer.id, Backend.polynomialBackend]

end PolyFunTest.ComplexityBackends.CslibSingleTape.Family
