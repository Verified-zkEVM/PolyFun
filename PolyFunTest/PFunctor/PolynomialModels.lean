/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Slice
public import PolyFun.PFunctor.NaturalModel

/-!
# Dependent sums and products of polynomials, and natural models

Examples for `PolyFun.PFunctor.Slice` (every polynomial functor is the polynomial of its total
projection) and `PolyFun.PFunctor.NaturalModel` (Σ- and Π-codes of a universe are Σ- and
Π-structures, and the code of the structure is the code of the codes).
-/

@[expose] public section

namespace PolyFunTest.PolynomialModels

open PFunctor

/-- Every polynomial functor is the polynomial of the projection of its total space. -/
example (P : PFunctor.{0, 0}) : P ≃ₚ Slice.ofMap (Sigma.fst : (Σ a, P.B a) → P.A) :=
  Slice.equivOfMapFst P

/-- The universe of finite types, `El n = Fin n`. -/
abbrev El : ℕ → Type := Fin

/-- Σ-codes of a universe are its Σ-structures. -/
example : NaturalModel.SigmaCodes El ≃ NaturalModel.SigmaStructure El :=
  NaturalModel.sigmaCodesEquiv El

/-- The code of the Σ-structure of Σ-codes is the code of the dependent sum. -/
example (c : NaturalModel.SigmaCodes El) (a : ℕ) (b : Fin a → ℕ) :
    (NaturalModel.sigmaCodesEquiv El c).toFunA ⟨a, b⟩ = c.sig a b :=
  rfl

/-- Π-codes of a universe are its Π-structures. -/
example : NaturalModel.PiCodes El ≃ NaturalModel.PiStructure El :=
  NaturalModel.piCodesEquiv El

end PolyFunTest.PolynomialModels
