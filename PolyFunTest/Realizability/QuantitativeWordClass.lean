/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.WordClass

/-!
# Quantitative word-class checks

Compile-time checks for the generic adapter from word-level executable code to quantitative
realizability.
-/

public section

universe u v

namespace PFunctor.StepClass.QuantitativeWordClassTest

variable {W : Type u} {V : WordClass W} (Q : QuantitativeWordClass.{u, v} V)

#check Q.toQuantitativeStepClass
#check QuantitativeWordClass.HasCategory
#check QuantitativeWordClass.HasExactCategory
#check QuantitativeWordClass.toHasCategory
#check QuantitativeWordClass.toHasExactCategory

section Category

variable [Q.HasCategory] [Q.HasExactCategory]

#check Q.identity
#check Q.compose
#check Q.composeOverhead
#check Q.toHasCategory
#check Q.toHasExactCategory

end Category

example {A B : Type u} {a : V.toStepClass.Str A} {b : V.toStepClass.Str B}
    {f : A → B} (code : QuantitativeWordClass.Realizer Q a b f) :
    V.toStepClass.Hom a b f :=
  code.toHom

end PFunctor.StepClass.QuantitativeWordClassTest
