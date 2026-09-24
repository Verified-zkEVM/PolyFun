/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Realizability.Quantitative.Polynomial
public import PolyFun.Realizability.Quantitative.WordClass

/-!
# Deprecated names of the quantitative composition API

The executable identity-and-composition interface of a quantitative backend is
`QuantitativeStepClass.HasComposition`, with exact refinement `HasExactComposition`, bundled
exact data `ExactComposition` and polynomial bounds `PolynomialComposition`; the word-level
interface uses the same names. These canaries pin that the earlier names still elaborate to the
same structures and report their replacements.
-/

@[expose] public section

universe u v w

namespace PFunctor.QuantitativeStepClass

variable {C : StepClass.{u, v}} {Q : QuantitativeStepClass.{u, v, w} C}

/--
warning: `PFunctor.QuantitativeStepClass.HasCategory` has been deprecated: Use `PFunctor.QuantitativeStepClass.HasComposition` instead
---
warning: `PFunctor.QuantitativeStepClass.HasCategory.identity` has been deprecated: Use `PFunctor.QuantitativeStepClass.HasComposition.identity` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.identity` to `HasComposition.identity x`).

Hint: Replace the deprecated name:
  H̵a̵s̵C̵a̵t̵e̵g̵o̵r̵y̵.̵i̵d̵e̵n̵t̵i̵t̵y̵H̲a̲s̲C̲o̲m̲p̲o̲s̲i̲t̲i̲o̲n̲.̲i̲d̲e̲n̲t̲i̲t̲y̲
-/
#guard_msgs in
example [Q.HasCategory] {A : Type u} (a : C.Str A) :
    Q.identity a = HasCategory.identity a := rfl

/--
warning: `PFunctor.QuantitativeStepClass.ExactCategory` has been deprecated: Use `PFunctor.QuantitativeStepClass.ExactComposition` instead
---
warning: `PFunctor.QuantitativeStepClass.HasExactCategory` has been deprecated: Use `PFunctor.QuantitativeStepClass.HasExactComposition` instead
---
warning: `PFunctor.QuantitativeStepClass.ExactCategory.toHasExactCategory` has been deprecated: Use `PFunctor.QuantitativeStepClass.ExactComposition.toHasExactComposition` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.toHasExactCategory` to `ExactComposition.toHasExactComposition x`).

Hint: Replace the deprecated name:
  E̵x̵a̵c̵t̵C̵a̵t̵e̵g̵o̵r̵y̵.̵t̵o̵H̵a̵s̵E̵x̵a̵c̵t̵C̵a̵t̵e̵g̵o̵r̵y̵E̲x̲a̲c̲t̲C̲o̲m̲p̲o̲s̲i̲t̲i̲o̲n̲.̲t̲o̲H̲a̲s̲E̲x̲a̲c̲t̲C̲o̲m̲p̲o̲s̲i̲t̲i̲o̲n̲
-/
#guard_msgs in
example (data : Q.ExactCategory) :
    letI := data.toHasComposition
    Q.HasExactCategory := ExactCategory.toHasExactCategory data

/--
warning: `PFunctor.QuantitativeStepClass.PolynomialCategory` has been deprecated: Use `PFunctor.QuantitativeStepClass.PolynomialComposition` instead
-/
#guard_msgs in
example [Q.HasComposition] (bounds : Q.PolynomialCategory) {A : Type u} (a : C.Str A) :
    Q.PolyRealizer a a id := PolyRealizer.identity bounds a

end PFunctor.QuantitativeStepClass

namespace PFunctor.StepClass

variable {W : Type u} {V : WordClass W} {Q : QuantitativeWordClass.{u, v} V}

/--
warning: `PFunctor.StepClass.QuantitativeWordClass.HasCategory` has been deprecated: Use `PFunctor.StepClass.QuantitativeWordClass.HasComposition` instead
---
warning: `PFunctor.StepClass.QuantitativeWordClass.toHasCategory` has been deprecated: Use `PFunctor.StepClass.QuantitativeWordClass.toHasComposition` instead
-/
#guard_msgs in
example [Q.HasCategory] : Q.toQuantitativeStepClass.HasComposition := Q.toHasCategory

end PFunctor.StepClass
