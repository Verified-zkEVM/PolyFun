/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Complexity
import ComplexityBackends
import PolyFun
import PolyFunComplexitylib

/-!
# Joint import of PolyFun and all of complexitylib

Elaborating this module checks that no declaration is defined twice across PolyFun, its
complexity backends, this package and the whole of complexitylib. Both libraries extend the shared
`Cslib.Turing.SingleTapeTM`, `Cslib.Turing.BiTape`, `Cslib.IsMonadHom` and `Relation`
namespaces.

PolyFun's resource polynomials live in the root `Complexity` namespace, while complexitylib's
classes live in `Cslib.Complexity`. With `Cslib` open, the qualified names below still resolve to
PolyFun's declarations.
-/

open Cslib

example : Complexity.FirstOrderPolynomial = Complexity.SecondOrderPolynomial PEmpty := rfl

example (n : ℕ) : (Complexity.FirstOrderPolynomial.input).eval n = n := rfl
