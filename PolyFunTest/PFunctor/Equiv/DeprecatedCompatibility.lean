/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Equiv.Basic

/-!
# Direct-import compatibility for the former `X` equivalence API

These canaries import only `PFunctor.Equiv.Basic`. They ensure downstream files
using the `@[simps]` lemmas generated for the former `tensorX` and `xTensor`
names keep elaborating without relying on an aggregate import.
-/

@[expose] public section

open scoped PFunctor

namespace PFunctor.Equiv

set_option linter.deprecated false in
example (P : PFunctor.{0, 0}) :
    (tensorX.{0, 0, 0, 0} P).equivA = _root_.Equiv.prodPUnit P.A :=
  tensorX_equivA.{0, 0, 0, 0} P

set_option linter.deprecated false in
example (P : PFunctor.{0, 0}) (a : (P ⊗ X).A) :
    (tensorX.{0, 0, 0, 0} P).equivB a = _root_.Equiv.prodPUnit (P.B a.1) :=
  tensorX_equivB.{0, 0, 0, 0} P a

set_option linter.deprecated false in
example (P : PFunctor.{0, 0}) :
    (xTensor.{0, 0, 0, 0} P).equivA = _root_.Equiv.punitProd P.A :=
  xTensor_equivA.{0, 0, 0, 0} P

set_option linter.deprecated false in
example (P : PFunctor.{0, 0}) (a : (X ⊗ P).A) :
    (xTensor.{0, 0, 0, 0} P).equivB a = _root_.Equiv.punitProd (P.B a.2) :=
  xTensor_equivB.{0, 0, 0, 0} P a

end PFunctor.Equiv
