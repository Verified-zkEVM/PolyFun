/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.TypeEvaluation
public import PolyFunCryptol.Translation.ConstraintEvidence

import all PolyFunCryptol.Model.Types
import all PolyFunCryptol.Model.Numeric
import all PolyFunCryptol.Model.Length

/-! # Defined type interpretation and kernel-replayed constraint evidence -/

public section

namespace Cryptol.Tests.TypeEvaluation

open Polymorphic Translation

/-- A demanded division by zero. -/
@[expose] def invalid : NumericExpr 0 := .binary .div (.finite 1) (.finite 0)
/-- The assignment for closed types. -/
@[expose] def empty : ParameterAssignment 0 0 := ⟨Fin.elim0, Fin.elim0⟩

-- Equal undefined expressions do not prove numeric reflexivity or type formation.
example :
    (ConstraintEvidence.prove Scope.empty (.numericEq invalid invalid)).isSome = false := by
  with_unfolding_all rfl
example : (Ty.seq invalid .bit).eval? empty = none := rfl

-- A genuine closed division computes the sequence type, without an arbitrary default.
example : (Ty.seq (.binary .div (.finite 12) (.finite 3)) .bit).eval? empty =
    some (.seq (.finite 4) .bit) := rfl

-- Substitution is lazy in unused images, including invalid type arguments.
example : ((Ty.bit : Ty (NumericExpr 1) (Fin 1)).instantiate
    (NumericExpr.subst (fun _ => invalid)) (fun _ => .seq invalid .bit)).eval? empty =
      some .bit := rfl

-- Used images really are demanded by type evaluation.
example : ((Ty.var 0 : Ty (NumericExpr 1) (Fin 1)).instantiate
    (NumericExpr.subst (fun _ => invalid)) (fun _ => .seq invalid .bit)).eval? empty = none := rfl

-- A finite parallel branch bounds an otherwise unbounded length.
example : Scope.empty.Entails (.fin (.min .infinite (.finite 7))) :=
  ConstraintEvidence.of_prove (by with_unfolding_all decide)

-- Composition uses ambient assumptions, without a solver assertion crossing the boundary.
example : (Scope.mk 1 0 [.fin (.var 0)]).Entails
    (.fin (.add (.mul (.var 0) (.finite 4)) (.finite 2))) :=
  ConstraintEvidence.of_prove (by with_unfolding_all decide)

example : Scope.empty.Entails
    (.numericEq (.binary .div (.finite 12) (.finite 3)) (.finite 4)) :=
  ConstraintEvidence.of_prove (by with_unfolding_all decide)

example : (ConstraintEvidence.prove Scope.empty (.numericEq (.finite 4) (.finite 3))).isSome =
    false := rfl

-- Reflexivity on parameters carries actual definedness, even in a nonempty scope.
example : (Scope.mk 1 0 []).Entails (.numericEq (.var 0) (.var 0)) :=
  ConstraintEvidence.of_prove (by with_unfolding_all decide)

-- Type-directed primitives can discharge closed structural constraints.
example : Scope.empty.Entails (.valueClass .ring (.seq (.finite 8) .bit)) :=
  ConstraintEvidence.of_prove (by with_unfolding_all decide)

example : (ConstraintEvidence.prove Scope.empty
    (.valueClass .ring (.seq .infinite .bit))).isSome = false := by
  with_unfolding_all rfl

example : Scope.empty.Entails (.literal true (.finite 8) (.seq (.finite 3) .bit)) :=
  ConstraintEvidence.of_prove (by with_unfolding_all decide)

-- Integral evidence suffices for zero even when the carrier is still a type parameter.
example : (Scope.mk 0 1 [.valueClass .integral (.var 0)]).Entails
    (.literal false (.finite 0) (.var 0)) :=
  ConstraintEvidence.of_prove (by with_unfolding_all decide)

end Cryptol.Tests.TypeEvaluation
