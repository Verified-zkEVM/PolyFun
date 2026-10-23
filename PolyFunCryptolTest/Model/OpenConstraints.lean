/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.PolyScopeMaps
public import PolyFunCryptol.Translation.OpenTypes

/-! # Open constraints retain definedness and avoid type-variable capture -/

public section

namespace Cryptol.Tests.OpenConstraints

open Polymorphic

/-- Division by a zero length has no numeric result. -/
@[expose] def undefined : NumericExpr 0 := .binary .div (.finite 1) (.finite 0)

/-- Equal undefined expressions are not valid numeric equalities. -/
theorem undefined_not_equal :
    ¬ (Constraint.numericEq (v := 0) undefined undefined).Holds Fin.elim0 Fin.elim0 := by
  rintro ⟨x, _, hx, _⟩
  simp [undefined, NumericExpr.eval?, NumericExpr.eval, NumericBinary.eval] at hx

/-- Definedness is independent of whether both failures have the same syntax. -/
example : ¬ (Constraint.numericGe (v := 0) undefined (.finite 0)).Holds
    Fin.elim0 Fin.elim0 := by
  rintro ⟨x, _, hx, _⟩
  simp [undefined, NumericExpr.eval?, NumericExpr.eval, NumericBinary.eval] at hx

/-- A type quantifier shifts assumptions on older type variables. -/
example : (Scope.mk 0 1 [.valueClass .integral (.var 0)]).bindType.constraints =
    [.valueClass .integral (.var 1)] := rfl

/-- Signed comparison excludes the empty word while ordinary equality admits it. -/
example : ClosedTy.supports .signedCmp (.seq (.finite 0) .bit) = false ∧
    ClosedTy.supports .eq (.seq (.finite 0) .bit) = true := by decide

/-- Finite words have ring operations; an infinite bit stream does not. -/
example : ClosedTy.supports .ring (.seq (.finite 0) .bit) = true ∧
    ClosedTy.supports .ring (.seq .infinite .bit) = false := by decide

/-- Literal bounds use different strictness conventions. -/
example : ClosedTy.literal false (.finite 8) (.seq (.finite 3) .bit) = false ∧
    ClosedTy.literal true (.finite 8) (.seq (.finite 3) .bit) = true := by decide

/-- Collapsing variables substitutes both the class carrier and numeric expressions. -/
example (ρ : ParameterAssignment 1 1) :
    ((Constraint.literal false (.binary .sub (.var 1) (.var 0)) (.seq (.var 1) (.var 1))).subst
      (⟨fun _ : Fin 2 => .var 0, fun _ : Fin 2 => .var 0⟩ : ParameterSubstitution 2 2 1 1)).Holds
        ρ.numbers ρ.types ↔
      (Constraint.literal false (.binary .sub (.var 0) (.var 0)) (.seq (.var 0) (.var 0))).Holds
        ρ.numbers ρ.types := Iff.rfl

/-- Unsupported partial lengths are rejected, even when they occur in an otherwise valid type. -/
example : Translation.OpenTypes.value (⟨[], []⟩ : Translation.OpenTypes.Parameters 0 0) 20
    (.constructor "TC TCSeq" [.constructor "TF TCDiv" [.number 1, .number 0],
      .constructor "TC TCBit" []]) =
        .error "type requires a checked partial numeric evaluation" := rfl

end Cryptol.Tests.OpenConstraints
