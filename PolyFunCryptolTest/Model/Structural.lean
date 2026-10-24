/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunCryptol.Model.Records
import PolyFunCryptol.Model.StructuralLogic
import PolyFunCryptol.Model.StructuralRing
import PolyFunCryptol.Model.Operational
import PolyFunCryptol.Model.Zero
import all PolyFunCryptol.Model.Reference.Types

/-! # Demand and class-resolution regressions for structural operations -/

public section

namespace Cryptol.Tests.Model.Structural

open OmegaCompletePartialOrder

/-- Foundation theta's `(x-1)%5` at zero has the pinned reference's negative index. -/
example : (Expr.index (.generate (Length.finite 5) (.bit false))
    (.intOp .mod (.intOp .sub (.integer 0) (.integer 1)) (.integer 5))).start.run 100 =
      .inl (.error (.invalidIndex (-1))) := rfl

example : (LogicType.seq (.finite 0) .bit).binarySem .and
    (.error (.user "left")) (.value Fin.elim0) = .error (.user "left") := rfl

example : (LogicType.seq (.finite 0) .bit).binarySem .or
    (.value Fin.elim0) (.error (.user "right")) = .error (.user "right") := rfl

example : (LogicType.prod .bit .bit).binarySem .xor
    (.value (.value ⟨true⟩, .error (.user "unselected")))
    (.value (.value ⟨false⟩, ⊥)) =
      .value (.value ⟨true⟩, .error (.user "unselected")) := rfl

example : DomainResult.applyContinuous
    ((LogicType.arrow .integer .bit).binarySem .and
      (.error (.user "left")) (.error (.user "right"))) ⊥ =
        .error (.user "left") := rfl

example : DomainResult.applyContinuous
    ((LogicType.arrow .integer (.arrow .integer .bit)).binarySem .and
      (.error (.user "outer")) ⊥) ⊥ = .error (.user "outer") := rfl

example : DomainResult.force (DomainResult.applyContinuous
    ((LogicType.arrow .integer (.arrow .integer .bit)).complementSem
      (.error (.user "outer"))) ⊥) (.value ⟨true⟩ : Computation .bit) = .value ⟨true⟩ := rfl

example : DomainResult.applyContinuous
    ((RingType.arrow .integer .integer).binarySem .add
      (.value (.const (.error (.user "left-result")))) (.error (.user "right-function"))) ⊥ =
        .error (.user "left-result") := rfl

example : (RingType.seq (.finite 0) .integer).binarySem .add
    (.value Fin.elim0) (.error (.user "right")) = .error (.user "right") := rfl

example (old : Expr [] (Record.type [.integer, .bit])) (value : Expr [] .bit) :
    (Record.select (.succ .zero) (Record.update (.succ .zero) old value)).denote
      Environment.empty = value.denote Environment.empty :=
  Record.denote_select_update _ _ _ _

example : (Record.select (.succ .zero)
    (Record.update (.succ .zero)
      (.error (.user "original") : Expr [] (Record.type [.integer, .bit])) (.bit true))).denote
      Environment.empty = .value ⟨true⟩ := by
  rw [Record.denote_select_update]
  rfl

/-- A later function field exposes a closure before demanding the old record. -/
example : (Expr.force
    (Record.select (fields := [.integer, .arrow .integer .integer]) (.succ .zero)
      ((RingType.prod .integer (.prod (.arrow .integer .integer) .unit)).binary .add
        (Record.update .zero
          (.error (.user "old") : Expr [] (Record.type [.integer, .arrow .integer .integer]))
          (.integer 0))
        (.zero (Record.type [.integer, .arrow .integer .integer]))))
    (.integer 5)).start.run 300 = .inl (.ok (.integer 5)) := rfl

example : (Reference.ValueType.seq .infinite .bit).supports .logic = true := rfl

example : (Reference.ValueType.seq .infinite .bit).supports .ring = false := rfl

example : (Reference.ValueType.seq .infinite .integer).supports .ring = true := rfl

example : (Reference.ValueType.seq .infinite .integer).supports .eq = false := rfl

example : (Reference.ValueType.seq (.finite 0) .bit).supports .signedCmp = false := rfl

example : (Reference.ValueType.seq (.finite 0) .bit).supports .integral = true := rfl

example : (Reference.ValueType.seq (.finite 1) .integer).supports .integral = false := rfl

example : (Reference.ValueType.record [("x", .bit), ("y", .integer)]).supports .logic = false := rfl

example : (Reference.ValueType.function .integer (.seq (.finite 8) .bit)).supports .ring =
    true := rfl

example : (Reference.ValueType.function .integer .bit).supports .cmp = false := rfl

example : Reference.ValueType.bit.literal false (.finite 2) = false := rfl
example : Reference.ValueType.bit.literal true (.finite 2) = true := rfl
example : (Reference.ValueType.seq (.finite 0) .bit).literal false (.finite 0) = true := rfl
example : (Reference.ValueType.seq (.finite 8) .bit).literal true (.finite 256) = true := rfl
example : (Reference.ValueType.seq (.finite 8) .bit).literal false (.finite 256) = false := rfl
example : Reference.ValueType.integer.literal true .infinite = true := rfl

example : Reference.evaluateConstructor "TF TCSub" [.number (.finite 0), .number (.finite 1)] =
    .error "undefined numeric operation TF TCSub" := rfl

end Cryptol.Tests.Model.Structural
