/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.Reference.Types
public import PolyFunCryptol.Model.Scheme

/-!
# Open source parameters and ordered schemes

Source parameter identities resolve to separate numeric and value-type de Bruijn
scopes. Numeric parsing retains partial operations. Scheme checking preserves
ordered binders and class evidence; it does not invoke an external solver.
-/

public section

namespace Cryptol.Translation.OpenTypes

open Reference

/-- Source identities at an open pair of parameter scopes. -/
structure Parameters (n v : Nat) where
  /-- Numeric source identities and their binding positions. -/
  numbers : List (Nat × Fin n)
  /-- Value-type source identities and their binding positions. -/
  types : List (Nat × Fin v)

/-- Enter one numeric source binder. -/
@[expose] def Parameters.bindNum {n v : Nat} (env : Parameters n v) (id : Nat) :
    Parameters (n + 1) v :=
  ⟨(id, 0) :: env.numbers.map (fun (name, i) => (name, i.succ)), env.types⟩

/-- Enter one value-type source binder. -/
@[expose] def Parameters.bindType {n v : Nat} (env : Parameters n v) (id : Nat) :
    Parameters n (v + 1) :=
  ⟨env.numbers, (id, 0) :: env.types.map (fun (name, i) => (name, i.succ))⟩

/-- Parse numeric expressions without choosing values for open parameters. -/
@[expose] def numeric {n v : Nat} (env : Parameters n v) :
    Nat → TypeExpr → Except String (NumericExpr n)
  | 0, _ => .error "numeric syntax budget exhausted"
  | fuel + 1, expression => do
      match expression with
      | .var p =>
          unless p.kind == .number do throw "expected numeric parameter"
          match env.numbers.find? (fun x => x.1 == p.id) with
          | some (_, i) => return .var i
          | none => throw s!"unbound numeric parameter {p.id}"
      | .number k => return .finite k
      | .constructor "TC TCInf" [] => return .infinite
      | .constructor "TF TCWidth" [e] => return .unary .width (← numeric env fuel e)
      | .constructor "TF TCLenFromThenTo" [a, b, c] =>
          return .rangeLength (← numeric env fuel a) (← numeric env fuel b) (← numeric env fuel c)
      | .constructor name [a, b] =>
          let some op := numericBinary? name | throw s!"unsupported numeric constructor {name}"
          return .binary op (← numeric env fuel a) (← numeric env fuel b)
      | .synonym _ _ body => numeric env fuel body
      | _ => throw "expected numeric expression"

/-- Recognize arithmetic with a total interpretation at every parameter assignment. -/
@[expose] def totalNumeric {n : Nat} : NumericExpr n → Except String (NumExpr n)
  | .var i => .ok (.var i)
  | .finite k => .ok (.finite k)
  | .infinite => .ok .infinite
  | .binary .add a b => .add <$> totalNumeric a <*> totalNumeric b
  | .binary .mul a b => .mul <$> totalNumeric a <*> totalNumeric b
  | .binary .min a b => .min <$> totalNumeric a <*> totalNumeric b
  | _ => .error "type requires a checked partial numeric evaluation"

/-- Check an open value type supported by the canonical type carrier. -/
@[expose] def value {n v : Nat} (env : Parameters n v) :
    Nat → TypeExpr → Except String (PolyTy n v)
  | 0, _ => .error "value-type syntax budget exhausted"
  | fuel + 1, expression => do
      match expression with
      | .var p =>
          unless p.kind == .value do throw "expected value-type parameter"
          match env.types.find? (fun x => x.1 == p.id) with
          | some (_, i) => return .var i
          | none => throw s!"unbound value-type parameter {p.id}"
      | .constructor "TC TCBit" [] => return .bit
      | .constructor "TC TCInteger" [] => return .integer
      | .constructor "TC TCSeq" [n, a] =>
          return .seq (← numeric env fuel n >>= totalNumeric) (← value env fuel a)
      | .constructor "TC TCFun" [a, b] =>
          return .arrow (← value env fuel a) (← value env fuel b)
      | .tuple 0 [] => return .unit
      | .synonym _ _ body => value env fuel body
      | _ => throw "value type requires an aggregate or nominal source-shape interpretation"

/-- Check an open assumption, retaining partial arithmetic and structural class identities. -/
@[expose] def constraint {n v : Nat} (env : Parameters n v) (fuel : Nat) :
    TypeExpr → Except String (Constraint n v)
  | .constructor "PC PFin" [e] =>
      .fin <$> (numeric env fuel e >>= totalNumeric)
  | .constructor "PC PEqual" [a, b] =>
      .numericEq <$> numeric env fuel a <*> numeric env fuel b
  | .constructor "PC PNeq" [a, b] =>
      .numericNe <$> numeric env fuel a <*> numeric env fuel b
  | .constructor "PC PGeq" [a, b] =>
      .numericGe <$> numeric env fuel a <*> numeric env fuel b
  | .constructor "PC PLiteral" [e, a] =>
      .literal false <$> numeric env fuel e <*> value env fuel a
  | .constructor "PC PLiteralLessThan" [e, a] =>
      .literal true <$> numeric env fuel e <*> value env fuel a
  | .constructor name [a] => do
      let some c := valueClass? name | throw s!"unsupported structural class {name}"
      return .valueClass c (← value env fuel a)
  | .synonym _ _ body => constraint env fuel body
  | _ => .error "unsupported open constraint"

/-- Build ordered scheme binders from the official source schema. -/
@[expose] def scheme : {n v : Nat} → Parameters n v → Nat → Reference.Schema →
    Except String (Polymorphic.Scheme n v)
  | _, _, _, 0, _ => .error "scheme syntax budget exhausted"
  | _, _, env, fuel + 1, ⟨[], constraints, body⟩ => do
      let cs ← constraints.mapM (constraint env fuel)
      let a ← value env fuel body
      return cs.foldr Polymorphic.Scheme.guard (.mono a)
  | _, _, env, fuel + 1, ⟨p :: ps, constraints, body⟩ =>
      match p.kind with
      | .number => .allNum <$> scheme (env.bindNum p.id) fuel ⟨ps, constraints, body⟩
      | .value => .allType <$> scheme (env.bindType p.id) fuel ⟨ps, constraints, body⟩
      | _ => .error "unsupported scheme binder kind"

end Cryptol.Translation.OpenTypes
