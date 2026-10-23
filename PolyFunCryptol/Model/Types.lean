/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Basic
public import PolyFunCryptol.Model.Numeric

/-!
# Kinds, lengths, and types of the Cryptol core

Numeric and value variables inhabit separate scopes. A schema records its
quantifiers and constraints explicitly; instantiation carries evidence for
those constraints. No inference or constraint solver is part of this model.
Infinite lengths are separate from finite lengths, including zero.
-/

@[expose] public section

namespace Cryptol

/-- Numeric expressions retained at runtime for sizes and primitive arguments. -/
inductive NumExpr (n : Nat) where
  | var (index : Fin n)
  | finite (value : Nat)
  | infinite
  | add (left right : NumExpr n)
  | mul (left right : NumExpr n)
  | min (left right : NumExpr n)
  deriving DecidableEq, Repr

/-- Evaluate numeric arguments under an explicit numeric instantiation. -/
def NumExpr.eval {n : Nat} (ρ : Fin n → Length) : NumExpr n → Length
  | .var i => ρ i
  | .finite m => .finite m
  | .infinite => .infinite
  | .add a b => Length.add (a.eval ρ) (b.eval ρ)
  | .mul a b => Length.mul (a.eval ρ) (b.eval ρ)
  | .min a b => Length.min (a.eval ρ) (b.eval ρ)

/-- Embed the total numeric fragment into partial reference numeric syntax. -/
def NumExpr.numeric {n : Nat} : NumExpr n → NumericExpr n
  | .var i => .var i
  | .finite k => .finite k
  | .infinite => .infinite
  | .add a b => .binary .add a.numeric b.numeric
  | .mul a b => .binary .mul a.numeric b.numeric
  | .min a b => .binary .min a.numeric b.numeric

/-- The total fragment has the same meaning in reference numeric semantics. -/
@[simp] theorem NumExpr.eval?_numeric {n : Nat} (e : NumExpr n) (ρ : Fin n → Length) :
    e.numeric.eval? ρ = some (e.eval ρ) := by
  induction e with
  | var | finite | infinite => rfl
  | add a b ha hb | mul a b ha hb | min a b ha hb =>
      simp_all [numeric, NumericExpr.eval?, NumericExpr.eval, eval, NumericBinary.eval]

/-- Value types; products also encode finite tuples and named record spines. -/
inductive Ty (N V : Type) where
  | var (index : V)
  | bit
  | integer
  | unit
  | seq (length : N) (element : Ty N V)
  | prod (left right : Ty N V)
  | arrow (argument result : Ty N V)
  deriving DecidableEq, Repr

/-- Closed semantic types with evaluated numeric arguments. -/
abbrev ClosedTy := Ty Length Empty

/-- Symbolic types scoped by numeric and value quantifiers. -/
abbrev PolyTy (n v : Nat) := Ty (NumExpr n) (Fin v)

/-- Interpret a type at an explicit assignment to both kinds of variables. -/
def Ty.instantiate {N V M W : Type} (ρ : N → M) (θ : V → Ty M W) :
    Ty N V → Ty M W
  | .var i => θ i
  | .bit => .bit
  | .integer => .integer
  | .unit => .unit
  | .seq l a => .seq (ρ l) (a.instantiate ρ θ)
  | .prod a b => .prod (a.instantiate ρ θ) (b.instantiate ρ θ)
  | .arrow a b => .arrow (a.instantiate ρ θ) (b.instantiate ρ θ)

/-- Structural classes interpreted by Cryptol's type-directed primitives. -/
inductive ValueClass where
  | zero | logic | ring | integral | eq | cmp | signedCmp
  deriving DecidableEq, Repr

/-- Recognize the bit element type used by packed sequences. -/
def ClosedTy.isBit : ClosedTy → Bool
  | .bit => true
  | _ => false

/-- Structural class membership of an evaluated semantic type. -/
def ClosedTy.supports (c : ValueClass) : ClosedTy → Bool
  | .var i => i.elim
  | .bit => c == .zero || c == .logic || c == .eq || c == .cmp
  | .integer => c == .zero || c == .ring || c == .integral || c == .eq || c == .cmp
  | .unit => c != .integral
  | .seq n a =>
      if c == .integral then
        match n, a with | .finite _, .bit => true | _, _ => false
      else if c == .ring && ClosedTy.isBit a then
        match n with | .finite _ => true | .infinite => false
      else if c == .signedCmp && ClosedTy.isBit a then
        match n with | .finite n => n > 0 | .infinite => false
      else if (c == .eq || c == .cmp || c == .signedCmp) && n == .infinite then false
      else supports c a
  | .prod a b => c != .integral && supports c a && supports c b
  | .arrow _ b => (c == .zero || c == .logic || c == .ring) && supports c b

/-- Literal admissibility distinguishes an exact value from an exclusive upper bound. -/
def ClosedTy.literal (exclusive : Bool) (n : Length) : ClosedTy → Bool
  | .bit => match n with
      | .finite n => n ≤ if exclusive then 2 else 1
      | .infinite => false
  | .integer => exclusive || match n with
      | .finite _ => true
      | .infinite => false
  | .seq (.finite w) .bit => match n with
      | .finite n =>
          match (if exclusive then NumericUnary.lg2 else .width).eval (.finite n) with
          | .finite needed => needed ≤ w
          | .infinite => false
      | .infinite => false
  | _ => false

/-- Every integral carrier admits the zero literal, including an empty word. -/
theorem ClosedTy.literal_zero_of_supports_integral (a : ClosedTy) (exclusive : Bool)
    (h : a.supports .integral = true) : a.literal exclusive (.finite 0) = true := by
  cases a with
  | var i => exact i.elim
  | integer => cases exclusive <;> rfl
  | seq n a =>
      cases n with
      | infinite => simp [supports] at h
      | finite n =>
          cases a <;> simp_all [supports, literal, NumericUnary.eval]
          cases exclusive <;> simp
  | bit | unit | prod | arrow => simp [supports] at h

/-- Numeric comparison with infinity as the greatest length. -/
def Length.ge : Length → Length → Bool
  | .infinite, _ => true
  | .finite _, .infinite => false
  | .finite a, .finite b => b ≤ a

/-- Open admissibility constraints retain numeric and value-type variables. -/
inductive Constraint (n v : Nat) where
  | fin (length : NumExpr n)
  | eq (left right : NumExpr n)
  | defined (expression : NumericExpr n)
  | numericEq (left right : NumericExpr n)
  | numericNe (left right : NumericExpr n)
  | numericGe (left right : NumericExpr n)
  | valueClass (cls : ValueClass) (type : PolyTy n v)
  | literal (exclusive : Bool) (value : NumericExpr n) (type : PolyTy n v)
  | typeEq (left right : PolyTy n v)
  deriving DecidableEq, Repr

/-- Satisfaction requires actual defined numeric results, including for equality. -/
def Constraint.Holds {n v : Nat} (ρ : Fin n → Length)
    (θ : Fin v → ClosedTy) : Constraint n v → Prop
  | .fin l => ∃ k, l.eval ρ = .finite k
  | .eq a b => a.eval ρ = b.eval ρ
  | .defined e => ∃ l, e.eval? ρ = some l
  | .numericEq a b => ∃ x y, a.eval? ρ = some x ∧ b.eval? ρ = some y ∧ x = y
  | .numericNe a b => ∃ x y, a.eval? ρ = some x ∧ b.eval? ρ = some y ∧ x ≠ y
  | .numericGe a b => ∃ x y, a.eval? ρ = some x ∧ b.eval? ρ = some y ∧ x.ge y = true
  | .valueClass c a => ClosedTy.supports c (a.instantiate (NumExpr.eval ρ) θ) = true
  | .literal exclusive e a => ∃ l, e.eval? ρ = some l ∧
      ClosedTy.literal exclusive l (a.instantiate (NumExpr.eval ρ) θ) = true
  | .typeEq a b => a.instantiate (NumExpr.eval ρ) θ = b.instantiate (NumExpr.eval ρ) θ

/-- A prenex polymorphic type with explicit constraints. -/
structure Schema where
  /-- Number of numeric parameters. -/
  numericArity : Nat
  /-- Number of value-type parameters. -/
  typeArity : Nat
  /-- Assumptions checked at each instantiation. -/
  constraints : List (Constraint numericArity typeArity)
  /-- The quantified type. -/
  body : PolyTy numericArity typeArity
  deriving Repr

/-- A valid schema instantiation, with numeric arguments retained. -/
structure Schema.Instantiation (schema : Schema) where
  /-- Actual numeric arguments. -/
  numbers : Fin schema.numericArity → Length
  /-- Actual value types. -/
  types : Fin schema.typeArity → ClosedTy
  /-- Evidence for every declared constraint. -/
  valid : ∀ c ∈ schema.constraints, c.Holds numbers types

/-- Typed variables use PolyFun's shared scoped representation. -/
abbrev Var {α : Type} : List α → α → Type := @IPFunctor.ScopedVar α

namespace Var
export IPFunctor.ScopedVar (zero succ index)
end Var


end Cryptol
