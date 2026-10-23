/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.PolyScope
public import PolyFunCryptol.Model.TypeEvaluation

/-!
# Proof-producing constraint discharge

The checker returns evidence of entailment, not a Boolean assertion supplied by
an external solver. Closed numeric evaluation uses the partial numeric model;
undefined expressions do not prove reflexivity. Unsupported goals remain open.
-/

public section

namespace Cryptol.Translation.ConstraintEvidence

open Polymorphic

/-- A numeric value known independently of the ambient parameter assignment. -/
@[expose] def numeric {n : Nat} (e : NumericExpr n) :
    Option {l : Length // ∀ ρ, e.eval? ρ = some l} :=
  match h : e.eval (fun _ => none) with
  | none => none
  | some l => some ⟨l, e.eval?_eq_of_eval_none h⟩

/-- An evaluated type that is independent of all ambient numeric and type parameters. -/
@[expose] def closedType {n v : Nat} (a : PolyTy n v) :
    Option {t : ClosedTy // ∀ ρ : ParameterAssignment n v, ρ.apply a = t} :=
  let t := a.instantiate NumExpr.numeric .var
  match h : t.eval (fun _ => none) (fun _ => none) with
  | none => none
  | some b => some ⟨b, fun ρ => Option.some.inj
      ((Ty.eval?_numeric ρ a).symm.trans (t.eval?_eq_of_eval_none h ρ))⟩

/-- Unary numeric functions preserve definedness at every valid assignment. -/
theorem defined_unary {w : Scope} (op : NumericUnary) {e : NumericExpr w.numbers}
    (h : w.Entails (.defined e)) : w.Entails (.defined (.unary op e)) := by
  intro ρ
  obtain ⟨x, hx⟩ := h ρ
  simp only [NumericExpr.eval?] at hx
  exact ⟨op.eval x, by simp [NumericExpr.eval?, NumericExpr.eval, hx]⟩

/-- Total binary operations preserve definedness of both demanded arguments. -/
theorem defined_binary {w : Scope} (op : NumericBinary) {a b : NumericExpr w.numbers}
    (total : ∀ x y, ∃ z, op.eval x y = some z)
    (ha : w.Entails (.defined a)) (hb : w.Entails (.defined b)) :
    w.Entails (.defined (.binary op a b)) := by
  intro ρ
  obtain ⟨x, hx⟩ := ha ρ
  obtain ⟨y, hy⟩ := hb ρ
  obtain ⟨z, hz⟩ := total x y
  simp only [NumericExpr.eval?] at hx hy
  exact ⟨z, by simp [NumericExpr.eval?, NumericExpr.eval, hx, hy, hz]⟩

/-- Establish numeric definedness without assigning defaults to partial operations. -/
@[expose] def defined (w : Scope) : Nat → (e : NumericExpr w.numbers) →
    Option (PLift (w.Entails (.defined e)))
  | 0, _ => none
  | fuel + 1, e =>
      if h : Constraint.defined e ∈ w.constraints then some ⟨fun ρ => ρ.property _ h⟩
      else match numeric e with
      | some ⟨x, hx⟩ => some ⟨fun ρ => ⟨x, hx ρ.val.numbers⟩⟩
      | none => match e with
          | .var i => some ⟨fun ρ => ⟨ρ.val.numbers i, rfl⟩⟩
          | .unary op a => do return ⟨defined_unary op (← defined w fuel a).down⟩
          | .binary .add a b => do
              return ⟨defined_binary .add (fun x y => ⟨x.add y, rfl⟩)
                (← defined w fuel a).down (← defined w fuel b).down⟩
          | .binary .mul a b => do
              return ⟨defined_binary .mul (fun x y => ⟨x.mul y, rfl⟩)
                (← defined w fuel a).down (← defined w fuel b).down⟩
          | .binary .min a b => do
              return ⟨defined_binary .min (fun x y => ⟨x.min y, rfl⟩)
                (← defined w fuel a).down (← defined w fuel b).down⟩
          | _ => none

/-- A sum of finite lengths is finite. -/
theorem finite_add {w : Scope} {a b : NumExpr w.numbers}
    (ha : w.Entails (.fin a)) (hb : w.Entails (.fin b)) : w.Entails (.fin (.add a b)) := by
  intro ρ
  obtain ⟨x, hx⟩ := ha ρ
  obtain ⟨y, hy⟩ := hb ρ
  exact ⟨x + y, by simp [NumExpr.eval, hx, hy, Length.add]⟩

/-- A product of finite lengths is finite. -/
theorem finite_mul {w : Scope} {a b : NumExpr w.numbers}
    (ha : w.Entails (.fin a)) (hb : w.Entails (.fin b)) : w.Entails (.fin (.mul a b)) := by
  intro ρ
  obtain ⟨x, hx⟩ := ha ρ
  obtain ⟨y, hy⟩ := hb ρ
  refine ⟨x * y, ?_⟩
  change Length.mul (a.eval ρ.val.numbers) (b.eval ρ.val.numbers) = _
  rw [hx, hy]
  cases x <;> cases y <;> simp [Length.mul]

/-- A finite left bound suffices for a finite minimum. -/
theorem finite_min_left {w : Scope} {a b : NumExpr w.numbers}
    (ha : w.Entails (.fin a)) : w.Entails (.fin (.min a b)) := by
  intro ρ
  obtain ⟨x, hx⟩ := ha ρ
  change ∃ k, Length.min (a.eval ρ.val.numbers) (b.eval ρ.val.numbers) = .finite k
  rw [hx]
  cases b.eval ρ.val.numbers <;> exact ⟨_, rfl⟩

/-- A finite right bound suffices for a finite minimum. -/
theorem finite_min_right {w : Scope} {a b : NumExpr w.numbers}
    (hb : w.Entails (.fin b)) : w.Entails (.fin (.min a b)) := by
  intro ρ
  obtain ⟨x, hx⟩ := hb ρ
  change ∃ k, Length.min (a.eval ρ.val.numbers) (b.eval ρ.val.numbers) = .finite k
  rw [hx]
  cases a.eval ρ.val.numbers <;> exact ⟨_, rfl⟩

/-- Find finite-length evidence compositionally, including a bounded parallel branch. -/
@[expose] def finite (w : Scope) : Nat → (e : NumExpr w.numbers) →
    Option (PLift (w.Entails (.fin e)))
  | 0, _ => none
  | fuel + 1, e =>
      if h : Constraint.fin e ∈ w.constraints then some ⟨fun ρ => ρ.property _ h⟩
      else match e with
      | .finite k => some ⟨fun _ => ⟨k, rfl⟩⟩
      | .add a b => do return ⟨finite_add (← finite w fuel a).down (← finite w fuel b).down⟩
      | .mul a b => do return ⟨finite_mul (← finite w fuel a).down (← finite w fuel b).down⟩
      | .min a b => match finite w fuel a with
          | some h => some ⟨finite_min_left h.down⟩
          | none => do return ⟨finite_min_right (← finite w fuel b).down⟩
      | _ => none

/-- Check supported entailments, preserving an explicit failure for unresolved goals. -/
@[expose] def prove (w : Scope) (c : Constraint w.numbers w.types) (fuel : Nat := 64) :
    Option (PLift (w.Entails c)) :=
  if h : c ∈ w.constraints then some ⟨fun ρ => ρ.property c h⟩
  else match c with
  | .fin e => finite w fuel e
  | .eq a b => if h : a = b then some ⟨fun _ => congrArg _ h⟩ else none
  | .typeEq a b => if h : a = b then some ⟨fun _ => congrArg _ h⟩ else none
  | .defined e => defined w fuel e
  | .valueClass c a => do
      let ⟨t, ht⟩ ← closedType a
      if h : t.supports c = true then
        return ⟨fun ρ => by
          change ClosedTy.supports c (ρ.val.apply a) = true
          rw [ht]
          exact h⟩
      else none
  | .literal exclusive e a => do
      let ⟨x, hx⟩ ← numeric e
      match closedType a with
      | some ⟨t, ht⟩ =>
          if h : t.literal exclusive x = true then
            return ⟨fun ρ => ⟨x, hx ρ.val.numbers, by
              change ClosedTy.literal exclusive x (ρ.val.apply a) = true
              rw [ht]
              exact h⟩⟩
          else none
      | none =>
          if hz : x = .finite 0 then
            if h : Constraint.valueClass .integral a ∈ w.constraints then
              return ⟨fun ρ => ⟨x, hx ρ.val.numbers, by
                rw [hz]
                exact ClosedTy.literal_zero_of_supports_integral _ _ (ρ.property _ h)⟩⟩
            else none
          else none
  | .numericEq a b =>
      if h : a = b then do
        let hd ← defined w fuel a
        return ⟨fun ρ => by
          obtain ⟨x, hx⟩ := hd.down ρ
          exact ⟨x, x, hx, h ▸ hx, rfl⟩⟩
      else do
        let ⟨x, hx⟩ ← numeric a
        let ⟨y, hy⟩ ← numeric b
        if he : x = y then
          return ⟨fun ρ => ⟨x, y, hx ρ.val.numbers, hy ρ.val.numbers, he⟩⟩
        else none
  | .numericNe a b => do
      let ⟨x, hx⟩ ← numeric a
      let ⟨y, hy⟩ ← numeric b
      if h : x ≠ y then return ⟨fun ρ => ⟨x, y, hx ρ.val.numbers, hy ρ.val.numbers, h⟩⟩ else none
  | .numericGe a b => do
      let ⟨x, hx⟩ ← numeric a
      let ⟨y, hy⟩ ← numeric b
      if h : x.ge y = true then
        return ⟨fun ρ => ⟨x, y, hx ρ.val.numbers, hy ρ.val.numbers, h⟩⟩
      else none

/-- Kernel replay of a successful proof search yields its entailment evidence. -/
theorem of_prove {w : Scope} {c : Constraint w.numbers w.types}
    (h : (prove w c).isSome = true) : w.Entails c :=
  ((prove w c).get h).down

end Cryptol.Translation.ConstraintEvidence
