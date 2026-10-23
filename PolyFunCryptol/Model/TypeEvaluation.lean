/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.Parameters

/-!
# Partial interpretation of symbolic types

Type interpretation traverses only the parameters actually used by the type.
Successful interpretation carries its resulting closed type, and substitution
commutes with interpretation even when unused substitution images are undefined.
-/

public section

namespace Cryptol.Ty

/-- Instantiate a type using partial numeric and value-type assignments. -/
@[expose] def instantiate? {N V M W : Type} (numbers : N → Option M)
    (types : V → Option (Ty M W)) : Ty N V → Option (Ty M W)
  | .var i => types i
  | .bit => some .bit
  | .integer => some .integer
  | .unit => some .unit
  | .seq n a => do return .seq (← numbers n) (← a.instantiate? numbers types)
  | .prod a b => do return .prod (← a.instantiate? numbers types) (← b.instantiate? numbers types)
  | .arrow a b => do return .arrow (← a.instantiate? numbers types) (← b.instantiate? numbers types)

/-- Total assignments are a special case of partial type interpretation. -/
theorem instantiate?_some {N V M W : Type} (a : Ty N V) (numbers : N → M)
    (types : V → Ty M W) :
    a.instantiate? (some ∘ numbers) (some ∘ types) = some (a.instantiate numbers types) := by
  induction a <;> simp_all [instantiate?, instantiate]

/-- Interpret a syntactically instantiated type without demanding unused images. -/
theorem instantiate?_instantiate {N V M W K U : Type} (a : Ty N V)
    (numbers : N → M) (types : V → Ty M W)
    (numericValues : M → Option K) (typeValues : W → Option (Ty K U)) :
    (a.instantiate numbers types).instantiate? numericValues typeValues =
      a.instantiate? (numericValues ∘ numbers)
        (fun i => (types i).instantiate? numericValues typeValues) := by
  induction a <;> simp_all [instantiate?, instantiate]

/-- Extending partial assignments preserves every successful type interpretation. -/
theorem instantiate?_mono {N V M W : Type} (a : Ty N V)
    {numbers numbers' : N → Option M} {types types' : V → Option (Ty M W)}
    (hn : ∀ n k, numbers n = some k → numbers' n = some k)
    (ht : ∀ v t, types v = some t → types' v = some t)
    {t : Ty M W} (h : a.instantiate? numbers types = some t) :
    a.instantiate? numbers' types' = some t := by
  induction a generalizing t with
  | var i => exact ht i t h
  | bit | integer | unit => exact h
  | seq n a ih =>
      cases he : numbers n with
      | none => simp [instantiate?, he] at h
      | some k =>
          cases ha : a.instantiate? numbers types with
          | none => simp [instantiate?, he, ha] at h
          | some u => simpa only [instantiate?, he, ha, hn n k he, ih ha] using h
  | prod a b iha ihb | arrow a b iha ihb =>
      cases ha : a.instantiate? numbers types with
      | none => simp [instantiate?, ha] at h
      | some u =>
          cases hb : b.instantiate? numbers types with
          | none => simp [instantiate?, ha, hb] at h
          | some v => simpa only [instantiate?, ha, hb, iha ha, ihb hb] using h

/-- Evaluate all numeric expressions occurring in a symbolic type. -/
@[expose] def eval {n v : Nat} (numbers : Fin n → Option Length)
    (types : Fin v → Option ClosedTy) (a : Ty (NumericExpr n) (Fin v)) : Option ClosedTy :=
  a.instantiate? (NumericExpr.eval numbers) types

/-- Partial type interpretation at a total assignment of its free parameters. -/
@[expose] def eval? {n v : Nat} (ρ : ParameterAssignment n v)
    (a : Ty (NumericExpr n) (Fin v)) : Option ClosedTy :=
  a.eval (some ∘ ρ.numbers) (some ∘ ρ.types)

/-- An assignment-independent type evaluation holds at every total assignment. -/
theorem eval?_eq_of_eval_none {n v : Nat} (a : Ty (NumericExpr n) (Fin v))
    {t : ClosedTy} (h : a.eval (fun _ => none) (fun _ => none) = some t)
    (ρ : ParameterAssignment n v) : a.eval? ρ = some t :=
  a.instantiate?_mono
    (numbers := NumericExpr.eval (fun _ => none))
    (numbers' := NumericExpr.eval (some ∘ ρ.numbers))
    (types := fun _ => none) (types' := some ∘ ρ.types)
    (fun e _ he => e.eval?_eq_of_eval_none he ρ.numbers) (fun _ _ he => nomatch he) h

/-- Evidence that a symbolic type denotes an actual closed semantic type. -/
structure Evaluation {n v : Nat} (ρ : ParameterAssignment n v)
    (a : Ty (NumericExpr n) (Fin v)) where
  /-- The interpreted type, without an arbitrary default for failed arithmetic. -/
  type : ClosedTy
  /-- Every numeric expression used by the type evaluates successfully. -/
  valid : a.eval? ρ = some type

/-- Interpretation witnesses cannot disagree about the semantic type. -/
theorem Evaluation.unique {n v : Nat} {ρ : ParameterAssignment n v}
    {a : Ty (NumericExpr n) (Fin v)} (x y : a.Evaluation ρ) : x.type = y.type :=
  Option.some.inj (x.valid.symm.trans y.valid)

/-- Raw numeric/type substitution commutes with partial interpretation. -/
theorem eval_subst {n v m w : Nat} (a : Ty (NumericExpr n) (Fin v))
    (numbers : Fin n → NumericExpr m) (types : Fin v → Ty (NumericExpr m) (Fin w))
    (numericValues : Fin m → Option Length) (typeValues : Fin w → Option ClosedTy) :
    (a.instantiate (NumericExpr.subst numbers) types).eval numericValues typeValues =
      a.eval (fun i => (numbers i).eval numericValues)
        (fun i => (types i).eval numericValues typeValues) := by
  rw [eval, instantiate?_instantiate]
  unfold eval
  congr 1
  funext e
  exact NumericExpr.eval_subst e numbers numericValues

/-- The total numeric fragment agrees with partial type interpretation. -/
theorem eval?_numeric {n v : Nat} (ρ : ParameterAssignment n v) (a : PolyTy n v) :
    (a.instantiate NumExpr.numeric .var).eval? ρ = some (ρ.apply a) := by
  rw [eval?, eval, instantiate?_instantiate]
  have hn : NumericExpr.eval (some ∘ ρ.numbers) ∘ NumExpr.numeric =
      some ∘ NumExpr.eval ρ.numbers := funext (fun e => NumExpr.eval?_numeric e ρ.numbers)
  rw [hn]
  exact instantiate?_some a _ _

end Cryptol.Ty
