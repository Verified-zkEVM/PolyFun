/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Resumption

/-! # Finite free-program embedding examples -/

@[expose] public section

universe uA uB uα uβ

namespace PFunctor.FreeM.ResumptionExamples

/-- The embedding keeps the polynomial and both return universes independent. -/
example {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    (program : FreeM p α) (k : α → FreeM p β) :
    toResumption (FreeM.bind program k) =
      Resumption.bind (toResumption program) (fun value => toResumption (k value)) := by
  exact toResumption_bind program k

inductive Command
  | choose
  | select (wide : Bool)

def Answer : Command → Type
  | .choose => Bool
  | .select true => Fin 2
  | .select false => PUnit

def Interface : PFunctor where
  A := Command
  B := Answer

def program : FreeM Interface Nat :=
  .liftBind .choose fun
    | false => .pure 7
    | true => .liftBind (.select true) fun index => .pure (10 + index.val)

example : Resumption.dest (toResumption program) =
    Sum.inr ⟨Command.choose, fun answer => toResumption (match answer with
      | false => FreeM.pure 7
      | true => FreeM.liftBind (.select true) fun index => .pure (10 + index.val))⟩ := by
  simpa only [program] using
    (dest_toResumption_liftBind (p := Interface) Command.choose (fun
      | false => FreeM.pure 7
      | true => FreeM.liftBind (.select true) fun index => .pure (10 + index.val)))

/-- Constructor discrimination is preserved by the embedding. -/
example : toResumption program ≠ toResumption (FreeM.pure 7) := by
  intro h
  have hdest := congrArg Resumption.dest h
  simp only [program, toResumption, Resumption.dest_query,
    Resumption.dest_pure] at hdest
  cases hdest

/-- The public injectivity theorem recovers the original dependent tree. -/
example (left right : FreeM Interface Nat)
    (h : toResumption left = toResumption right) : left = right :=
  toResumption_injective h

example (k : Nat → FreeM Interface Nat) :
    toResumptionHom (FreeM.bind program k) =
      Resumption.bind (toResumptionHom program) (fun value => toResumptionHom (k value)) := by
  simp only [toResumptionHom_apply, toResumption_bind]

example (f : Nat → Nat) :
    toResumption (FreeM.map f program) = Resumption.map f (toResumption program) := by
  exact toResumption_map f program

end PFunctor.FreeM.ResumptionExamples
