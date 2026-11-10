/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedPrograms
import PolyFun.IPFunctor.Scoped.EnvRelation
import PolyFun.IPFunctor.Scoped.Reindex

/-!
# Ordinary-import checks for binding syntax

These checks exercise capture avoidance, the shared fold theorem, and a
noninjective change of sorts that routes arguments and transports binders,
without opening implementation bodies. Environments, renamings and substitutions
share one type, so their lookup, composition and positional reindexing laws are
checked once.
-/

public section

namespace PolyFunTest.Scoped

open IPFunctor IPFunctor.ScopedSignature Examples.ScopedPrograms

example : (sumTo 10).denote algebra Env.empty = 45 := rfl
/-- The older binding survives entry into the lambda body. -/
theorem scoped_capture : captureExample.denote algebra Env.empty 3 = 10 := rfl
example : (eliminateLets captureExample).denote algebra Env.empty 3 = 10 := rfl

example {Γ : List Ty} {a : Ty} (e : Expr Γ a) (ρ : Env Ty.Value Γ) :
    (eliminateLets e).denote algebra ρ = e.denote algebra ρ := eliminateLets_correct e ρ

/-- An empty constructor signature isolates variables at arbitrary sorts. -/
@[expose] def variableOnly : ScopedSignature Nat where
  Op _ := Empty
  Arg e := nomatch e
  binders e := nomatch e
  sort e := nomatch e

/-- Distinct sorts may become equal after instantiation. -/
private def collapse : Hom variableOnly variableOnly (fun _ => 0) where
  op e := nomatch e
  arg e := nomatch e
  binders e := nomatch e
  sort e := nomatch e

example :
    ((Term.var (.succ .zero) : variableOnly.Term [1, 2] 2).map collapse) =
      (Term.var (.succ .zero) : variableOnly.Term [0, 0] 0) := rfl

/-- At each sort, a constructor whose `false` child binds that sort and whose `true` child binds
nothing. -/
@[expose] def bindsFirst : ScopedSignature Nat where
  Op _ := Unit
  Arg _ := Bool
  binders {a} _ p := if p then [] else [a]
  sort {a} _ _ := a

/-- The same constructor with the roles of its children exchanged. -/
@[expose] def bindsSecond : ScopedSignature Nat where
  Op _ := Unit
  Arg _ := Bool
  binders {a} _ p := if p then [a] else []
  sort {a} _ _ := a

/-- Collapse all sorts and exchange the two children. -/
private def collapseSwap : Hom bindsFirst bindsSecond (fun _ => 0) where
  op _ := ()
  arg _ p := !p
  binders _ p := by cases p <;> rfl
  sort _ _ := rfl

/-- Both children survive at the exchanged arguments. The child under the binder still reads the
bound variable, and the other still reads the ambient one, though every sort is now `0`. -/
example :
    ((Term.node () (fun
        | false => Term.var .zero
        | true => Term.var (.succ .zero)) : bindsFirst.Term [1, 2] 2).map collapseSwap) =
      (Term.node () (fun
        | false => Term.var (.succ .zero)
        | true => Term.var .zero) : bindsSecond.Term [0, 0] 0) := by
  refine congrArg (Term.node (σ := bindsSecond) (Γ := [0, 0]) (a := 0) ()) (funext fun p => ?_)
  cases p <;> rfl

example {Γ Δ Θ : List Ty} {a : Ty} (e : Expr Γ a)
    (θ : signature.Substitution Γ Δ) (ψ : signature.Substitution Δ Θ) :
    (e.subst θ).subst ψ = e.subst (fun a x => (θ a x).subst ψ) := Term.subst_subst e θ ψ

/-! ## Environments -/

/-- Extension reads the new value at the nearest position and the old values above it. -/
example {Γ : List Ty} {a b : Ty} (x : Ty.Value a) (η : Env Ty.Value Γ) (v : ScopedVar Γ b) :
    Env.cons x η a .zero = x ∧ Env.cons x η b (.succ v) = η b v := by
  simp

/-- A one-variable environment is an extension of the empty one. -/
example {a : Ty} (x : Ty.Value a) : Env.single x a .zero = x := by
  simp

/-- A lambda body reads its argument from a one-variable environment. -/
example : algebra (.lam .nat .nat) (fun _ η => η .nat .zero + 1) 4 = 5 := rfl

/-- Renamings are environments of variables: reading through two renamings reads through their
composite. -/
example {Γ Δ Θ : List Ty} {a : Ty} (e : Expr Γ a) (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ)
    (η : Env Ty.Value Θ) :
    ((e.rename ρ).rename τ).denote algebra η =
      e.denote algebra (Env.rename (Env.rename ρ τ) η) := by
  rw [Term.rename_rename, Term.denote_rename]

/-- Substitution after renaming reads the substitution through the renaming. -/
example {Γ Δ Θ : List Ty} {a : Ty} (e : Expr Γ a) (ρ : Renaming Γ Δ)
    (θ : signature.Substitution Δ Θ) :
    (e.rename ρ).subst θ = e.subst (Env.rename ρ θ) := Term.subst_rename e ρ θ

/-- Weakening a closed program does not change its meaning. -/
example (x : Ty.Value .nat) :
    ((sumTo 3).rename (fun _ => ScopedVar.succ) : Expr [.nat] .nat).denote algebra
      (Env.single x) = 3 := by
  rw [Term.denote_rename]
  rfl

/-- Positional reindexing along a sort map that identifies two sorts keeps both bindings. -/
example :
    let η : Env (fun _ : Ty => Nat) [.nat, .arrow .nat .nat] := Env.cons 1 (Env.cons 2 Env.empty)
    let ζ := Env.reindex (fun _ : Ty => ()) (V := fun _ => Nat) η
    ζ () .zero = 1 ∧ ζ () (.succ .zero) = 2 := ⟨rfl, rfl⟩

/-- Mapping a renaming along sorts is positional reindexing of its variables. -/
example {Γ Δ : List Ty} (f : Ty → Unit) (ρ : Renaming Γ Δ) {a : Ty} (x : ScopedVar Γ a) :
    Renaming.map f ρ (f a) (x.map f) = (ρ a x).map f := by
  simp

/-- Positional relations need no order on the values. -/
example {Γ : List Ty} {a : Ty} (η ζ : Env (fun _ : Ty => Nat) Γ)
    (h : Env.Forall₂ (fun _ _ m n => m ≤ n) η ζ) :
    Env.Forall₂ (fun _ _ m n => m ≤ n) (Env.cons (a := a) 1 η) (Env.cons (a := a) 2 ζ) :=
  h.cons (by decide)

/-- An environment is related to its reindexing at each original binding position. -/
example (f : Ty → Unit) {Γ : List Ty} (η : Env (fun _ : Ty => Nat) Γ) :
    Env.Forall₂ (fun _ _ m n => m = n) η (Env.reindex f (V := fun _ => Nat) η) :=
  Env.forall₂_reindex_right_iff.mpr fun _ _ => rfl

/-- Positions past the shorter context are unconstrained. -/
example {Δ : List Ty} (R : ∀ _ b, Nat → Ty.Value b → Prop) (ζ : Env Ty.Value Δ) :
    Env.Forall₂ R (Env.empty (V := fun _ : Ty => Nat)) ζ := by
  intro _ _ x
  nomatch x

/-- Reindexing a relation on one side preserves it, with no order on the values. -/
example (f : Ty → Unit) {Γ : List Ty} (η ζ : Env (fun _ : Ty => Nat) Γ)
    (h : Env.Forall₂ (fun _ _ m n => m ≤ n) η ζ) :
    Env.Forall₂ (fun _ _ m n => m ≤ n) η (Env.reindex f (V := fun _ => Nat) ζ) ∧
      Env.Forall₂ (fun _ _ m n => m ≤ n) (Env.reindex f (V := fun _ => Nat) η) ζ :=
  ⟨h.reindex_right, h.reindex_left⟩

/-- The empty environment reindexes to the empty environment. -/
example (f : Ty → Unit) :
    Env.reindex f (V := fun _ => Nat) (Env.empty : Env (fun _ : Ty => Nat) []) = Env.empty := by
  simp

/-- Mapping a renaming along sorts is defined as positional reindexing. -/
example {Γ Δ : List Ty} (f : Ty → Unit) (ρ : Renaming Γ Δ) :
    Renaming.map f ρ = Env.reindex f fun a x => (ρ a x).map f := rfl

/-- Exchange two bindings of the same sort. -/
def swap : Renaming [Ty.nat, .nat] [Ty.nat, .nat] := Env.cons (.succ .zero) (Env.single .zero)

/-- Renaming keeps bindings of equal sorts apart, and the swap is an involution. -/
example (η : Env Ty.Value [Ty.nat, .nat]) :
    Env.rename swap (Env.cons (V := Ty.Value) (a := .nat) 1 (Env.single 2)) .nat .zero = 2 ∧
      Env.rename (Env.rename swap swap) η = η := by
  refine ⟨rfl, ?_⟩
  funext a x
  cases x with
  | zero => rfl
  | succ x =>
    cases x with
    | zero => rfl
    | succ x => nomatch x

end PolyFunTest.Scoped
