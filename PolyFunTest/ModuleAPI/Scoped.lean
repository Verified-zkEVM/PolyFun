/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedPrograms
import PolyFun.IPFunctor.Scoped.Reindex

/-!
# Ordinary-import checks for binding syntax

These checks exercise capture avoidance, the shared fold theorem, and a
noninjective change of sorts without opening implementation bodies.
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

example {Γ Δ Θ : List Ty} {a : Ty} (e : Expr Γ a)
    (θ : signature.Substitution Γ Δ) (ψ : signature.Substitution Δ Θ) :
    (e.subst θ).subst ψ = e.subst (fun x => (θ x).subst ψ) := Term.subst_subst e θ ψ

end PolyFunTest.Scoped
