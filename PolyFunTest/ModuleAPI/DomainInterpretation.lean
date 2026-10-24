/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Examples.Tutorials.ScopedDomains

/-! # Ordinary-import checks for continuous interpretations of scoped syntax -/

open OmegaCompletePartialOrder IPFunctor IPFunctor.ScopedSignature

/-! ## Generic equations -/

example {S : Type} {σ : ScopedSignature S} {D : S → PointedDomain}
    (alg : DomainInterpretation σ D) {Γ : List S} {a : S} (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p))
    (η : ScopedDomain.Env D Γ) :
    (Term.node op args).denoteDomain alg η =
      alg op (fun p => DomainInterpretation.under ((args p).denoteDomain alg) η) := rfl

example {S : Type} {σ : ScopedSignature S} {D : S → PointedDomain}
    (alg : DomainInterpretation σ D) {Γ : List S} {a b : S}
    (body : σ.Term (a :: Γ) b) (value : σ.Term Γ a) (η : ScopedDomain.Env D Γ) :
    (body.substOne value).denoteDomain alg η =
      body.denoteDomain alg (ScopedDomain.Env.cons D (value.denoteDomain alg η) η) :=
  Term.denoteDomain_substOne alg body value η

/-! ## The tutorial's definitional facts survive the module boundary -/

open Examples.ScopedDomains

example : meaning (.app (.lam .zero) diverge) = number 0 := rfl

example : (Expr.app (.lam .zero) diverge).denote evaluator Env.empty = none := rfl

example (t : Expr [] .nat) (n : ℕ) (h : t.denote evaluator Env.empty = some n) :
    meaning t = number n :=
  meaning_eq_number t n h
