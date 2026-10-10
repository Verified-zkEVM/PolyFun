/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Examples.Tutorials.ScopedFamily
import PolyFun.IPFunctor.Scoped.FamilySubstitution
import PolyFun.IPFunctor.Scoped.Domain

/-! # Ordinary-import checks for context-changing binding families -/

open IPFunctor

example {n m : Nat} (ρ : Fin n → Fin m)
    {Γ : List (Examples.ScopedFamily.ValueSort n)} {s : Examples.ScopedFamily.ValueSort n}
    (t : Examples.ScopedFamily.Term n Γ s) :
    Examples.ScopedFamily.erase (t.map Examples.ScopedFamily.parameterHom ρ) =
      Examples.ScopedFamily.erase t := Examples.ScopedFamily.erase_parameters ρ t

example {S : Type} {σ : ScopedSignature S} {Γ : List S} {a : S} (t : σ.Term Γ a) :
    ScopedSignature.Term.fromFamily t.toFamily = t :=
  ScopedSignature.Term.fromFamily_toFamily t

example {W : Type} {S : W → Type} {σ : ScopedFamily W S} (A : σ.ReindexAction)
    {w : W} {Γ Δ Θ : List (S w)} {a : S w} (t : σ.Term w Γ a)
    (ρ : ScopedSignature.Renaming Γ Δ) (θ : σ.Substitution Δ Θ) :
    (t.rename ρ).subst A θ = t.subst A (fun x => θ (ρ x)) :=
  ScopedFamily.Term.subst_rename A ρ θ t
