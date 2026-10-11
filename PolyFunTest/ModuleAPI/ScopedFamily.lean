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

example {I : Type} {P : Endo I} {X : I → Type} {i j : I}
    (s : PLift (i = j)) (t : IFreeM P X i) :
    t.traverse (Traversal.identity P) (fun s x => .pure (s.down ▸ x)) s = s.down ▸ t := by
  simp

example {S : Type} {Γ Δ : List S} (hΓ : Γ = Γ) (hΔ : Δ = Δ)
    (ρ : ScopedSignature.Renaming Γ Δ) :
    (ScopedSignature.Renaming.cast hΓ hΔ ρ : ScopedSignature.Renaming Γ Δ) = @ρ := by
  simp

example {S : Type} {Γ Γ' Δ Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (ρ : ScopedSignature.Renaming Γ Δ) :
    HEq (ScopedSignature.Renaming.cast hΓ hΔ ρ : ScopedSignature.Renaming Γ' Δ') (@ρ) := by
  simp

example {W : Type} {S : W → Type} {σ τ υ : ScopedFamily W S}
    {M N : W → W → Type} {f : ∀ {w z}, M w z → S w → S z}
    {g : ∀ {w z}, N w z → S w → S z}
    (h : ScopedFamily.Hom σ τ M f) (k : ScopedFamily.Hom τ υ N g)
    {w z y : W} (μ : M w z) (ν : N z y) {Γ : List (S w)} {a : S w}
    (t : σ.Term w Γ a) :
    ((t.map h μ).map k ν).cast List.map_map rfl = t.map (h.comp k) ⟨z, μ, ν⟩ :=
  ScopedFamily.Term.map_map h k μ ν t

example {W : Type} {S : W → Type} {σ : ScopedFamily W S}
    {w z : W} (e : PLift (w = z)) {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a) :
    HEq (t.map (ScopedFamily.Hom.identity σ) e) t := by
  simp

example {W : Type} {S : W → Type} {σ : ScopedFamily W S}
    {w : W} (e : PLift (w = w)) {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a)
    (hΓ : Γ.map id = Γ) (ha : a = a) :
    (t.map (ScopedFamily.Hom.identity σ) e).cast hΓ ha = t := by
  simp

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

example {W : Type} {S : W → Type} {σ : ScopedFamily W S} (A : σ.ReindexAction)
    (hA : A.Lawful σ) {w : W} {Γ Δ Θ : List (S w)} {a : S w}
    (t : σ.Term w Γ a) (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ) :
    (t.subst A θ).subst A τ = t.subst A (fun x => (θ x).subst A τ) :=
  ScopedFamily.Term.subst_subst A hA t θ τ

example {W : Type} {S : W → Type} {σ : ScopedFamily W S} (A : σ.ReindexAction)
    (hA : A.Lawful σ) {w : W} {Γ Δ : List (S w)} {a b : S w}
    (body : σ.Term w (a :: Γ) b) (θ : σ.Substitution Γ Δ) (value : σ.Term w Δ a) :
    (body.subst A (ScopedFamily.Substitution.lift θ a)).substOne A value =
      body.subst A (ScopedFamily.Substitution.cons θ value) :=
  ScopedFamily.Term.substOne_subst_lift A hA body θ value

example {W : Type} {S : W → Type} {σ : ScopedFamily W S} {w : W}
    {Γ Δ : List (S w)} {a b : S w} (hΓ : Γ = Δ) (ha : a = b) (t : σ.Term w Γ a) :
    HEq (t.cast hΓ ha) t := by simp

/-- Identifying two free type parameters does not identify their value bindings. -/
example :
    let olderParameter : Examples.ScopedFamily.Term 2
        [.mono (.param 0), .mono (.param 1)] (.mono (.param 1)) := .pure (.succ .zero)
    Examples.ScopedFamily.erase
    (olderParameter.map Examples.ScopedFamily.parameterHom
      (fun _ => (0 : Fin 1))) = .var 1 := by
  dsimp only
  rw [Examples.ScopedFamily.erase_parameters]
  rfl

example : Examples.ScopedFamily.erase
    (Examples.ScopedFamily.ambientValue.rename (ScopedVar.succ
      (b := Examples.ScopedFamily.ValueSort.mono .bit))) = .lam (.var 2) :=
  Examples.ScopedFamily.erase_rename_ambientValue
