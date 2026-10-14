/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Examples.Tutorials.ScopedFamily
import PolyFun.IPFunctor.Scoped.FamilyMapSubstitution
import PolyFun.IPFunctor.Scoped.FamilyMapCongr
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

example {W : Type} {S : W → Type} {σ : ScopedFamily W S} {w : W}
    {Γ Δ Γ' Δ' : List (S w)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (θ : σ.Substitution Γ Δ) :
    HEq (θ.cast hΓ hΔ : σ.Substitution Γ' Δ') (@θ) := by simp

example {W : Type} {S : W → Type} {σ τ : ScopedFamily W S}
    {M : W → W → Type} {f : ∀ {w z}, M w z → S w → S z}
    (h : ScopedFamily.Hom σ τ M f) (A : σ.ReindexAction) (B : τ.ReindexAction)
    (compatible : h.PreservesReindex A B) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} {a : S w} (θ : σ.Substitution Γ Δ) (t : σ.Term w Γ a) :
    (t.subst A θ).map h μ = (t.map h μ).subst B (θ.map h μ) :=
  ScopedFamily.Term.map_subst h A B (compatible.preservesSubstitution h A B) μ θ t

/-- A noninjective type map retains both positional assignments. -/
example :
    let f : Bool → Unit := fun _ => ()
    let θ : ∀ {a}, ScopedVar [true, false] a → Nat := fun {_} x => x.index + 7
    (ScopedVar.mapLookup f (Γ := [true, false]) (V := fun _ => Nat) θ
        (ScopedVar.zero : ScopedVar [(), ()] ()),
      ScopedVar.mapLookup f (Γ := [true, false]) (V := fun _ => Nat) θ
        (ScopedVar.succ .zero : ScopedVar [(), ()] ())) = (7, 8) := rfl

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

universe uScope uSort uOp uArg

/-- Related traversals retain arbitrary endpoint equality witnesses at independent universes. -/
example {W : Type uScope} {S : W → Type uSort}
    {σ : ScopedFamily.{uScope, uSort, uOp, uArg} W S}
    {a b c : W} (μ : PLift (a = b)) (ν : PLift (a = c))
    {Γ : List (S a)} {s : S a} (t : σ.Term a Γ s) :
    HEq (t.map (ScopedFamily.Hom.identity σ) μ)
      (t.map (ScopedFamily.Hom.identity σ) ν) := by
  apply ScopedFamily.Term.map_congr (ScopedFamily.Hom.identity σ)
    (ScopedFamily.Hom.identity σ) (fun _ _ => True) ?_ ?_ ?_ ?_ ?_ trivial t
  · intro a b c μ ν _
    exact μ.down.symm.trans ν.down
  · intro a b c μ ν _
    cases μ.down
    cases ν.down
    rfl
  · intro a b c μ ν _ s op
    cases μ.down
    cases ν.down
    rfl
  · intro a b c μ ν _ s op p q he
    cases μ.down
    cases ν.down
    exact eq_of_heq he
  · intros
    trivial
