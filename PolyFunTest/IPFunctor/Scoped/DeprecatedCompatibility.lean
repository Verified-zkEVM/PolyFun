/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.DomainRelation
public import PolyFun.IPFunctor.Scoped.FamilySubstitution
public import PolyFun.IPFunctor.Scoped.Interpretation

/-!
# Deprecated scoped-environment compatibility

Ordinary imports keep the spellings that predate the single environment type. The old
bundled environment type and both `Substitution.cons` keep their signatures. The renamed
continuous-environment lemmas still rewrite goals about the continuous renaming, and the
renamed positional lookup still computes. Each use reports its deprecation.
-/

@[expose] public section

open OmegaCompletePartialOrder IPFunctor

namespace PolyFunTest.Scoped.DeprecatedCompatibility

/--
warning: `IPFunctor.ScopedDomain.Env` has been deprecated: Use `IPFunctor.ScopedSignature.Env` instead

Note: The updated constant has a different type:
  {S : Type u} → (S → Type z) → List S → Type (max u z)
instead of
  {S : Type u} → (S → PointedDomain) → List S → Type (max u z)

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.Env` to `ScopedSignature.Env x`).
-/
#guard_msgs in
example {S : Type} (D : S → PointedDomain) (Γ : List S) :
    ScopedDomain.Env D Γ = ScopedSignature.Env (fun a => D a) Γ := rfl

/--
warning: `IPFunctor.ScopedSignature.Substitution.cons` has been deprecated: Use `IPFunctor.ScopedSignature.Env.cons` instead

Note: The updated constant has a different type:
  {S : Type u} →
    {V : S → Type z} → {Γ : List S} → {a : S} → V a → ScopedSignature.Env V Γ → ScopedSignature.Env V (a :: Γ)
instead of
  {S : Type u} →
    {σ : ScopedSignature S} → {Γ Δ : List S} → {a : S} → σ.Substitution Γ Δ → σ.Term Δ a → σ.Substitution (a :: Γ) Δ

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.cons` to `ScopedSignature.Env.cons x`).
-/
#guard_msgs in
example {S : Type} {σ : ScopedSignature S} {Γ Δ : List S} {a : S}
    (θ : σ.Substitution Γ Δ) (v : σ.Term Δ a) :
    ScopedSignature.Substitution.cons θ v = ScopedSignature.Env.cons v θ := rfl

/--
warning: `IPFunctor.ScopedFamily.Substitution.cons` has been deprecated: Use `IPFunctor.ScopedSignature.Env.cons` instead

Note: The updated constant has a different type:
  {S : Type u} →
    {V : S → Type z} → {Γ : List S} → {a : S} → V a → ScopedSignature.Env V Γ → ScopedSignature.Env V (a :: Γ)
instead of
  {W : Type u} →
    {S : W → Type v} →
      {σ : ScopedFamily W S} →
        {w : W} → {Γ Δ : List (S w)} → {a : S w} → σ.Substitution Γ Δ → σ.Term w Δ a → σ.Substitution (a :: Γ) Δ

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.cons` to `ScopedSignature.Env.cons x`).
-/
#guard_msgs in
example {W : Type} {S : W → Type} {σ : ScopedFamily W S} {w : W} {Γ Δ : List (S w)}
    {a : S w} (θ : σ.Substitution Γ Δ) (v : σ.Term w Δ a) :
    ScopedFamily.Substitution.cons θ v = ScopedSignature.Env.cons v θ := rfl

/--
warning: `IPFunctor.ScopedVar.mapLookup` has been deprecated: Use `IPFunctor.ScopedSignature.Env.reindex` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.mapLookup` to `ScopedSignature.Env.reindex x`).

Hint: Replace the deprecated name:
  S̵c̵o̵p̵e̵d̵V̵a̵r̵.̵m̵a̵p̵L̵o̵o̵k̵u̵p̵S̲c̲o̲p̲e̲d̲S̲i̲g̲n̲a̲t̲u̲r̲e̲.̲E̲n̲v̲.̲r̲e̲i̲n̲d̲e̲x̲
-/
#guard_msgs in
example :
    ScopedVar.mapLookup (fun _ : Bool => ()) (V := fun _ => Nat)
      (fun _ x => x.index + 7 : ScopedSignature.Env (fun _ => Nat) [true, false])
      () (.succ .zero) = 8 := rfl

/--
warning: `IPFunctor.ScopedSignature.Env.pull` has been deprecated: Use `IPFunctor.ScopedSignature.Env.rename` instead

Hint: Replace the deprecated name:
  ScopedSignature.Env.p̵u̵l̵l̵r̲e̲n̲a̲m̲e̲
-/
#guard_msgs in
example {S : Type} {V : S → Type} {Γ Δ : List S} (ρ : ScopedSignature.Renaming Γ Δ)
    (η : ScopedSignature.Env V Δ) :
    ScopedSignature.Env.pull ρ η = ScopedSignature.Env.rename ρ η := rfl

section Continuous

variable {S : Type} {V : S → Type} [∀ a, OmegaCompletePartialOrder (V a)] {Γ Δ : List S}

/--
warning: `IPFunctor.ScopedDomain.Env.rename_id` has been deprecated: Use `IPFunctor.ScopedSignature.Env.renameContinuous_id` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.rename_id` to `ScopedSignature.Env.renameContinuous_id x`).

Hint: Replace the deprecated name:
  S̵c̵o̵p̵e̵d̵D̵o̵m̵a̵i̵n̵.̵E̵n̵v̵.̵r̵e̵n̵a̵m̵e̵_̵i̵d̵S̲c̲o̲p̲e̲d̲S̲i̲g̲n̲a̲t̲u̲r̲e̲.̲E̲n̲v̲.̲r̲e̲n̲a̲m̲e̲C̲o̲n̲t̲i̲n̲u̲o̲u̲s̲_̲i̲d̲
-/
#guard_msgs in
example (η : ScopedSignature.Env V Γ) :
    ScopedSignature.Env.renameContinuous (fun _ x => x) η = η := by
  rw [ScopedDomain.Env.rename_id]

/--
warning: `IPFunctor.ScopedDomain.Env.rename_cons` has been deprecated: Use `IPFunctor.ScopedSignature.Env.renameContinuous_cons` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.rename_cons` to `ScopedSignature.Env.renameContinuous_cons x`).

Hint: Replace the deprecated name:
  S̵c̵o̵p̵e̵d̵D̵o̵m̵a̵i̵n̵.̵E̵n̵v̵.̵r̵e̵n̵a̵m̵e̵_̵c̵o̵n̵s̵S̲c̲o̲p̲e̲d̲S̲i̲g̲n̲a̲t̲u̲r̲e̲.̲E̲n̲v̲.̲r̲e̲n̲a̲m̲e̲C̲o̲n̲t̲i̲n̲u̲o̲u̲s̲_̲c̲o̲n̲s̲
-/
#guard_msgs in
example (ρ : ScopedSignature.Renaming Γ Δ) {a : S} (x : V a) (η : ScopedSignature.Env V Δ) :
    ScopedSignature.Env.renameContinuous (ρ.lift a) (ScopedSignature.Env.cons x η) =
      ScopedSignature.Env.cons x (ScopedSignature.Env.renameContinuous ρ η) := by
  rw [ScopedDomain.Env.rename_cons]

/--
warning: `IPFunctor.ScopedDomain.Env.rename_apply` has been deprecated: Use `IPFunctor.ScopedSignature.Env.renameContinuous_apply_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.rename_apply` to `ScopedSignature.Env.renameContinuous_apply_apply x`).

Hint: Replace the deprecated name:
  S̵c̵o̵p̵e̵d̵D̵o̵m̵a̵i̵n̵.̵E̵n̵v̵.̵r̵e̵n̵a̵m̵e̵_̵a̵p̵p̵l̵y̵S̲c̲o̲p̲e̲d̲S̲i̲g̲n̲a̲t̲u̲r̲e̲.̲E̲n̲v̲.̲r̲e̲n̲a̲m̲e̲C̲o̲n̲t̲i̲n̲u̲o̲u̲s̲_̲a̲p̲p̲l̲y̲_̲a̲p̲p̲l̲y̲
-/
#guard_msgs in
example (ρ : ScopedSignature.Renaming Γ Δ) (η : ScopedSignature.Env V Δ) {a : S}
    (x : ScopedVar Γ a) :
    ScopedSignature.Env.renameContinuous ρ η a x = η a (ρ a x) := by
  rw [ScopedDomain.Env.rename_apply]

/--
warning: `IPFunctor.ScopedDomain.Env.fixGroup_rename` has been deprecated: Use `IPFunctor.ScopedSignature.Env.fixGroup_renameContinuous` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.fixGroup_rename` to `ScopedSignature.Env.fixGroup_renameContinuous x`).

Hint: Replace the deprecated name:
  S̵c̵o̵p̵e̵d̵D̵o̵m̵a̵i̵n̵.̵E̵n̵v̵.̵f̵i̵x̵G̵r̵o̵u̵p̵_̵r̵e̵n̵a̵m̵e̵S̲c̲o̲p̲e̲d̲S̲i̲g̲n̲a̲t̲u̲r̲e̲.̲E̲n̲v̲.̲f̲i̲x̲G̲r̲o̲u̲p̲_̲r̲e̲n̲a̲m̲e̲C̲o̲n̲t̲i̲n̲u̲o̲u̲s̲
-/
#guard_msgs in
example [∀ a, OrderBot (V a)] {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → ScopedSignature.Env V (Ξ ++ Γ) →𝒄 V Ξ[i])
    (ρ : ScopedSignature.Renaming Γ Δ) (η : ScopedSignature.Env V Δ) :
    ScopedSignature.Env.fixGroup rhs (ScopedSignature.Env.renameContinuous ρ η) =
      ScopedSignature.Env.fixGroup
        (fun i => (rhs i).comp (ScopedSignature.Env.renameContinuous (ρ.liftMany Ξ))) η := by
  rw [ScopedDomain.Env.fixGroup_rename]

end Continuous

/--
warning: `IPFunctor.ScopedDomain.Env.reindex` has been deprecated: Use `IPFunctor.ScopedSignature.Env.transport` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.reindex` to `ScopedSignature.Env.transport x`).

Hint: Replace the deprecated name:
  S̵c̵o̵p̵e̵d̵D̵o̵m̵a̵i̵n̵.̵E̵n̵v̵.̵r̵e̵i̵n̵d̵e̵x̵S̲c̲o̲p̲e̲d̲S̲i̲g̲n̲a̲t̲u̲r̲e̲.̲E̲n̲v̲.̲t̲r̲a̲n̲s̲p̲o̲r̲t̲
-/
#guard_msgs in
example {S T : Type} {D : S → PointedDomain} {E : T → PointedDomain} {Γ : List S}
    (f : S → T) (hf : ∀ a, E (f a) = D a) (η : ScopedSignature.Env (fun a => D a) Γ) :
    ScopedDomain.Env.reindex E f hf η = ScopedSignature.Env.transport E f hf η := rfl

end PolyFunTest.Scoped.DeprecatedCompatibility
