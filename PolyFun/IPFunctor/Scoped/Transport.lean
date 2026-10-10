/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Renaming

/-!
# Context lookup through a change of sorts

Reindexing a context need not be injective on sorts. Lookup follows the original
binding position, so variables remain distinct when their instantiated types agree.
-/

public section

universe u v w

namespace IPFunctor.ScopedVar

variable {S : Type u} {T : Type v}

/-- Context transport leaves the nearest binding position unchanged. -/
theorem cast_zero {Γ Δ : List S} (h : Γ = Δ) (a : S) :
    (congrArg (a :: ·) h ▸ (zero : ScopedVar (a :: Γ) a)) = zero := by
  cases h
  rfl

/-- Context transport commutes with moving past a binding. -/
theorem cast_succ {Γ Δ : List S} (h : Γ = Δ) {a b : S} (x : ScopedVar Γ a) :
    (congrArg (b :: ·) h ▸ (succ x : ScopedVar (b :: Γ) a)) = succ (h ▸ x) := by
  cases h
  rfl

/-- Mapping the identity sort function is context normalization. -/
theorem map_id {Γ : List S} {a : S} (x : ScopedVar Γ a) :
    x.map id = (List.map_id Γ).symm ▸ x := by
  induction x with
  | @zero Γ a => exact (cast_zero (List.map_id Γ).symm a).symm
  | @succ Γ a b x ih =>
      change succ (x.map id) = (congrArg (b :: ·) (List.map_id Γ).symm ▸ succ x)
      rw [cast_succ, ih]

/-- Read a mapped context using an assignment to its original variable positions. -/
@[expose] def mapLookup (f : S → T) {V : T → Type w} :
    {Γ : List S} → (∀ {a}, ScopedVar Γ a → V (f a)) →
      ∀ {b}, ScopedVar (Γ.map f) b → V b
  | _ :: _, η, _, .zero => η .zero
  | _ :: _, η, _, .succ x => mapLookup f (fun x => η (.succ x)) x

/-- Looking up an explicitly mapped variable retrieves its original assignment. -/
@[simp] theorem mapLookup_map (f : S → T) {V : T → Type w}
    {Γ : List S} (η : ∀ {a}, ScopedVar Γ a → V (f a))
    {a : S} (x : ScopedVar Γ a) : mapLookup f η (x.map f) = η x := by
  induction x with
  | zero => rfl
  | succ x ih => exact ih _

/-- Every variable in a mapped context comes from its original binding position. -/
@[elab_as_elim] theorem map_inductionOn (f : S → T) {Γ : List S}
    {motive : ∀ b, ScopedVar (Γ.map f) b → Prop}
    (h : ∀ a (x : ScopedVar Γ a), motive (f a) (x.map f))
    {b : T} (x : ScopedVar (Γ.map f) b) : motive b x := by
  induction Γ generalizing b with
  | nil => cases x
  | cons a Γ ih =>
      cases x with
      | zero => exact h a .zero
      | succ x =>
          exact ih (motive := fun b x => motive b (.succ x)) (fun a x => h a (.succ x)) x

end IPFunctor.ScopedVar

namespace IPFunctor.ScopedSignature.Renaming

variable {S : Type u} {T : Type v} {Γ Δ Θ : List S}

/-- Reindex both contexts of a renaming, retaining their variable positions. -/
@[expose] def map (f : S → T) (ρ : Renaming Γ Δ) : Renaming (Γ.map f) (Δ.map f) :=
  ScopedVar.mapLookup f (fun x => (ρ x).map f)

@[simp] theorem map_apply (f : S → T) (ρ : Renaming Γ Δ) {a : S}
    (x : ScopedVar Γ a) : map f ρ (x.map f) = (ρ x).map f :=
  ScopedVar.mapLookup_map f _ x

@[simp] theorem map_id (f : S → T) :
    (map f (fun {a} (x : ScopedVar Γ a) => x) : Renaming (Γ.map f) (Γ.map f)) =
      fun {_} x => x := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => exact map_apply f _ x

/-- Mapping a context commutes with composing its renamings. -/
theorem map_comp (f : S → T) (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) :
    (map f (fun x => τ (ρ x)) : Renaming (Γ.map f) (Θ.map f)) =
      fun {_} x => map f τ (map f ρ x) := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [map_apply]

end IPFunctor.ScopedSignature.Renaming
