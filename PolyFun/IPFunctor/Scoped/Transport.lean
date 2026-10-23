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

universe u v w x

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

/-- Composing sort maps retains the original binding position. -/
theorem map_map {U : Type w} (f : S → T) (g : T → U)
    {Γ : List S} {a : S} (x : ScopedVar Γ a) :
    (List.map_map ▸ (x.map f).map g) = x.map (g ∘ f) := by
  induction x with
  | @zero Γ a => exact cast_zero List.map_map _
  | @succ Γ a b x ih =>
      change (congrArg (g (f b) :: ·) (List.map_map (l := Γ)) ▸
        succ ((x.map f).map g)) = succ (x.map (g ∘ f))
      rw [cast_succ (List.map_map (l := Γ)), ih]

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

/-- Applying a sort-indexed function commutes with positional lookup. -/
theorem mapLookup_postcomp (f : S → T) {V : T → Type w} {U : T → Type x}
    {Γ : List S} (η : ∀ {a}, ScopedVar Γ a → V (f a))
    (k : ∀ b, V b → U b) {b : T} (x : ScopedVar (Γ.map f) b) :
    k b (mapLookup f η x) = mapLookup f (fun x => k _ (η x)) x := by
  induction x using map_inductionOn f with
  | h a x => simp only [mapLookup_map]

/-- Lookup through two sort maps is lookup through their composite. -/
theorem mapLookup_comp {U : Type w} (f : S → T) (g : T → U) {V : U → Type x}
    {Γ : List S} (η : ∀ {a}, ScopedVar Γ a → V (g (f a)))
    {b : U} (x : ScopedVar ((Γ.map f).map g) b) :
    mapLookup g (fun x => mapLookup f (V := fun b => V (g b)) η x) x =
      mapLookup (g ∘ f) η (List.map_map ▸ x) := by
  induction x using map_inductionOn g with
  | h a x =>
      induction x using map_inductionOn f with
      | h a x => simp only [mapLookup_map, map_map]

/-- Equal sort maps and pointwise assignments give the same positional lookup. -/
theorem mapLookup_heq {f g : S → T} {V U : T → Type w} {Γ : List S}
    (hf : f = g) (hV : V = U)
    {η : ∀ {a}, ScopedVar Γ a → V (f a)}
    {θ : ∀ {a}, ScopedVar Γ a → U (g a)}
    (h : ∀ {a} (x : ScopedVar Γ a), HEq (η x) (θ x)) :
    HEq (mapLookup f η : ∀ {b}, ScopedVar (Γ.map f) b → V b)
      (mapLookup g θ : ∀ {b}, ScopedVar (Γ.map g) b → U b) := by
  cases hf
  cases hV
  have he : @η = @θ := by
    funext a x
    exact eq_of_heq (h x)
  cases he
  rfl

end IPFunctor.ScopedVar

namespace IPFunctor.ScopedSignature.Renaming

variable {S : Type u} {T : Type v} {Γ Δ Θ : List S}

/-- Normalize the two contexts of a renaming. -/
@[expose] def cast {Γ' Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (ρ : Renaming Γ Δ) : Renaming Γ' Δ' := hΔ ▸ hΓ ▸ ρ

@[simp] theorem cast_self (hΓ : Γ = Γ) (hΔ : Δ = Δ) (ρ : Renaming Γ Δ) :
    (cast hΓ hΔ ρ : Renaming Γ Δ) = @ρ := rfl

theorem cast_apply {Γ' Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (ρ : Renaming Γ Δ) {a : S} (x : ScopedVar Γ a) :
    cast hΓ hΔ ρ (hΓ ▸ x) = hΔ ▸ ρ x := by
  cases hΓ
  cases hΔ
  rfl

/-- Context normalization only changes the type of a renaming. -/
@[simp] theorem cast_heq {Γ' Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (ρ : Renaming Γ Δ) : HEq (cast hΓ hΔ ρ : Renaming Γ' Δ') (@ρ) := by
  cases hΓ
  cases hΔ
  rfl

/-- Context normalization commutes with protecting a fresh binder. -/
theorem cast_lift {Γ' Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (ρ : Renaming Γ Δ) (a : S) :
    (cast (congrArg (a :: ·) hΓ) (congrArg (a :: ·) hΔ) (lift ρ a) :
      Renaming (a :: Γ') (a :: Δ')) =
      (fun {_} x => lift (cast hΓ hΔ ρ) a x) := by
  cases hΓ
  cases hΔ
  rfl

/-- Reindex both contexts of a renaming, retaining their variable positions. -/
@[expose] def map (f : S → T) (ρ : Renaming Γ Δ) : Renaming (Γ.map f) (Δ.map f) :=
  ScopedVar.mapLookup f (fun x => (ρ x).map f)

@[simp] theorem map_apply (f : S → T) (ρ : Renaming Γ Δ) {a : S}
    (x : ScopedVar Γ a) : map f ρ (x.map f) = (ρ x).map f :=
  ScopedVar.mapLookup_map f _ x

/-- Equal sort functions induce the same positional renaming. -/
theorem map_heq {f g : S → T} (h : f = g) (ρ : Renaming Γ Δ) :
    HEq (map f ρ : Renaming _ _) (map g ρ : Renaming _ _) := by
  cases h
  rfl

theorem map_lift (f : S → T) (ρ : Renaming Γ Δ) (a : S) :
    (map f (lift ρ a) : Renaming _ _) = (fun {_} x => lift (map f ρ) (f a) x) := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h b x =>
      rw [map_apply]
      cases x <;> simp only [lift, ScopedVar.map, map_apply]

/-- Mapping sorts commutes with lifting under a block of value binders. -/
theorem map_liftMany (f : S → T) (ρ : Renaming Γ Δ) (Ξ : List S) :
    (cast List.map_append List.map_append (map f (liftMany ρ Ξ)) : Renaming _ _) =
      (fun {_} x => liftMany (map f ρ) (Ξ.map f) x) := by
  induction Ξ with
  | nil => rfl
  | cons a Ξ ih =>
      change (cast (congrArg (f a :: ·) List.map_append)
        (congrArg (f a :: ·) List.map_append) (map f (lift (liftMany ρ Ξ) a)) : Renaming _ _) = _
      rw [map_lift, cast_lift
        (show (Ξ ++ Γ).map f = Ξ.map f ++ Γ.map f from List.map_append)
        (show (Ξ ++ Δ).map f = Ξ.map f ++ Δ.map f from List.map_append), ih]
      rfl

/-- Mapping a renaming twice agrees with composing the sort maps. -/
theorem map_map {U : Type w} (f : S → T) (g : T → U) (ρ : Renaming Γ Δ) :
    (cast List.map_map List.map_map (map g (map f ρ)) : Renaming _ _) =
      (fun {_} x => map (g ∘ f) ρ x) := by
  funext b x
  induction x using ScopedVar.map_inductionOn (g ∘ f) with
  | h a x =>
      rw [← ScopedVar.map_map f g x, cast_apply, map_apply, map_apply,
        ScopedVar.map_map f g (ρ x), ScopedVar.map_map f g x, map_apply]

/-- Lifting respects equality of the two contexts and the fresh binding block. -/
theorem liftMany_heq {Γ' Δ' Ξ Ξ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {ρ : Renaming Γ Δ} {τ : Renaming Γ' Δ'} (hρ : HEq (@ρ) (@τ)) (hΞ : Ξ = Ξ') :
    HEq (liftMany ρ Ξ : Renaming _ _) (liftMany τ Ξ' : Renaming _ _) := by
  cases hΓ
  cases hΔ
  cases hΞ
  cases eq_of_heq hρ
  rfl

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
