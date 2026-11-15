/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Renaming

/-!
# Context lookup through a change of sorts

`Env.reindex f` moves an environment of `Γ` to the context `Γ.map f`. Lookup follows
the original binding position, so `f` need not be injective: variables remain
distinct when their instantiated sorts agree. Mapping a renaming along a sort map is
an instance.
-/

public section

universe u v w x z

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

namespace IPFunctor.ScopedSignature.Env

variable {S : Type u} {T : Type v}

/-- Read a mapped context using an environment of its original binding positions. -/
@[expose] def reindex (f : S → T) {V : T → Type w} :
    {Γ : List S} → Env (fun a => V (f a)) Γ → Env V (Γ.map f)
  | _ :: _, η, _, .zero => η _ .zero
  | _ :: _, η, _, .succ x => reindex f (fun a x => η a (.succ x)) _ x

@[deprecated (since := "2026-11-07")] alias _root_.IPFunctor.ScopedVar.mapLookup := reindex

/-- Looking up an explicitly mapped variable retrieves its original value. -/
@[simp] theorem reindex_map (f : S → T) {V : T → Type w} {Γ : List S}
    (η : Env (fun a => V (f a)) Γ) {a : S} (x : ScopedVar Γ a) :
    reindex f η (f a) (x.map f) = η a x := by
  induction x with
  | zero => rfl
  | succ x ih => exact ih _

@[deprecated (since := "2026-11-07")] alias _root_.IPFunctor.ScopedVar.mapLookup_map :=
  reindex_map

/-- Reindexing the empty environment gives the empty environment. -/
@[simp] theorem reindex_empty (f : S → T) {V : T → Type w} :
    reindex f (empty : Env (fun a => V (f a)) []) = empty :=
  eq_empty _

/-- Reindexing keeps the nearest binding and reindexes the older positions. -/
@[simp] theorem reindex_cons (f : S → T) {V : T → Type w} {Γ : List S} {a : S}
    (x : V (f a)) (η : Env (fun a => V (f a)) Γ) :
    reindex f (cons x η) = cons x (reindex f η) := by
  funext b v
  cases v <;> rfl

/-- Applying a sort-indexed function commutes with positional lookup. -/
theorem reindex_postcomp (f : S → T) {V : T → Type w} {U : T → Type x}
    {Γ : List S} (η : Env (fun a => V (f a)) Γ)
    (k : ∀ b, V b → U b) {b : T} (x : ScopedVar (Γ.map f) b) :
    k b (reindex f η b x) = reindex f (fun a x => k (f a) (η a x)) b x := by
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [reindex_map]

@[deprecated (since := "2026-11-07")] alias _root_.IPFunctor.ScopedVar.mapLookup_postcomp :=
  reindex_postcomp

/-- Lookup through two sort maps is lookup through their composite. -/
theorem reindex_comp {U : Type w} (f : S → T) (g : T → U) {V : U → Type x}
    {Γ : List S} (η : Env (fun a => V (g (f a))) Γ)
    {b : U} (x : ScopedVar ((Γ.map f).map g) b) :
    reindex g (reindex f (V := fun b => V (g b)) η) b x =
      reindex (g ∘ f) η b (List.map_map ▸ x) := by
  induction x using ScopedVar.map_inductionOn g with
  | h a x =>
      induction x using ScopedVar.map_inductionOn f with
      | h a x =>
          rw [reindex_map, reindex_map, ScopedVar.map_map]
          exact (reindex_map (g ∘ f) η x).symm

@[deprecated (since := "2026-11-07")] alias _root_.IPFunctor.ScopedVar.mapLookup_comp :=
  reindex_comp

/-- Equal sort maps and positionwise equal values give the same lookup. -/
theorem reindex_heq {f g : S → T} {V U : T → Type w} {Γ : List S}
    (hf : f = g) (hV : V = U)
    {η : Env (fun a => V (f a)) Γ} {θ : Env (fun a => U (g a)) Γ}
    (h : ∀ a (x : ScopedVar Γ a), HEq (η a x) (θ a x)) :
    HEq (reindex f η) (reindex g θ) := by
  cases hf
  cases hV
  have he : η = θ := by
    funext a x
    exact eq_of_heq (h a x)
  cases he
  rfl

@[deprecated (since := "2026-11-07")] alias _root_.IPFunctor.ScopedVar.mapLookup_heq :=
  reindex_heq

/-- Context transport preserves lookup at the corresponding binding position. -/
theorem cast_apply {V : S → Type z} {Γ Δ : List S} (h : Γ = Δ) (η : Env V Γ)
    {a : S} (x : ScopedVar Γ a) : (h ▸ η) a (h ▸ x) = η a x := by
  cases h
  rfl

/-- Move an environment along an equation of contexts. -/
@[expose] def castCtx {V : S → Type z} {Γ Γ' : List S} (h : Γ = Γ') (η : Env V Γ) :
    Env V Γ' := h ▸ η

@[simp] theorem castCtx_rfl {V : S → Type z} {Γ : List S} (η : Env V Γ) :
    castCtx rfl η = η := rfl

/-- Transport along an equation of contexts keeps the environment. -/
theorem castCtx_heq {V : S → Type z} {Γ Γ' : List S} (h : Γ = Γ') (η : Env V Γ) :
    HEq (castCtx h η) η := by
  subst h
  rfl

end IPFunctor.ScopedSignature.Env

namespace IPFunctor.ScopedSignature.Renaming

variable {S : Type u} {T : Type v} {Γ Δ Θ : List S}

/-- Normalize the two contexts of a renaming. -/
@[expose] def cast {Γ' Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (ρ : Renaming Γ Δ) : Renaming Γ' Δ' := hΔ ▸ hΓ ▸ ρ

@[simp] theorem cast_self (hΓ : Γ = Γ) (hΔ : Δ = Δ) (ρ : Renaming Γ Δ) :
    cast hΓ hΔ ρ = ρ := rfl

theorem cast_apply {Γ' Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (ρ : Renaming Γ Δ) {a : S} (x : ScopedVar Γ a) :
    cast hΓ hΔ ρ a (hΓ ▸ x) = hΔ ▸ ρ a x := by
  cases hΓ
  cases hΔ
  rfl

/-- Context normalization only changes the type of a renaming. -/
@[simp] theorem cast_heq {Γ' Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (ρ : Renaming Γ Δ) : HEq (cast hΓ hΔ ρ) ρ := by
  cases hΓ
  cases hΔ
  rfl

/-- Context normalization commutes with protecting a fresh binder. -/
theorem cast_lift {Γ' Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (ρ : Renaming Γ Δ) (a : S) :
    cast (congrArg (a :: ·) hΓ) (congrArg (a :: ·) hΔ) (lift ρ a) =
      lift (cast hΓ hΔ ρ) a := by
  cases hΓ
  cases hΔ
  rfl

/-- Reindex both contexts of a renaming, retaining their variable positions. -/
@[expose] def map (f : S → T) (ρ : Renaming Γ Δ) : Renaming (Γ.map f) (Δ.map f) :=
  Env.reindex f fun a x => (ρ a x).map f

@[simp] theorem map_apply (f : S → T) (ρ : Renaming Γ Δ) {a : S}
    (x : ScopedVar Γ a) : map f ρ (f a) (x.map f) = (ρ a x).map f :=
  Env.reindex_map f _ x

/-- Equal sort functions induce the same positional renaming. -/
theorem map_heq {f g : S → T} (h : f = g) (ρ : Renaming Γ Δ) :
    HEq (map f ρ) (map g ρ) := by
  cases h
  rfl

theorem map_lift (f : S → T) (ρ : Renaming Γ Δ) (a : S) :
    map f (lift ρ a) = lift (map f ρ) (f a) := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h b x =>
      rw [map_apply]
      cases x <;> simp only [lift, ScopedVar.map, map_apply]

/-- Mapping sorts commutes with lifting under a block of value binders. -/
theorem map_liftMany (f : S → T) (ρ : Renaming Γ Δ) (Ξ : List S) :
    cast List.map_append List.map_append (map f (liftMany ρ Ξ)) =
      liftMany (map f ρ) (Ξ.map f) := by
  induction Ξ with
  | nil => rfl
  | cons a Ξ ih =>
      change cast (congrArg (f a :: ·) List.map_append)
        (congrArg (f a :: ·) List.map_append) (map f (lift (liftMany ρ Ξ) a)) = _
      rw [map_lift, cast_lift
        (show (Ξ ++ Γ).map f = Ξ.map f ++ Γ.map f from List.map_append)
        (show (Ξ ++ Δ).map f = Ξ.map f ++ Δ.map f from List.map_append), ih]
      rfl

/-- Mapping a renaming twice agrees with composing the sort maps. -/
theorem map_map {U : Type w} (f : S → T) (g : T → U) (ρ : Renaming Γ Δ) :
    cast List.map_map List.map_map (map g (map f ρ)) = map (g ∘ f) ρ := by
  funext b x
  induction x using ScopedVar.map_inductionOn (g ∘ f) with
  | h a x =>
      change cast _ _ _ (g (f a)) _ = map (g ∘ f) ρ (g (f a)) _
      rw [← ScopedVar.map_map f g x, cast_apply, map_apply, map_apply,
        ScopedVar.map_map f g (ρ a x), ScopedVar.map_map f g x]
      exact (map_apply (g ∘ f) ρ x).symm

/-- Lifting respects equality of the two contexts and the fresh binding block. -/
theorem liftMany_heq {Γ' Δ' Ξ Ξ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {ρ : Renaming Γ Δ} {τ : Renaming Γ' Δ'} (hρ : HEq ρ τ) (hΞ : Ξ = Ξ') :
    HEq (liftMany ρ Ξ) (liftMany τ Ξ') := by
  cases hΓ
  cases hΔ
  cases hΞ
  cases eq_of_heq hρ
  rfl

/-- Renamings between equal contexts that produce the same binding positions are
heterogeneously equal. -/
theorem heq_of_index {Γ' Δ' : List S} (hΓ : Γ = Γ') (hΔ : Δ = Δ') {ρ : Renaming Γ Δ}
    {τ : Renaming Γ' Δ'}
    (h : ∀ a b (x : ScopedVar Γ a) (y : ScopedVar Γ' b), x.index = y.index →
      (ρ a x).index = (τ b y).index) : HEq ρ τ := by
  subst hΓ hΔ
  apply heq_of_eq
  funext a x
  exact eq_of_heq (Sigma.mk.inj_iff.mp
    (ScopedVar.sigma_eq_of_index_eq (ρ a x) (τ a x) (h a a x x rfl))).2

@[simp] theorem map_id (f : S → T) :
    map f (fun _ x => x : Renaming Γ Γ) = fun _ x => x := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => exact map_apply f _ x

end IPFunctor.ScopedSignature.Renaming

namespace IPFunctor.ScopedSignature.Env

variable {S : Type u} {T : Type v} {Γ Δ : List S}

/-- Changing sorts commutes with reading through a renaming, even for noninjective maps. -/
theorem reindex_rename (f : S → T) {V : T → Type w} (ρ : Renaming Γ Δ)
    (η : Env (fun a => V (f a)) Δ) :
    reindex f (rename ρ η) = rename (Renaming.map f ρ) (reindex f η) := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [reindex_map, rename_apply, Renaming.map_apply]

end IPFunctor.ScopedSignature.Env

namespace IPFunctor.ScopedSignature.Renaming

variable {S : Type u} {T : Type v} {Γ Δ Θ : List S}

/-- Mapping a context commutes with composing its renamings. -/
theorem map_comp (f : S → T) (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) :
    map f (Env.rename ρ τ) = Env.rename (map f ρ) (map f τ) :=
  Env.reindex_rename f ρ fun a x => (τ a x).map f

end IPFunctor.ScopedSignature.Renaming
