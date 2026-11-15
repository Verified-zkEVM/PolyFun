/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.FamilyMap
public import PolyFun.IPFunctor.Scoped.FamilySubstitution
import PolyFun.IPFunctor.Scoped.EnvRelation

/-!
# Substitution through binding-family translations

Parameter translations act on substitution images at their original binding
positions. Compatibility with each constructor's context extension gives the
substitution law for the whole tree.
-/

public section

universe u v w z m

namespace IPFunctor.ScopedFamily

variable {W : Type u} {S : W → Type v}
  {σ τ : ScopedFamily.{u, v, w, z} W S}
  {M : W → W → Type m} {f : ∀ {w z}, M w z → S w → S z}

namespace Substitution

/-- Normalize the source and target contexts of a substitution. -/
@[expose] def cast {w : W} {Γ Δ Γ' Δ' : List (S w)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (θ : σ.Substitution Γ Δ) :
    σ.Substitution Γ' Δ' := hΔ ▸ hΓ ▸ θ

@[simp] theorem cast_self {w : W} {Γ Δ : List (S w)}
    (hΓ : Γ = Γ) (hΔ : Δ = Δ) (θ : σ.Substitution Γ Δ) :
    θ.cast hΓ hΔ = θ := rfl

@[simp] theorem cast_heq {w : W} {Γ Δ Γ' Δ' : List (S w)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (θ : σ.Substitution Γ Δ) :
    HEq (θ.cast hΓ hΔ) θ := by
  cases hΓ
  cases hΔ
  rfl

/-- Reading a normalized substitution only normalizes its result context. -/
theorem cast_apply {w : W} {Γ Δ Γ' Δ' : List (S w)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (θ : σ.Substitution Γ Δ)
    {a : S w} (x : ScopedVar Γ a) :
    cast hΓ hΔ θ a (hΓ ▸ x) = (θ a x).cast hΔ rfl := by
  cases hΓ
  cases hΔ
  rfl

/-- Translate the images of a simultaneous substitution without merging positions. -/
@[expose] def map (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} (θ : σ.Substitution Γ Δ) :
    τ.Substitution (Γ.map (f μ)) (Δ.map (f μ)) :=
  ScopedSignature.Env.reindex (f μ) fun _ x => (θ _ x).map h μ

@[simp] theorem map_apply (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} (θ : σ.Substitution Γ Δ) {a : S w} (x : ScopedVar Γ a) :
    θ.map h μ (f μ a) (x.map (f μ)) = (θ a x).map h μ :=
  ScopedSignature.Env.reindex_map _ _ x

/-- Context normalization commutes with protecting one fresh value variable. -/
theorem cast_lift {w : W} {Γ Δ Γ' Δ' : List (S w)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (θ : σ.Substitution Γ Δ) (a : S w) :
    cast (congrArg (a :: ·) hΓ) (congrArg (a :: ·) hΔ) (lift θ a) =
      lift (cast hΓ hΔ θ) a := by
  cases hΓ
  cases hΔ
  rfl

/-- Parameter translation commutes with protecting one fresh value variable. -/
theorem map_lift (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} (θ : σ.Substitution Γ Δ) (a : S w) :
    map h μ (lift θ a) = lift (map h μ θ) (f μ a) := by
  funext b x
  induction x using ScopedVar.map_inductionOn (f μ) with
  | h b x =>
      rw [map_apply]
      cases x with
      | zero => rfl
      | succ x =>
          simp only [lift, ScopedVar.map, map_apply, Term.map_rename]
          congr 1
          funext b y
          induction y using ScopedVar.map_inductionOn (f μ) with
          | h b y => simp only [ScopedSignature.Renaming.map_apply, ScopedVar.map]

/-- Parameter translation commutes with a whole block of fresh value variables. -/
theorem map_liftMany (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} (θ : σ.Substitution Γ Δ) (Ξ : List (S w)) :
    cast List.map_append List.map_append (map h μ (liftMany θ Ξ)) =
      liftMany (map h μ θ) (Ξ.map (f μ)) := by
  induction Ξ with
  | nil => rfl
  | cons a Ξ ih =>
      change cast (congrArg (f μ a :: ·) List.map_append)
        (congrArg (f μ a :: ·) List.map_append) (map h μ (lift (liftMany θ Ξ) a)) = _
      rw [map_lift, cast_lift
        (show (Ξ ++ Γ).map (f μ) = Ξ.map (f μ) ++ Γ.map (f μ) from List.map_append)
        (show (Ξ ++ Δ).map (f μ) = Ξ.map (f μ) ++ Δ.map (f μ) from List.map_append), ih]
      rfl

/-- Lifting respects equal contexts, images and fresh binding blocks. -/
theorem liftMany_heq {w : W} {Γ Δ Γ' Δ' Ξ Ξ' : List (S w)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {θ : σ.Substitution Γ Δ} {η : σ.Substitution Γ' Δ'}
    (hθ : HEq θ η) (hΞ : Ξ = Ξ') :
    HEq (liftMany θ Ξ) (liftMany η Ξ') := by
  cases hΓ
  cases hΔ
  cases hΞ
  cases eq_of_heq hθ
  rfl

end Substitution

/-- Normalizing a context before substitution also normalizes its variable assignment. -/
theorem Term.cast_subst (A : σ.ReindexAction) {w : W}
    {Γ Δ Γ' Δ' : List (S w)} {a b : S w}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (ha : a = b)
    (θ : σ.Substitution Γ Δ) (t : σ.Term w Γ a) :
    (t.subst A θ).cast hΔ ha = (t.cast hΓ ha).subst A (θ.cast hΓ hΔ) := by
  cases hΓ
  cases hΔ
  cases ha
  rfl

/-- Each constructor's lifted substitution commutes with its parameter translation. -/
@[expose] def Hom.PreservesSubstitution (h : Hom σ τ M f)
    (A : σ.ReindexAction) (B : τ.ReindexAction) : Prop :=
  ∀ {w z : W} (μ : M w z) {Γ Δ : List (S w)} (θ : σ.Substitution Γ Δ)
    {a : S w} (op : σ.Op w a) (p : τ.Arg (h.op μ op)),
    Substitution.cast (h.context μ op p) (h.context μ op p)
      (Substitution.map h (h.next μ op p) (Substitution.liftMany
        (θ.reindex A op (h.arg μ op p)) (σ.binders op (h.arg μ op p)))) =
      Substitution.liftMany
        (Substitution.reindex B (θ.map h μ) (h.op μ op) p) (τ.binders (h.op μ op) p)

/-- A translation commutes with the parameter action at each selected child. -/
@[expose] def Hom.PreservesReindex (h : Hom σ τ M f)
    (A : σ.ReindexAction) (B : τ.ReindexAction) : Prop :=
  ∀ {w z : W} (μ : M w z) {a : S w} (op : σ.Op w a) (p : τ.Arg (h.op μ op))
    {Γ : List (S w)} {b : S w} (t : σ.Term w Γ b),
    HEq ((A op (h.arg μ op p) t).map h (h.next μ op p))
      (B (h.op μ op) p (t.map h μ))

/-- Constructor-local parameter naturality supplies compatibility with all value images. -/
theorem Hom.PreservesReindex.preservesSubstitution (h : Hom σ τ M f)
    (A : σ.ReindexAction) (B : τ.ReindexAction) (compatible : h.PreservesReindex A B) :
    h.PreservesSubstitution A B := by
  intro w z μ Γ Δ θ a op p
  have hs := h.reindex μ op p
  have hm : HEq
      (Substitution.map h (h.next μ op p) (θ.reindex A op (h.arg μ op p)))
      (Substitution.reindex B (θ.map h μ) (h.op μ op) p) := by
    apply ScopedSignature.Env.heq_of_pointwise (Ambient.map_context _ _ hs Γ)
      (funext fun b => congrArg (fun Δ => τ.Term (τ.world (h.op μ op) p) Δ b)
        (Ambient.map_context _ _ hs Δ))
    intro b c x y hxy
    induction x using ScopedVar.map_inductionOn (f (h.next μ op p)) with
    | h b x =>
      induction x using Ambient.var_inductionOn (σ.ambient op (h.arg μ op p)) with
      | h b x =>
        induction y using Ambient.var_inductionOn (τ.ambient (h.op μ op) p) with
        | h c y =>
          induction y using ScopedVar.map_inductionOn (f μ) with
          | h c y =>
            simp only [ScopedVar.index_map, Ambient.index_var] at hxy
            cases ScopedVar.sigma_eq_of_index_eq x y hxy
            rw [Substitution.map_apply, Substitution.reindex_var, Substitution.reindex_var,
              Substitution.map_apply]
            exact compatible μ op p (θ _ x)
  apply eq_of_heq
  apply (Substitution.cast_heq _ _ _).trans
  apply (Substitution.cast_heq List.map_append List.map_append _).symm.trans
  apply (heq_of_eq (Substitution.map_liftMany _ _ _ _)).trans
  exact Substitution.liftMany_heq (Ambient.map_context _ _ hs Γ)
    (Ambient.map_context _ _ hs Δ) hm (h.binders μ op p)

/-- A constructor-compatible parameter translation commutes with value substitution. -/
theorem Term.map_subst (h : Hom σ τ M f) (A : σ.ReindexAction) (B : τ.ReindexAction)
    (compatible : h.PreservesSubstitution A B) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} {a : S w} (θ : σ.Substitution Γ Δ) (t : σ.Term w Γ a) :
    (t.subst A θ).map h μ = (t.map h μ).subst B (θ.map h μ) := by
  induction t using Term.inductionOn generalizing z with
  | hvar => simp only [subst_var, map_var, Substitution.map_apply]
  | hnode w Γ a op args ih =>
      simp only [subst_node, map_node]
      congr 1
      funext p
      rw [ih (h.arg μ op p), Term.cast_subst B (h.context μ op p), compatible μ θ op p]

end IPFunctor.ScopedFamily
