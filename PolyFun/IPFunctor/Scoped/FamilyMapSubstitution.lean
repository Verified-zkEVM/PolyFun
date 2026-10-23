/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.FamilyMap
public import PolyFun.IPFunctor.Scoped.FamilySubstitution

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
    (θ.cast hΓ hΔ : σ.Substitution Γ Δ) = @θ := rfl

@[simp] theorem cast_heq {w : W} {Γ Δ Γ' Δ' : List (S w)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (θ : σ.Substitution Γ Δ) :
    HEq (θ.cast hΓ hΔ : σ.Substitution Γ' Δ') (@θ) := by
  cases hΓ
  cases hΔ
  rfl

/-- Reading a normalized substitution only normalizes its result context. -/
theorem cast_apply {w : W} {Γ Δ Γ' Δ' : List (S w)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (θ : σ.Substitution Γ Δ)
    {a : S w} (x : ScopedVar Γ a) :
    cast hΓ hΔ θ (hΓ ▸ x) = (θ x).cast hΔ rfl := by
  cases hΓ
  cases hΔ
  rfl

/-- Translate the images of a simultaneous substitution without merging positions. -/
@[expose] def map (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} (θ : σ.Substitution Γ Δ) :
    τ.Substitution (Γ.map (f μ)) (Δ.map (f μ)) :=
  ScopedVar.mapLookup (f μ) (fun x => (θ x).map h μ)

@[simp] theorem map_apply (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} (θ : σ.Substitution Γ Δ) {a : S w} (x : ScopedVar Γ a) :
    θ.map h μ (x.map (f μ)) = (θ x).map h μ :=
  ScopedVar.mapLookup_map _ _ x

/-- Context normalization commutes with protecting one fresh value variable. -/
theorem cast_lift {w : W} {Γ Δ Γ' Δ' : List (S w)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (θ : σ.Substitution Γ Δ) (a : S w) :
    (cast (congrArg (a :: ·) hΓ) (congrArg (a :: ·) hΔ) (lift θ a) :
      σ.Substitution _ _) = fun {_} x => lift (cast hΓ hΔ θ) a x := by
  cases hΓ
  cases hΔ
  rfl

/-- Parameter translation commutes with protecting one fresh value variable. -/
theorem map_lift (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} (θ : σ.Substitution Γ Δ) (a : S w) :
    (map h μ (lift θ a) : τ.Substitution _ _) =
      fun {_} x => lift (map h μ θ) (f μ a) x := by
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
    (cast List.map_append List.map_append (map h μ (liftMany θ Ξ)) :
      τ.Substitution _ _) = fun {_} x => liftMany (map h μ θ) (Ξ.map (f μ)) x := by
  induction Ξ with
  | nil => rfl
  | cons a Ξ ih =>
      change (cast (congrArg (f μ a :: ·) List.map_append)
        (congrArg (f μ a :: ·) List.map_append) (map h μ (lift (liftMany θ Ξ) a)) :
          τ.Substitution _ _) = _
      rw [map_lift, cast_lift
        (show (Ξ ++ Γ).map (f μ) = Ξ.map (f μ) ++ Γ.map (f μ) from List.map_append)
        (show (Ξ ++ Δ).map (f μ) = Ξ.map (f μ) ++ Δ.map (f μ) from List.map_append), ih]
      rfl

/-- Lifting respects equal contexts, images and fresh binding blocks. -/
theorem liftMany_heq {w : W} {Γ Δ Γ' Δ' Ξ Ξ' : List (S w)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {θ : σ.Substitution Γ Δ} {η : σ.Substitution Γ' Δ'}
    (hθ : HEq (@θ) (@η)) (hΞ : Ξ = Ξ') :
    HEq (liftMany θ Ξ : σ.Substitution _ _) (liftMany η Ξ' : σ.Substitution _ _) := by
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
    (Substitution.cast (h.context μ op p) (h.context μ op p)
      (Substitution.map h (h.next μ op p) (Substitution.liftMany
        (θ.reindex A op (h.arg μ op p)) (σ.binders op (h.arg μ op p)))) :
          τ.Substitution _ _) =
      (fun {_} x => Substitution.liftMany
        (Substitution.reindex B (θ.map h μ) (h.op μ op) p) (τ.binders (h.op μ op) p) x)

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
  let r := σ.reindex op (h.arg μ op p)
  let g := f (h.next μ op p)
  let k := τ.reindex (h.op μ op) p
  have hs : g ∘ r = k ∘ f μ := funext (h.reindex μ op p)
  have hc (Γ : List (S w)) : (Γ.map r).map g = (Γ.map (f μ)).map k := by
    simp only [List.map_map, hs]
  have hl : (Substitution.cast List.map_map rfl
      (Substitution.map h (h.next μ op p) (θ.reindex A op (h.arg μ op p))) :
        τ.Substitution _ _) = fun {_} x => ScopedVar.mapLookup (g ∘ r)
      (fun x => (A op (h.arg μ op p) (θ x)).map h (h.next μ op p)) x := by
    funext b x
    induction x using ScopedVar.map_inductionOn (g ∘ r) with
    | h b x =>
        rw [← ScopedVar.map_map r g x, Substitution.cast_apply, Substitution.map_apply,
          Substitution.reindex_map, Term.cast_self, ScopedVar.map_map,
          ScopedVar.mapLookup_map]
  have hr : (Substitution.cast List.map_map rfl
      (Substitution.reindex B (θ.map h μ) (h.op μ op) p) : τ.Substitution _ _) =
      fun {_} x => ScopedVar.mapLookup (k ∘ f μ)
        (fun x => B (h.op μ op) p ((θ x).map h μ)) x := by
    funext b x
    induction x using ScopedVar.map_inductionOn (k ∘ f μ) with
    | h b x =>
        rw [← ScopedVar.map_map (f μ) k x, Substitution.cast_apply,
          Substitution.reindex_map, Substitution.map_apply, Term.cast_self,
          ScopedVar.map_map, ScopedVar.mapLookup_map]
  have hm : HEq
      (Substitution.map h (h.next μ op p) (θ.reindex A op (h.arg μ op p)) :
        τ.Substitution _ _)
      (Substitution.reindex B (θ.map h μ) (h.op μ op) p : τ.Substitution _ _) := by
    apply (Substitution.cast_heq List.map_map rfl _).symm.trans
    apply (heq_of_eq hl).trans
    apply (ScopedVar.mapLookup_heq hs
      (congrArg (fun Δ => fun b => τ.Term (τ.world (h.op μ op) p) Δ b) (hc Δ))
      (fun x => compatible μ op p (θ x))).trans
    exact (heq_of_eq hr).symm.trans (Substitution.cast_heq List.map_map rfl _)
  apply eq_of_heq
  apply (Substitution.cast_heq _ _ _).trans
  apply (Substitution.cast_heq List.map_append List.map_append _).symm.trans
  apply (heq_of_eq (Substitution.map_liftMany _ _ _ _)).trans
  exact Substitution.liftMany_heq (hc Γ) (hc Δ) hm (h.binders μ op p)

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
