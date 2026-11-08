/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Domain
public import PolyFun.IPFunctor.Scoped.EnvRelation
public import ToCslib.Order.Admissible

/-!
# Positional relations between continuous environments

`Env.Forall₂` is preserved by `Env.map`, and by a whole-group least fixed point when the
relation is admissible at corresponding sorts. The graph of `Env.map` is one instance.
For pointed domains, `Env.transport` along an equation of domains is the unique target
with the same values in the sense of `Env.Pointwise`.
-/

public section

open OmegaCompletePartialOrder

universe u v w z z' z''

namespace IPFunctor.ScopedSignature.Env

variable {S : Type u} {T : Type v} {V : S → Type z} {W : T → Type z'}
  {Γ : List S} {Δ : List T} {R : ∀ a b, V a → W b → Prop}

/-- Mapping the target preserves a relation that the family carries forward. -/
theorem Forall₂.map_right [∀ b, OmegaCompletePartialOrder (W b)] {U : Type w}
    {X : U → Type z''} [∀ c, OmegaCompletePartialOrder (X c)] {R' : ∀ a c, V a → X c → Prop}
    {η : Env V Γ} {ζ : Env W Δ} (h : Forall₂ R η ζ) (f : T → U) (t : ∀ b, W b →𝒄 X (f b))
    (ht : ∀ a b x y, R a b x y → R' a (f b) x (t b y)) :
    Forall₂ R' η (map f t ζ) :=
  Forall₂.reindex_right (ζ := fun b y => t b (ζ b y)) fun _ _ x y e => ht _ _ _ _ (h x y e)

/-- Mapping the source preserves a relation that the family carries forward. -/
theorem Forall₂.map_left [∀ a, OmegaCompletePartialOrder (V a)] {U : Type w}
    {X : U → Type z''} [∀ c, OmegaCompletePartialOrder (X c)] {R' : ∀ c b, X c → W b → Prop}
    {η : Env V Γ} {ζ : Env W Δ} (h : Forall₂ R η ζ) (f : S → U) (t : ∀ a, V a →𝒄 X (f a))
    (ht : ∀ a b x y, R a b x y → R' (f a) b (t a x) y) :
    Forall₂ R' (map f t η) ζ :=
  Forall₂.reindex_left (η := fun a x => t a (η a x)) fun _ _ x y e => ht _ _ _ _ (h x y e)

/-- A relation that is the graph of a family at corresponding sorts is the graph of
`Env.map`. -/
theorem forall₂_map_iff [∀ a, OmegaCompletePartialOrder (V a)]
    [∀ b, OmegaCompletePartialOrder (W b)] {f : S → T} (t : ∀ a, V a →𝒄 W (f a))
    (ht : ∀ a x y, R a (f a) x y ↔ t a x = y) {η : Env V Γ} {ζ : Env W (Γ.map f)} :
    Forall₂ R η ζ ↔ map f t η = ζ := by
  rw [forall₂_iff_map]
  constructor
  · intro h
    funext b x
    induction x using ScopedVar.map_inductionOn f with
    | h a x => rw [map_apply]; exact (ht _ _ _).mp (h a x)
  · rintro rfl a x
    rw [map_apply]
    exact (ht _ _ _).mpr rfl

/-- A relation admissible at corresponding sorts holds of two whole-group least fixed
points when it holds at bottom and whole-group unfolding preserves it. -/
theorem fixGroup_forall₂ [∀ a, OmegaCompletePartialOrder (V a)] [∀ a, OrderBot (V a)]
    [∀ b, OmegaCompletePartialOrder (W b)] [∀ b, OrderBot (W b)]
    (f : S → T) (hbot : ∀ a, R a (f a) ⊥ ⊥)
    (hsup : ∀ a, Admissible fun p : V a × W (f a) => R a (f a) p.1 p.2)
    {Ξ : List S} (rhs : (i : Fin Ξ.length) → Env V (Ξ ++ Γ) →𝒄 V Ξ[i])
    (rhs' : (j : Fin (Ξ.map f).length) → Env W (Ξ.map f ++ Δ) →𝒄 W (Ξ.map f)[j])
    (η : Env V Γ) (ζ : Env W Δ)
    (h : ∀ (ξ : Env V Ξ) (ψ : Env W (Ξ.map f)), Forall₂ R ξ ψ →
      ∀ i j, i.val = j.val → R _ _ (rhs i (append ξ η)) (rhs' j (append ψ ζ))) :
    Forall₂ R (fixGroup rhs η) (fixGroup rhs' ζ) := by
  have hadm : Admissible fun q : Env V Ξ × Env W (Ξ.map f) => Forall₂ R q.1 q.2 := by
    simp only [forall₂_iff_map]
    refine Admissible.forall fun a => Admissible.forall fun x => (hsup a).comp
      (.ofFun fun q : Env V Ξ × Env W (Ξ.map f) => (q.1 a x, q.2 (f a) (x.map f)))
  exact hadm.fix_induction₂ (p := Forall₂ R) _ _
    (forall₂_iff_map.mpr fun a _ => hbot a)
    (fun ξ ψ hr => forall₂_ofFin (List.length_map f).symm _ _ (h ξ ψ hr))

/-! ## Pointed domains related by equations -/

section Transport

variable {D : S → PointedDomain.{z}} {E : T → PointedDomain.{z}}

/-- Domain transport preserves the values at their binding positions. -/
theorem Pointwise.transport_right {U : Type w} {F : U → PointedDomain.{z}}
    {η : Env (fun a => D a) Γ} {ζ : Env (fun b => E b) Δ} (h : Pointwise η ζ)
    (f : T → U) (hf : ∀ a, F (f a) = E a) :
    Pointwise η (transport F f hf ζ) :=
  Forall₂.map_right h f _ fun _ _ _ _ e => e.trans (PointedDomain.cast_heq _ _).symm

/-- Domain transport of the source preserves positional correspondence. -/
theorem Pointwise.transport_left {U : Type w} {F : U → PointedDomain.{z}}
    {η : Env (fun a => D a) Γ} {ζ : Env (fun b => E b) Δ} (h : Pointwise η ζ)
    (f : S → U) (hf : ∀ a, F (f a) = D a) :
    Pointwise (transport F f hf η) ζ :=
  Pointwise.symm (Pointwise.transport_right (Pointwise.symm h) f hf)

/-- Domain transport is the unique target environment with the corresponding values. -/
theorem pointwise_transport_eq {f : S → T} (hf : ∀ a, E (f a) = D a)
    {η : Env (fun a => D a) Γ} {ζ : Env (fun b => E b) (Γ.map f)} (h : Pointwise η ζ) :
    transport E f hf η = ζ :=
  (forall₂_map_iff _ fun _ _ _ => (PointedDomain.cast_eq_iff _ _ _).symm).mp h

/-- A whole-group unfolding that preserves correspondence preserves its least fixed point. -/
theorem fixGroup_pointwise (f : S → T) (hf : ∀ a, E (f a) = D a)
    {Ξ : List S} (rhs : (i : Fin Ξ.length) → Env (fun a => D a) (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (j : Fin (Ξ.map f).length) → Env (fun b => E b) (Ξ.map f ++ Δ) →𝒄 E (Ξ.map f)[j])
    (η : Env (fun a => D a) Γ) (ζ : Env (fun b => E b) Δ)
    (h : ∀ (ξ : Env (fun a => D a) Ξ) (ψ : Env (fun b => E b) (Ξ.map f)), Pointwise ξ ψ →
      ∀ i j, i.val = j.val → HEq (rhs i (append ξ η)) (rhs' j (append ψ ζ))) :
    Pointwise (fixGroup rhs η) (fixGroup rhs' ζ) := by
  have hcast (a : S) (x : D a) (y : E (f a)) :
      HEq x y ↔ PointedDomain.cast (hf a).symm x = y :=
    (PointedDomain.cast_eq_iff _ _ _).symm
  exact fixGroup_forall₂ f (fun a => (hcast a _ _).mpr (PointedDomain.cast_bot _))
    (fun a c hc => (hcast a _ _).mpr
      (admissible_graph (PointedDomain.cast (hf a).symm) c fun n => (hcast a _ _).mp (hc n)))
    rhs rhs' η ζ h

end Transport

end IPFunctor.ScopedSignature.Env

/-! ## Deprecated aliases -/

namespace IPFunctor.ScopedDomain.Env

@[deprecated (since := "2026-11-07")] alias Forall₂ := ScopedSignature.Env.Forall₂
@[deprecated (since := "2026-11-07")] alias Forall₂.refl := ScopedSignature.Env.Forall₂.refl
@[deprecated (since := "2026-11-07")] alias Forall₂.flip := ScopedSignature.Env.Forall₂.flip
@[deprecated (since := "2026-11-07")] alias Forall₂.imp := ScopedSignature.Env.Forall₂.imp
@[deprecated (since := "2026-11-07")] alias Forall₂.cons := ScopedSignature.Env.Forall₂.cons
@[deprecated (since := "2026-11-07")] alias Forall₂.cast_left :=
  ScopedSignature.Env.Forall₂.cast_left
@[deprecated (since := "2026-11-07")] alias Forall₂.cast_right :=
  ScopedSignature.Env.Forall₂.cast_right
@[deprecated (since := "2026-11-07")] alias Forall₂.eq := ScopedSignature.Env.Forall₂.eq
@[deprecated (since := "2026-11-07")] alias Forall₂.append := ScopedSignature.Env.Forall₂.append
@[deprecated (since := "2026-11-07")] alias forall₂_iff_map := ScopedSignature.Env.forall₂_iff_map
@[deprecated (since := "2026-11-07")] alias Forall₂.map_right :=
  ScopedSignature.Env.Forall₂.map_right
@[deprecated (since := "2026-11-07")] alias Forall₂.map_left :=
  ScopedSignature.Env.Forall₂.map_left
@[deprecated (since := "2026-11-07")] alias forall₂_map_iff := ScopedSignature.Env.forall₂_map_iff
@[deprecated (since := "2026-11-07")] alias ofFin_cons := ScopedSignature.Env.ofFin_cons
@[deprecated (since := "2026-11-07")] alias forall₂_ofFin := ScopedSignature.Env.forall₂_ofFin
@[deprecated (since := "2026-11-07")] alias fixGroup_forall₂ :=
  ScopedSignature.Env.fixGroup_forall₂
@[deprecated (since := "2026-11-07")] alias Pointwise := ScopedSignature.Env.Pointwise
@[deprecated (since := "2026-11-07")] alias pointwise_refl := ScopedSignature.Env.pointwise_refl
@[deprecated (since := "2026-11-07")] alias Pointwise.symm := ScopedSignature.Env.Pointwise.symm
@[deprecated (since := "2026-11-07")] alias Pointwise.reindex_right :=
  ScopedSignature.Env.Pointwise.transport_right
@[deprecated (since := "2026-11-07")] alias Pointwise.reindex_left :=
  ScopedSignature.Env.Pointwise.transport_left
@[deprecated (since := "2026-11-07")] alias pointwise_eq := ScopedSignature.Env.pointwise_eq
@[deprecated (since := "2026-11-07")] alias pointwise_reindex_eq :=
  ScopedSignature.Env.pointwise_transport_eq
@[deprecated (since := "2026-11-07")] alias fixGroup_pointwise :=
  ScopedSignature.Env.fixGroup_pointwise

end IPFunctor.ScopedDomain.Env
