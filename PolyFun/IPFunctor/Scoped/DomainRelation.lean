/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Domain
public import ToCslib.Order.Admissible

/-!
# Positional relations between semantic environments

`Forall₂ R` compares the values at equal de Bruijn positions, independently of the
syntax of their sorts, using any family of relations. It is preserved by binding and
by `Env.map`, and by a whole-group least fixed point when the relation is admissible
at corresponding sorts. The graph of `Env.map` is one instance. `Pointwise` is the
instance for values at propositionally equal domains.
-/

public section

open OmegaCompletePartialOrder

universe u v

namespace IPFunctor
namespace ScopedDomain.Env

variable {S : Type u} {T : Type v} {D : S → PointedDomain} {E : T → PointedDomain}
  {Γ : List S} {Δ : List T} {R : ∀ a b, D a → E b → Prop}

/-- Values at every shared binding position are related, across different sorts and domains.
Unlike `List.Forall₂`, this does not force equal lengths: positions past the shorter context
are unconstrained. -/
@[expose] def Forall₂ (R : ∀ a b, D a → E b → Prop) (η : Env D Γ) (ζ : Env E Δ) : Prop :=
  ∀ ⦃a b⦄ (x : ScopedVar Γ a) (y : ScopedVar Δ b), x.index = y.index → R a b (η a x) (ζ b y)

/-- A relation reflexive at each sort relates an environment to itself. -/
theorem Forall₂.refl {R : ∀ a b, D a → D b → Prop} (hR : ∀ a x, R a a x x) (η : Env D Γ) :
    Forall₂ R η η := by
  intro a b x y h
  cases ScopedVar.sigma_eq_of_index_eq x y h
  exact hR a _

/-- Swapping both environments swaps the arguments of the relation. -/
theorem Forall₂.flip {η : Env D Γ} {ζ : Env E Δ} (h : Forall₂ R η ζ) :
    Forall₂ (fun b a y x => R a b x y) ζ η := fun _ _ y x e => h x y e.symm

/-- Environment relations are monotone in the relation between values. -/
theorem Forall₂.imp {R' : ∀ a b, D a → E b → Prop} (hR : ∀ a b x y, R a b x y → R' a b x y)
    {η : Env D Γ} {ζ : Env E Δ} (h : Forall₂ R η ζ) : Forall₂ R' η ζ :=
  fun _ _ x y e => hR _ _ _ _ (h x y e)

/-- Related fresh bindings extend related environments. -/
theorem Forall₂.cons {η : Env D Γ} {ζ : Env E Δ} (h : Forall₂ R η ζ)
    {a : S} {b : T} {x : D a} {y : E b} (hxy : R a b x y) :
    Forall₂ R (cons D x η) (cons E y ζ) := by
  intro c d v w he
  cases v <;> cases w
  · exact hxy
  · simp only [ScopedVar.index] at he; omega
  · simp only [ScopedVar.index] at he; omega
  · exact h _ _ (Nat.add_right_cancel he)

/-- Transporting a context retains the relation on the source side. -/
theorem Forall₂.cast_left {Γ' : List S} (hc : Γ = Γ')
    {η : Env D Γ} {ζ : Env E Δ} (h : Forall₂ R η ζ) : Forall₂ R (hc ▸ η) ζ := by
  cases hc
  exact h

/-- Transporting a context retains the relation on the target side. -/
theorem Forall₂.cast_right {Δ' : List T} (hc : Δ = Δ')
    {η : Env D Γ} {ζ : Env E Δ} (h : Forall₂ R η ζ) : Forall₂ R η (hc ▸ ζ) := by
  cases hc
  exact h

/-- A relation contained in equality at each sort forces equal environments. -/
theorem Forall₂.eq {R : ∀ a b, D a → D b → Prop} (hR : ∀ a x y, R a a x y → x = y)
    {η ζ : Env D Γ} (h : Forall₂ R η ζ) : η = ζ := by
  funext a x
  exact hR _ _ _ (h x x rfl)

/-- Appending related blocks of equal length preserves positions. -/
theorem Forall₂.append {Ξ : List S} {Ψ : List T} (hl : Ξ.length = Ψ.length)
    {ξ : Env D Ξ} {ψ : Env E Ψ} {η : Env D Γ} {ζ : Env E Δ}
    (hx : Forall₂ R ξ ψ) (he : Forall₂ R η ζ) :
    Forall₂ R (append D ξ η) (append E ψ ζ) := by
  induction Ξ generalizing Ψ with
  | nil =>
    cases Ψ with
    | nil => exact he
    | cons => simp only [List.length_cons, List.length_nil] at hl; omega
  | cons a Ξ ih =>
    cases Ψ with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons b Ψ =>
      apply Forall₂.cons
      · apply ih (Nat.add_right_cancel hl)
        intro s t x y hi
        exact hx (.succ x) (.succ y) (congrArg (· + 1) hi)
      · exact hx .zero .zero rfl

/-- Against a mapped context, the relation is the one at each mapped position. -/
theorem forall₂_iff_map {f : S → T} {η : Env D Γ} {ζ : Env E (Γ.map f)} :
    Forall₂ R η ζ ↔ ∀ a (x : ScopedVar Γ a), R a (f a) (η a x) (ζ (f a) (x.map f)) := by
  refine ⟨fun h a x => h x (x.map f) (ScopedVar.index_map f x).symm, fun h a b x y he => ?_⟩
  induction y using ScopedVar.map_inductionOn f with
  | h b y =>
    rw [ScopedVar.index_map] at he
    cases ScopedVar.sigma_eq_of_index_eq x y he
    exact h _ _

/-- Mapping the target preserves a relation that the family carries forward. -/
theorem Forall₂.map_right {U : Type*} {F : U → PointedDomain} {R' : ∀ a c, D a → F c → Prop}
    {η : Env D Γ} {ζ : Env E Δ} (h : Forall₂ R η ζ) (f : T → U) (t : ∀ b, E b →𝒄 F (f b))
    (ht : ∀ a b x y, R a b x y → R' a (f b) x (t b y)) :
    Forall₂ R' η (map E F f t ζ) := by
  intro a c x y he
  induction y using ScopedVar.map_inductionOn f with
  | h b y =>
    rw [map_apply]
    exact ht _ _ _ _ (h x y (by simpa only [ScopedVar.index_map] using he))

/-- Mapping the source preserves a relation that the family carries forward. -/
theorem Forall₂.map_left {U : Type*} {F : U → PointedDomain} {R' : ∀ c b, F c → E b → Prop}
    {η : Env D Γ} {ζ : Env E Δ} (h : Forall₂ R η ζ) (f : S → U) (t : ∀ a, D a →𝒄 F (f a))
    (ht : ∀ a b x y, R a b x y → R' (f a) b (t a x) y) :
    Forall₂ R' (map D F f t η) ζ :=
  (h.flip.map_right (R' := fun b c y z => R' c b z y) f t
    (fun _ _ _ _ hr => ht _ _ _ _ hr)).flip

/-- A relation that is the graph of a family at corresponding sorts is the graph of
`Env.map`. -/
theorem forall₂_map_iff {f : S → T} (t : ∀ a, D a →𝒄 E (f a))
    (ht : ∀ a x y, R a (f a) x y ↔ t a x = y) {η : Env D Γ} {ζ : Env E (Γ.map f)} :
    Forall₂ R η ζ ↔ map D E f t η = ζ := by
  rw [forall₂_iff_map]
  constructor
  · intro h
    funext b x
    induction x using ScopedVar.map_inductionOn f with
    | h a x => rw [map_apply]; exact (ht _ _ _).mp (h a x)
  · rintro rfl a x
    rw [map_apply]
    exact (ht _ _ _).mpr rfl

/-- Finite environment assembly separates the nearest position from the remaining positions. -/
theorem ofFin_cons {a : S} (xs : (i : Fin (a :: Γ).length) → D (a :: Γ)[i]) :
    ofFin D xs = cons D (xs 0) (ofFin D (fun i => xs i.succ)) := by
  funext b x
  cases x <;> rfl

/-- Related finite components assemble into related environments. -/
theorem forall₂_ofFin {Ξ : List S} {Ψ : List T} (hl : Ξ.length = Ψ.length)
    (xs : (i : Fin Ξ.length) → D Ξ[i]) (ys : (j : Fin Ψ.length) → E Ψ[j])
    (h : ∀ i j, i.val = j.val → R _ _ (xs i) (ys j)) :
    Forall₂ R (ofFin D xs) (ofFin E ys) := by
  induction Ξ generalizing Ψ with
  | nil => intro a b x; exact nomatch x
  | cons a Ξ ih =>
    cases Ψ with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons b Ψ =>
      rw [ofFin_cons, ofFin_cons]
      apply Forall₂.cons
      · exact ih (Nat.add_right_cancel hl) _ _
          (fun i j he => h i.succ j.succ (congrArg (· + 1) he))
      · exact h 0 0 rfl

/-- A relation admissible at corresponding sorts holds of two whole-group least fixed
points when it holds at bottom and whole-group unfolding preserves it. -/
theorem fixGroup_forall₂ (f : S → T) (hbot : ∀ a, R a (f a) ⊥ ⊥)
    (hsup : ∀ a, Admissible fun p : D a × E (f a) => R a (f a) p.1 p.2)
    {Ξ : List S} (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (j : Fin (Ξ.map f).length) → Env E (Ξ.map f ++ Δ) →𝒄 E (Ξ.map f)[j])
    (η : Env D Γ) (ζ : Env E Δ)
    (h : ∀ (ξ : Env D Ξ) (ψ : Env E (Ξ.map f)), Forall₂ R ξ ψ →
      ∀ i j, i.val = j.val → R _ _ (rhs i (append D ξ η)) (rhs' j (append E ψ ζ))) :
    Forall₂ R (fixGroup D rhs η) (fixGroup E rhs' ζ) := by
  have hadm : Admissible fun q : Env D Ξ × Env E (Ξ.map f) => Forall₂ R q.1 q.2 := by
    simp only [forall₂_iff_map]
    refine Admissible.forall fun a => Admissible.forall fun x => (hsup a).comp
      (.ofFun fun q : Env D Ξ × Env E (Ξ.map f) => (q.1 a x, q.2 (f a) (x.map f)))
  exact hadm.fix_induction₂ (p := Forall₂ R) _ _
    (forall₂_iff_map.mpr fun a _ => hbot a)
    (fun ξ ψ hr => forall₂_ofFin (List.length_map f).symm _ _ (h ξ ψ hr))

/-! ## Values at propositionally equal domains -/

/-- Environments agree at every shared binding position, across different sorts and domains. -/
abbrev Pointwise (η : Env D Γ) (ζ : Env E Δ) : Prop :=
  Forall₂ (fun _ _ x y => HEq x y) η ζ

/-- An environment agrees with itself at every binding position. -/
theorem pointwise_refl (η : Env D Γ) : Pointwise η η :=
  Forall₂.refl (fun _ _ => HEq.rfl) η

/-- Positional correspondence is symmetric. -/
theorem Pointwise.symm {η : Env D Γ} {ζ : Env E Δ} (h : Pointwise η ζ) :
    Pointwise ζ η := h.flip.imp fun _ _ _ _ e => e.symm

/-- Domain transport preserves the values at their binding positions. -/
theorem Pointwise.reindex_right {U : Type*} {F : U → PointedDomain}
    {η : Env D Γ} {ζ : Env E Δ} (h : Pointwise η ζ)
    (f : T → U) (hf : ∀ a, F (f a) = E a) :
    Pointwise η (reindex E F f hf ζ) :=
  Forall₂.map_right h f _ fun _ _ _ _ e => e.trans (PointedDomain.cast_heq _ _).symm

/-- Domain transport of the source preserves positional correspondence. -/
theorem Pointwise.reindex_left {U : Type*} {F : U → PointedDomain}
    {η : Env D Γ} {ζ : Env E Δ} (h : Pointwise η ζ)
    (f : S → U) (hf : ∀ a, F (f a) = D a) :
    Pointwise (reindex D F f hf η) ζ :=
  Pointwise.symm (Pointwise.reindex_right (Pointwise.symm h) f hf)

/-- Positional correspondence in one typed context implies equality. -/
theorem pointwise_eq {η ζ : Env D Γ} (h : Pointwise η ζ) : η = ζ :=
  Forall₂.eq (fun _ _ _ e => eq_of_heq e) h

/-- Domain transport is the unique target environment with the corresponding values. -/
theorem pointwise_reindex_eq {f : S → T} (hf : ∀ a, E (f a) = D a)
    {η : Env D Γ} {ζ : Env E (Γ.map f)} (h : Pointwise η ζ) :
    reindex D E f hf η = ζ :=
  (forall₂_map_iff _ fun _ _ _ => (PointedDomain.cast_eq_iff _ _ _).symm).mp h

/-- A whole-group unfolding that preserves correspondence preserves its least fixed point. -/
theorem fixGroup_pointwise (f : S → T) (hf : ∀ a, E (f a) = D a)
    {Ξ : List S} (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (j : Fin (Ξ.map f).length) → Env E (Ξ.map f ++ Δ) →𝒄 E (Ξ.map f)[j])
    (η : Env D Γ) (ζ : Env E Δ)
    (h : ∀ (ξ : Env D Ξ) (ψ : Env E (Ξ.map f)), Pointwise ξ ψ →
      ∀ i j, i.val = j.val → HEq (rhs i (append D ξ η)) (rhs' j (append E ψ ζ))) :
    Pointwise (fixGroup D rhs η) (fixGroup E rhs' ζ) := by
  have hcast (a : S) (x : D a) (y : E (f a)) :
      HEq x y ↔ PointedDomain.cast (hf a).symm x = y :=
    (PointedDomain.cast_eq_iff _ _ _).symm
  exact fixGroup_forall₂ f (fun a => (hcast a _ _).mpr (PointedDomain.cast_bot _))
    (fun a c hc => (hcast a _ _).mpr
      (admissible_graph (PointedDomain.cast (hf a).symm) c fun n => (hcast a _ _).mp (hc n)))
    rhs rhs' η ζ h

end ScopedDomain.Env
end IPFunctor
