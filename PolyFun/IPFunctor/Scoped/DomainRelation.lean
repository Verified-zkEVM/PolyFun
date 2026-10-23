/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Domain

/-!
# Positional correspondence of semantic environments

The relation compares the values at equal de Bruijn positions, independently of
the syntax of their sorts. It is preserved by domain transport and binding, and
by a whole-group least fixed point when its unfolding preserves the relation.
-/

public section

open OmegaCompletePartialOrder

universe u v

namespace IPFunctor
namespace ScopedDomain.Env

variable {S : Type u} {T : Type v} {D : S → PointedDomain} {E : T → PointedDomain}
  {Γ : List S} {Δ : List T}

/-- Environments agree at every shared binding position, across different sorts and domains. -/
@[expose] def Pointwise (η : Env D Γ) (ζ : Env E Δ) : Prop :=
  ∀ {a b} (x : ScopedVar Γ a) (y : ScopedVar Δ b), x.index = y.index → HEq (η a x) (ζ b y)

/-- An environment agrees with itself at every binding position. -/
theorem pointwise_refl (η : Env D Γ) : Pointwise η η := by
  intro a b x y h
  have he := ScopedVar.sigma_eq_of_index_eq x y h
  cases he
  rfl

/-- Positional correspondence is symmetric. -/
theorem Pointwise.symm {η : Env D Γ} {ζ : Env E Δ} (h : Pointwise η ζ) :
    Pointwise ζ η := fun _ _ e => (h _ _ e.symm).symm

/-- Corresponding fresh bindings extend corresponding environments. -/
theorem Pointwise.cons {η : Env D Γ} {ζ : Env E Δ} (h : Pointwise η ζ)
    {a : S} {b : T} {x : D a} {y : E b} (hxy : HEq x y) :
    Pointwise (cons D x η) (cons E y ζ) := by
  intro c d v w he
  cases v <;> cases w
  · exact hxy
  · simp only [ScopedVar.index] at he; omega
  · simp only [ScopedVar.index] at he; omega
  · exact h _ _ (Nat.add_right_cancel he)

/-- Domain transport preserves the values at their binding positions. -/
theorem Pointwise.reindex_right {U : Type*} {F : U → PointedDomain}
    {η : Env D Γ} {ζ : Env E Δ} (h : Pointwise η ζ)
    (f : T → U) (hf : ∀ a, F (f a) = E a) :
    Pointwise η (reindex E F f hf ζ) := by
  intro a b x y he
  induction y using ScopedVar.map_inductionOn f with
  | h b y =>
    rw [reindex_map]
    exact (h x y (by simpa only [ScopedVar.index_map] using he)).trans
      (PointedDomain.cast_heq _ _).symm

/-- Domain transport of the source preserves positional correspondence. -/
theorem Pointwise.reindex_left {U : Type*} {F : U → PointedDomain}
    {η : Env D Γ} {ζ : Env E Δ} (h : Pointwise η ζ)
    (f : S → U) (hf : ∀ a, F (f a) = D a) :
    Pointwise (reindex D F f hf η) ζ :=
  Pointwise.symm (Pointwise.reindex_right (Pointwise.symm h) f hf)

/-- Transporting a context retains positional correspondence on the source side. -/
theorem Pointwise.cast_left {Γ' : List S} (hc : Γ = Γ')
    {η : Env D Γ} {ζ : Env E Δ} (h : Pointwise η ζ) : Pointwise (hc ▸ η) ζ := by
  cases hc
  exact h

/-- Transporting a context retains positional correspondence on the target side. -/
theorem Pointwise.cast_right {Δ' : List T} (hc : Δ = Δ')
    {η : Env D Γ} {ζ : Env E Δ} (h : Pointwise η ζ) : Pointwise η (hc ▸ ζ) := by
  cases hc
  exact h

/-- Positional correspondence in one typed context implies equality. -/
theorem pointwise_eq {η ζ : Env D Γ} (h : Pointwise η ζ) : η = ζ := by
  funext a x
  exact eq_of_heq (h x x rfl)

/-- Domain transport is the unique target environment with the corresponding values. -/
theorem pointwise_reindex_eq {f : S → T} (hf : ∀ a, E (f a) = D a)
    {η : Env D Γ} {ζ : Env E (Γ.map f)} (h : Pointwise η ζ) :
    reindex D E f hf η = ζ := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x =>
    rw [reindex_map, PointedDomain.cast_eq_iff]
    exact h x (x.map f) (ScopedVar.index_map f x).symm

/-- Appending corresponding blocks of equal length preserves positions. -/
theorem Pointwise.append {Ξ : List S} {Ψ : List T} (hl : Ξ.length = Ψ.length)
    {ξ : Env D Ξ} {ψ : Env E Ψ} {η : Env D Γ} {ζ : Env E Δ}
    (hx : Pointwise ξ ψ) (he : Pointwise η ζ) :
    Pointwise (append D ξ η) (append E ψ ζ) := by
  induction Ξ generalizing Ψ with
  | nil =>
    cases Ψ with
    | nil => exact he
    | cons => simp only [List.length_cons, List.length_nil] at hl; omega
  | cons a Ξ ih =>
    cases Ψ with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons b Ψ =>
      apply Pointwise.cons
      · apply ih (Nat.add_right_cancel hl)
        intro s t x y hi
        exact hx (.succ x) (.succ y) (congrArg (· + 1) hi)
      · exact hx .zero .zero rfl

/-- Finite environment assembly separates the nearest position from the remaining positions. -/
theorem ofFin_cons {a : S} (xs : (i : Fin (a :: Γ).length) → D (a :: Γ)[i]) :
    ofFin D xs = cons D (xs 0) (ofFin D (fun i => xs i.succ)) := by
  funext b x
  cases x <;> rfl

/-- Corresponding finite components assemble into corresponding environments. -/
theorem pointwise_ofFin {Ξ : List S} {Ψ : List T} (hl : Ξ.length = Ψ.length)
    (xs : (i : Fin Ξ.length) → D Ξ[i]) (ys : (j : Fin Ψ.length) → E Ψ[j])
    (h : ∀ i j, i.val = j.val → HEq (xs i) (ys j)) :
    Pointwise (ofFin D xs) (ofFin E ys) := by
  induction Ξ generalizing Ψ with
  | nil => intro a b x; exact nomatch x
  | cons a Ξ ih =>
    cases Ψ with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons b Ψ =>
      rw [ofFin_cons, ofFin_cons]
      apply Pointwise.cons
      · exact ih (Nat.add_right_cancel hl) _ _
          (fun i j he => h i.succ j.succ (congrArg (· + 1) he))
      · exact h 0 0 rfl

/-- A whole-group unfolding that preserves correspondence preserves its least fixed point. -/
theorem fixGroup_pointwise (f : S → T) (hf : ∀ a, E (f a) = D a)
    {Ξ : List S} (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (j : Fin (Ξ.map f).length) → Env E (Ξ.map f ++ Δ) →𝒄 E (Ξ.map f)[j])
    (η : Env D Γ) (ζ : Env E Δ)
    (h : ∀ (ξ : Env D Ξ) (ψ : Env E (Ξ.map f)), Pointwise ξ ψ →
      ∀ i j, i.val = j.val → HEq (rhs i (append D ξ η)) (rhs' j (append E ψ ζ))) :
    Pointwise (fixGroup D rhs η) (fixGroup E rhs' ζ) := by
  have hfix := fixGroup_fusion D E rhs rhs' η ζ (reindex D E f hf)
    (reindex_bot D E f hf) (fun ξ => pointwise_reindex_eq hf
      (pointwise_ofFin (List.length_map f).symm _ _
        (h ξ _ (Pointwise.reindex_right (pointwise_refl ξ) f hf))))
  rw [← hfix]
  exact fun {_ _} x y he => Pointwise.reindex_right
    (pointwise_refl (fixGroup D rhs η)) f hf x y he

end ScopedDomain.Env
end IPFunctor
