/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Transport

/-!
# Positional relations between environments

`Forall₂ R` compares the values of two environments at equal de Bruijn positions,
independently of the syntax of their sorts, using any family of relations. Binding,
appending, positional assembly and positional reindexing preserve it, and against a
mapped context it is the relation at each mapped position. `Pointwise` is the instance
for values whose types are equal only propositionally. Nothing here assumes an order on
the values; the continuous facts are in `PolyFun.IPFunctor.Scoped.DomainRelation`.
-/

public section

universe u v w z z' z''

namespace IPFunctor.ScopedSignature.Env

variable {S : Type u} {T : Type v} {V : S → Type z} {W : T → Type z'}
  {Γ : List S} {Δ : List T} {R : ∀ a b, V a → W b → Prop}

/-- Values at every shared binding position are related, across different sorts and value
families. Unlike `List.Forall₂`, this does not force equal lengths: positions past the shorter
context are unconstrained. -/
@[expose] def Forall₂ (R : ∀ a b, V a → W b → Prop) (η : Env V Γ) (ζ : Env W Δ) : Prop :=
  ∀ ⦃a b⦄ (x : ScopedVar Γ a) (y : ScopedVar Δ b), x.index = y.index → R a b (η a x) (ζ b y)

/-- A relation reflexive at each sort relates an environment to itself. -/
theorem Forall₂.refl {R : ∀ a b, V a → V b → Prop} (hR : ∀ a x, R a a x x) (η : Env V Γ) :
    Forall₂ R η η := by
  intro a b x y h
  cases ScopedVar.sigma_eq_of_index_eq x y h
  exact hR a _

/-- Swapping both environments swaps the arguments of the relation. -/
theorem Forall₂.flip {η : Env V Γ} {ζ : Env W Δ} (h : Forall₂ R η ζ) :
    Forall₂ (fun b a y x => R a b x y) ζ η := fun _ _ y x e => h x y e.symm

/-- Environment relations are monotone in the relation between values. -/
theorem Forall₂.imp {R' : ∀ a b, V a → W b → Prop} (hR : ∀ a b x y, R a b x y → R' a b x y)
    {η : Env V Γ} {ζ : Env W Δ} (h : Forall₂ R η ζ) : Forall₂ R' η ζ :=
  fun _ _ x y e => hR _ _ _ _ (h x y e)

/-- Related fresh bindings extend related environments. -/
theorem Forall₂.cons {η : Env V Γ} {ζ : Env W Δ} (h : Forall₂ R η ζ)
    {a : S} {b : T} {x : V a} {y : W b} (hxy : R a b x y) :
    Forall₂ R (cons x η) (cons y ζ) := by
  intro c d v w he
  cases v <;> cases w
  · exact hxy
  · simp only [ScopedVar.index] at he; omega
  · simp only [ScopedVar.index] at he; omega
  · exact h _ _ (Nat.add_right_cancel he)

/-- Transporting a context retains the relation on the source side. -/
theorem Forall₂.cast_left {Γ' : List S} (hc : Γ = Γ')
    {η : Env V Γ} {ζ : Env W Δ} (h : Forall₂ R η ζ) : Forall₂ R (hc ▸ η) ζ := by
  cases hc
  exact h

/-- Transporting a context retains the relation on the target side. -/
theorem Forall₂.cast_right {Δ' : List T} (hc : Δ = Δ')
    {η : Env V Γ} {ζ : Env W Δ} (h : Forall₂ R η ζ) : Forall₂ R η (hc ▸ ζ) := by
  cases hc
  exact h

/-- A relation contained in equality at each sort forces equal environments. -/
theorem Forall₂.eq {R : ∀ a b, V a → V b → Prop} (hR : ∀ a x y, R a a x y → x = y)
    {η ζ : Env V Γ} (h : Forall₂ R η ζ) : η = ζ := by
  funext a x
  exact hR _ _ _ (h x x rfl)

/-- Appending related blocks of equal length preserves positions. -/
theorem Forall₂.append {Ξ : List S} {Ψ : List T} (hl : Ξ.length = Ψ.length)
    {ξ : Env V Ξ} {ψ : Env W Ψ} {η : Env V Γ} {ζ : Env W Δ}
    (hx : Forall₂ R ξ ψ) (he : Forall₂ R η ζ) :
    Forall₂ R (append ξ η) (append ψ ζ) := by
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
theorem forall₂_iff_map {f : S → T} {η : Env V Γ} {ζ : Env W (Γ.map f)} :
    Forall₂ R η ζ ↔ ∀ a (x : ScopedVar Γ a), R a (f a) (η a x) (ζ (f a) (x.map f)) := by
  refine ⟨fun h a x => h x (x.map f) (ScopedVar.index_map f x).symm, fun h a b x y he => ?_⟩
  induction y using ScopedVar.map_inductionOn f with
  | h b y =>
    rw [ScopedVar.index_map] at he
    cases ScopedVar.sigma_eq_of_index_eq x y he
    exact h _ _

/-- Reindexing the target preserves a relation read at the mapped sorts. -/
theorem Forall₂.reindex_right {U : Type w} {X : U → Type z''} {f : T → U}
    {R' : ∀ a c, V a → X c → Prop} {η : Env V Γ} {ζ : Env (fun b => X (f b)) Δ}
    (h : Forall₂ (fun a b x y => R' a (f b) x y) η ζ) : Forall₂ R' η (reindex f ζ) := by
  intro a c x y he
  induction y using ScopedVar.map_inductionOn f with
  | h b y =>
    rw [reindex_map]
    exact h x y (by simpa only [ScopedVar.index_map] using he)

/-- Reindexing the source preserves a relation read at the mapped sorts. -/
theorem Forall₂.reindex_left {U : Type w} {X : U → Type z''} {f : S → U}
    {R' : ∀ c b, X c → W b → Prop} {η : Env (fun a => X (f a)) Γ} {ζ : Env W Δ}
    (h : Forall₂ (fun a b x y => R' (f a) b x y) η ζ) : Forall₂ R' (reindex f η) ζ :=
  (Forall₂.reindex_right (R' := fun b c y x => R' c b x y) h.flip).flip

/-- Against a positionally reindexed target, the relation is the one at each original
position. -/
theorem forall₂_reindex_right_iff {f : S → T} {η : Env V Γ} {ζ : Env (fun a => W (f a)) Γ} :
    Forall₂ R η (reindex f ζ) ↔ ∀ a (x : ScopedVar Γ a), R a (f a) (η a x) (ζ a x) := by
  rw [forall₂_iff_map]
  simp only [reindex_map]

/-- Against a positionally reindexed source, the relation is the one at each original
position. -/
theorem forall₂_reindex_left_iff {U : Type w} {X : U → Type z''} {f : S → U}
    {R' : ∀ c a, X c → V a → Prop} {η : Env (fun a => X (f a)) Γ} {ζ : Env V Γ} :
    Forall₂ R' (reindex f η) ζ ↔ ∀ a (x : ScopedVar Γ a), R' (f a) a (η a x) (ζ a x) := by
  rw [← forall₂_reindex_right_iff (R := fun b c y x => R' c b x y)]
  exact ⟨Forall₂.flip, Forall₂.flip⟩

/-- Related finite components assemble into related environments. -/
theorem forall₂_ofFin {Ξ : List S} {Ψ : List T} (hl : Ξ.length = Ψ.length)
    (xs : (i : Fin Ξ.length) → V Ξ[i]) (ys : (j : Fin Ψ.length) → W Ψ[j])
    (h : ∀ i j, i.val = j.val → R _ _ (xs i) (ys j)) :
    Forall₂ R (ofFin xs) (ofFin ys) := by
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

/-! ## Values of propositionally equal types -/

/-- Environments agree at every shared binding position, across different sorts and value
families in one universe. -/
abbrev Pointwise {W : T → Type z} (η : Env V Γ) (ζ : Env W Δ) : Prop :=
  Forall₂ (fun _ _ x y => HEq x y) η ζ

/-- An environment agrees with itself at every binding position. -/
theorem pointwise_refl (η : Env V Γ) : Pointwise η η :=
  Forall₂.refl (fun _ _ => HEq.rfl) η

/-- Positional correspondence is symmetric. -/
theorem Pointwise.symm {W : T → Type z} {η : Env V Γ} {ζ : Env W Δ} (h : Pointwise η ζ) :
    Pointwise ζ η := h.flip.imp fun _ _ _ _ e => e.symm

/-- Positional correspondence in one typed context implies equality. -/
theorem pointwise_eq {η ζ : Env V Γ} (h : Pointwise η ζ) : η = ζ :=
  Forall₂.eq (fun _ _ _ e => eq_of_heq e) h

/-- Environments of equal contexts and value families that agree at every binding position
are heterogeneously equal. -/
theorem heq_of_pointwise {V' : S → Type z} {Γ' : List S} (hΓ : Γ = Γ') (hV : V = V')
    {η : Env V Γ} {ζ : Env V' Γ'} (h : Pointwise η ζ) : HEq η ζ := by
  subst hΓ hV
  exact heq_of_eq (pointwise_eq h)

end IPFunctor.ScopedSignature.Env
