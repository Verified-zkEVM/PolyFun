/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Bisim.Bind

/-!
# Lawful iteration for interaction trees

This file packages the iteration theory of `ITree` over weak bisimulation.
The central congruence theorem is relational: loop states and final results
may have different types and universes on the two sides.
-/

@[expose] public section

universe uFA uFB uα uβ uγ uδ

namespace ITree

/-- Close one coinductive step for two binds over the same source tree when
each pure leaf produces either matching result leaves or matching guarded
recursive calls. -/
private theorem bindGuarded_closure {F : PFunctor.{uFA, uFB}}
    {α : Type uα} {β : Type uβ}
    (R : ITree F α → ITree F α → Prop) (k l : β → ITree F α)
    (hbind : ∀ u, R (bind u k) (bind u l))
    (hleaf : ∀ b,
      (∃ x y, k b = step x ∧ l b = step y ∧ R x y) ∨
      (∃ r, k b = pure r ∧ l b = pure r))
    (u : ITree F β) : WeakBisimF R (bind u k) (bind u l) := by
  rcases hu : PFunctor.M.dest u with ⟨sh, c⟩
  cases sh with
  | pure b =>
      have hu_eq : u = pure b := by
        apply PFunctor.M.eq_of_dest_eq
        rw [hu]
        change (⟨.pure b, c⟩ : (Poly F β).Obj _) = ⟨.pure b, PEmpty.elim⟩
        congr 1
        funext z
        exact z.elim
      subst hu_eq
      rw [bind_pure_left, bind_pure_left]
      rcases hleaf b with ⟨x, y, hk, hl, hxy⟩ | ⟨r, hk, hl⟩
      · rw [hk, hl]
        exact ⟨step x, step y, .refl _, .refl _,
          Match.tau _ _ (shape'_step _) (shape'_step _) hxy⟩
      · rw [hk, hl]
        exact ⟨pure r, pure r, .refl _, .refl _,
          Match.pure r (shape'_pure r) (shape'_pure r)⟩
  | step =>
      exact ⟨bind u k, bind u l, .refl _, .refl _,
        Match.tau _ _ (dest_bind_step k u c hu) (dest_bind_step l u c hu)
          (hbind (c PUnit.unit))⟩
  | query a =>
      refine ⟨bind u k, bind u l, .refl _, .refl _,
        Match.query a _ _ (dest_bind_query k u a c hu)
          (dest_bind_query l u a c hu) ?_⟩
      intro b
      exact hbind (c b)

private theorem bindIterRel_closure {F : PFunctor.{uFA, uFB}}
    {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    {RI : β → δ → Prop} {RR : α → γ → Prop}
    (body₁ : β → ITree F (β ⊕ α)) (body₂ : δ → ITree F (δ ⊕ γ))
    (R : ITree F α → ITree F γ → Prop)
    (hiter : ∀ i j, RI i j → R (iter body₁ i) (iter body₂ j))
    (hbind : ∀ u v, WeakBisimRel (Sum.LiftRel RI RR) u v →
      R
        (bind u (fun | .inl i => step (iter body₁ i) | .inr r => pure r))
        (bind v (fun | .inl j => step (iter body₂ j) | .inr s => pure s)))
    {u : ITree F (β ⊕ α)} {v : ITree F (δ ⊕ γ)}
    (huv : WeakBisimRel (Sum.LiftRel RI RR) u v) :
    WeakBisimRelF RR R
      (bind u (fun | .inl i => step (iter body₁ i) | .inr r => pure r))
      (bind v (fun | .inl j => step (iter body₂ j) | .inr s => pure s)) := by
  obtain ⟨u', v', hu, hv, M⟩ := huv.dest
  cases M with
  | pure x y hxy hu' hv' =>
      cases hxy with
      | @inl i j hij =>
          have hu_eq : u' = pure (Sum.inl i) := by
            apply PFunctor.M.eq_of_dest_eq
            change shape' u' = shape' (pure (Sum.inl i))
            exact hu'.trans (shape'_pure (Sum.inl i)).symm
          have hv_eq : v' = pure (Sum.inl j) := by
            apply PFunctor.M.eq_of_dest_eq
            change shape' v' = shape' (pure (Sum.inl j))
            exact hv'.trans (shape'_pure (Sum.inl j)).symm
          subst hu_eq
          subst hv_eq
          refine ⟨step (iter body₁ i), step (iter body₂ j), ?_, ?_, ?_⟩
          · simpa only [bind_pure_left] using hu.bind
              (fun | .inl i => step (iter body₁ i) | .inr r => pure r)
          · simpa only [bind_pure_left] using hv.bind
              (fun | .inl j => step (iter body₂ j) | .inr s => pure s)
          · exact MatchRel.tau _ _ (shape'_step _) (shape'_step _)
              (hiter i j hij)
      | @inr r s hrs =>
          have hu_eq : u' = pure (Sum.inr r) := by
            apply PFunctor.M.eq_of_dest_eq
            change shape' u' = shape' (pure (Sum.inr r))
            exact hu'.trans (shape'_pure (Sum.inr r)).symm
          have hv_eq : v' = pure (Sum.inr s) := by
            apply PFunctor.M.eq_of_dest_eq
            change shape' v' = shape' (pure (Sum.inr s))
            exact hv'.trans (shape'_pure (Sum.inr s)).symm
          subst hu_eq
          subst hv_eq
          refine ⟨pure r, pure s, ?_, ?_,
            MatchRel.pure r s hrs (shape'_pure r) (shape'_pure s)⟩
          · simpa only [bind_pure_left] using hu.bind
              (fun | .inl i => step (iter body₁ i) | .inr r => pure r)
          · simpa only [bind_pure_left] using hv.bind
              (fun | .inl j => step (iter body₂ j) | .inr s => pure s)
  | query a c c' hu' hv' hcc =>
      refine ⟨bind u' (fun | .inl i => step (iter body₁ i) | .inr r => pure r),
        bind v' (fun | .inl j => step (iter body₂ j) | .inr s => pure s),
        hu.bind _, hv.bind _, ?_⟩
      refine MatchRel.query a _ _
        (dest_bind_query _ u' a c hu') (dest_bind_query _ v' a c' hv') ?_
      intro b
      exact hbind (c b) (c' b) (hcc b)
  | tau cu cv hu' hv' hcc =>
      refine ⟨bind u' (fun | .inl i => step (iter body₁ i) | .inr r => pure r),
        bind v' (fun | .inl j => step (iter body₂ j) | .inr s => pure s),
        hu.bind _, hv.bind _, ?_⟩
      exact MatchRel.tau _ _
        (dest_bind_step _ u' cu hu') (dest_bind_step _ v' cv hv')
        (hbind (cu PUnit.unit) (cv PUnit.unit) hcc)

/-- Relational congruence of iteration. Loop states and returned values may
have different types and universes; the body relation is lifted through the
continue/result sum. -/
theorem iter_weakBisimRel {F : PFunctor.{uFA, uFB}}
    {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    {RI : β → δ → Prop} {RR : α → γ → Prop}
    {body₁ : β → ITree F (β ⊕ α)} {body₂ : δ → ITree F (δ ⊕ γ)}
    (hbody : ∀ i j, RI i j →
      WeakBisimRel (Sum.LiftRel RI RR) (body₁ i) (body₂ j))
    {init₁ : β} {init₂ : δ} (hinit : RI init₁ init₂) :
    WeakBisimRel RR (iter body₁ init₁) (iter body₂ init₂) := by
  let K₁ : β ⊕ α → ITree F α := fun
    | .inl i => step (iter body₁ i)
    | .inr r => pure r
  let K₂ : δ ⊕ γ → ITree F γ := fun
    | .inl j => step (iter body₂ j)
    | .inr s => pure s
  let R : ITree F α → ITree F γ → Prop := fun x y =>
    (∃ i j, RI i j ∧ x = iter body₁ i ∧ y = iter body₂ j) ∨
    (∃ u v, WeakBisimRel (Sum.LiftRel RI RR) u v ∧
      x = bind u K₁ ∧ y = bind v K₂)
  have hiter : ∀ i j, RI i j → R (iter body₁ i) (iter body₂ j) :=
    fun i j hij => Or.inl ⟨i, j, hij, rfl, rfl⟩
  have hbind : ∀ u v, WeakBisimRel (Sum.LiftRel RI RR) u v →
      R (bind u K₁) (bind v K₂) :=
    fun u v huv => Or.inr ⟨u, v, huv, rfl, rfl⟩
  refine WeakBisimRel.coinduct RR R ?_ (hiter init₁ init₂ hinit)
  rintro x y (⟨i, j, hij, rfl, rfl⟩ | ⟨u, v, huv, rfl, rfl⟩)
  · rw [iter_unfold, iter_unfold]
    exact bindIterRel_closure body₁ body₂ R hiter hbind (hbody i j hij)
  · exact bindIterRel_closure body₁ body₂ R hiter hbind huv

/-- Pointwise weakly bisimilar loop bodies have weakly bisimilar
iterations. -/
theorem iter_weakBisim {F : PFunctor.{uFA, uFB}} {α : Type uα}
    {β : Type uβ} {body₁ body₂ : β → ITree F (β ⊕ α)}
    (hbody : ∀ b, WeakBisim (body₁ b) (body₂ b)) (init : β) :
    WeakBisim (iter body₁ init) (iter body₂ init) :=
  iter_weakBisimRel
    (RI := Eq) (RR := Eq)
    (fun i _ h => h ▸ (hbody i).mono_result (fun x _ hx => by
      subst hx
      cases x <;> constructor <;> rfl)) rfl

/-! ## Characteristic iteration laws -/

/-- Fixed-point unfolding with the productivity guard hidden by weak
bisimulation. -/
theorem iter_unfold_weak {F : PFunctor.{uFA, uFB}} {α : Type uα}
    {β : Type uβ} (body : β → ITree F (β ⊕ α)) (init : β) :
    WeakBisim (iter body init)
      (bind (body init) (fun
        | .inl next => iter body next
        | .inr result => pure result)) := by
  rw [iter_unfold]
  apply bind_weakBisim_cont
  intro value
  cases value with
  | inl next => exact step_weakBisim _
  | inr result => exact WeakBisim.refl (pure result)

/-- Naturality in the output / parameter identity. This law is an exact
M-type equality for `ITree`; it is exposed at the lawful interface's weak
equivalence as well. -/
theorem iter_natural_weak {F : PFunctor.{uFA, uFB}} {α : Type uα}
    {β : Type uβ} {γ : Type uγ} (body : β → ITree F (β ⊕ α))
    (k : α → ITree F γ) (init : β) :
    WeakBisim (bind (iter body init) k)
      (iter (fun b => bind (body b) (fun
        | .inl next => pure (.inl next)
        | .inr result => bind (k result) (fun value => pure (.inr value)))) init) := by
  rw [iter_bind]
  exact WeakBisim.refl _

/-- Dinaturality in the loop state / composition identity. -/
theorem iter_dinatural_weak {F : PFunctor.{uFA, uFB}}
    {α : Type uα} {β : Type uβ} {γ : Type uγ}
    (f : α → ITree F (β ⊕ γ)) (g : β → ITree F (α ⊕ γ)) (init : α) :
    WeakBisim
      (iter (fun a => bind (f a) (fun
        | .inl b => g b
        | .inr result => pure (.inr result))) init)
      (bind (f init) (fun
        | .inl b => iter (fun b => bind (g b) (fun
            | .inl a => f a
            | .inr result => pure (.inr result))) b
        | .inr result => pure result)) := by
  let H₀ : α → ITree F (α ⊕ γ) := fun a => bind (f a) (fun
    | .inl b => g b
    | .inr result => pure (.inr result))
  let K₀ : β → ITree F (β ⊕ γ) := fun b => bind (g b) (fun
    | .inl a => f a
    | .inr result => pure (.inr result))
  let H : α → ITree F (α ⊕ γ) := fun a => bind (f a) (fun
    | .inl b => step (g b)
    | .inr result => pure (.inr result))
  let K : β → ITree F (β ⊕ γ) := fun b => bind (g b) (fun
    | .inl a => step (f a)
    | .inr result => pure (.inr result))
  let L : α ⊕ γ → ITree F γ := fun
    | .inl a => step (iter H a)
    | .inr result => pure result
  let RF : β ⊕ γ → ITree F γ := fun
    | .inl b => step (iter K b)
    | .inr result => pure result
  let CF : β ⊕ γ → ITree F γ := fun
    | .inl b => step (bind (g b) L)
    | .inr result => pure result
  let RD : α ⊕ γ → ITree F γ := fun
    | .inl a => step (bind (f a) RF)
    | .inr result => pure result
  let R : ITree F γ → ITree F γ → Prop := fun x y =>
    (∃ a, x = iter H a ∧ y = bind (f a) RF) ∨
    (∃ b, x = bind (g b) L ∧ y = iter K b) ∨
    (∃ u : ITree F (β ⊕ γ), x = bind u CF ∧ y = bind u RF) ∨
    (∃ u : ITree F (α ⊕ γ), x = bind u L ∧ y = bind u RD)
  have hA : ∀ a, R (iter H a) (bind (f a) RF) :=
    fun a => Or.inl ⟨a, rfl, rfl⟩
  have hB : ∀ b, R (bind (g b) L) (iter K b) :=
    fun b => Or.inr (Or.inl ⟨b, rfl, rfl⟩)
  have hC : ∀ u, R (bind u CF) (bind u RF) :=
    fun u => Or.inr (Or.inr (Or.inl ⟨u, rfl, rfl⟩))
  have hD : ∀ u, R (bind u L) (bind u RD) :=
    fun u => Or.inr (Or.inr (Or.inr ⟨u, rfl, rfl⟩))
  have hcore : WeakBisim (iter H init) (bind (f init) RF) := by
    refine WeakBisim.coinduct R ?_ (hA init)
    rintro x y (⟨a, rfl, rfl⟩ | ⟨b, rfl, rfl⟩ |
      ⟨u, rfl, rfl⟩ | ⟨u, rfl, rfl⟩)
    · rw [iter_unfold, bind_assoc]
      convert (bindGuarded_closure R CF RF hC (fun value => by
          cases value with
          | inl b => exact Or.inl ⟨bind (g b) L, iter K b, rfl, rfl, hB b⟩
          | inr result => exact Or.inr ⟨result, rfl, rfl⟩) (f a)) using 1
      apply congrArg (bind (f a))
      funext value
      cases value with
      | inl b =>
          rw [bind_step]
          apply congrArg step
          apply congrArg (bind (g b))
          funext loopValue
          cases loopValue <;> rfl
      | inr result => simp only [CF, bind_pure_left, L]
    · rw [iter_unfold, bind_assoc]
      convert (bindGuarded_closure R L RD hD (fun value => by
          cases value with
          | inl a => exact Or.inl ⟨iter H a, bind (f a) RF, rfl, rfl, hA a⟩
          | inr result => exact Or.inr ⟨result, rfl, rfl⟩) (g b)) using 1
      apply congrArg (bind (g b))
      funext value
      cases value with
      | inl a =>
          rw [bind_step]
          apply congrArg step
          apply congrArg (bind (f a))
          funext loopValue
          cases loopValue <;> rfl
      | inr result => simp only [RD, bind_pure_left, RF]
    · exact bindGuarded_closure R CF RF hC (fun value => by
        cases value with
        | inl b => exact Or.inl ⟨bind (g b) L, iter K b, rfl, rfl, hB b⟩
        | inr result => exact Or.inr ⟨result, rfl, rfl⟩) u
    · exact bindGuarded_closure R L RD hD (fun value => by
        cases value with
        | inl a => exact Or.inl ⟨iter H a, bind (f a) RF, rfl, rfl, hA a⟩
        | inr result => exact Or.inr ⟨result, rfl, rfl⟩) u
  have hH : ∀ a, WeakBisim (H₀ a) (H a) := by
    intro a
    apply bind_weakBisim_cont
    intro value
    cases value with
    | inl b => exact (step_weakBisim (g b)).symm
    | inr result => exact WeakBisim.refl _
  have hK : ∀ b, WeakBisim (K₀ b) (K b) := by
    intro b
    apply bind_weakBisim_cont
    intro value
    cases value with
    | inl a => exact (step_weakBisim (f a)).symm
    | inr result => exact WeakBisim.refl _
  have hleft : WeakBisim (iter H₀ init) (iter H init) :=
    iter_weakBisim hH init
  have hright : WeakBisim (bind (f init) RF)
      (bind (f init) (fun
        | .inl b => iter K₀ b
        | .inr result => pure result)) := by
    apply bind_weakBisim_cont
    intro value
    cases value with
    | inl b =>
        exact (step_weakBisim (iter K b)).trans (iter_weakBisim hK b).symm
    | inr result => exact WeakBisim.refl _
  exact hleft.trans (hcore.trans hright)

/-- Codiagonal / double-dagger law: nested iteration flattens to one loop. -/
theorem iter_codiagonal_weak {F : PFunctor.{uFA, uFB}}
    {α : Type uα} {β : Type uβ}
    (body : α → ITree F (α ⊕ (α ⊕ β))) (init : α) :
    WeakBisim (iter (iter body) init)
      (iter (fun a => bind (body a) (fun
        | .inl next => pure (.inl next)
        | .inr (.inl next) => pure (.inl next)
        | .inr (.inr result) => pure (.inr result))) init) := by
  let Nested : α → ITree F β := fun a => iter (iter body) a
  let FlatBody : α → ITree F (α ⊕ β) := fun a => bind (body a) (fun
    | .inl next => pure (.inl next)
    | .inr (.inl next) => pure (.inl next)
    | .inr (.inr result) => pure (.inr result))
  let Flat : α → ITree F β := fun a => iter FlatBody a
  let KN : α ⊕ (α ⊕ β) → ITree F β := fun
    | .inl next => step (Nested next)
    | .inr (.inl next) => step (Nested next)
    | .inr (.inr result) => pure result
  let KF : α ⊕ (α ⊕ β) → ITree F β := fun
    | .inl next => step (Flat next)
    | .inr (.inl next) => step (Flat next)
    | .inr (.inr result) => pure result
  have hnested_unfold (a : α) : Nested a = bind (body a) KN := by
    dsimp only [Nested]
    rw [iter_unfold, iter_unfold, bind_assoc]
    apply congrArg (bind (body a))
    funext value
    cases value with
    | inl next =>
        rw [bind_step]
        apply congrArg step
        exact (iter_unfold (iter body) next).symm
    | inr result =>
        cases result with
        | inl next =>
            simp only [bind_pure_left, KN]
            dsimp only [Nested]
        | inr result => simp only [bind_pure_left, KN]
  have hflat_unfold (a : α) : Flat a = bind (body a) KF := by
    dsimp only [Flat]
    rw [iter_unfold]
    dsimp only [FlatBody]
    rw [bind_assoc]
    apply congrArg (bind (body a))
    funext value
    cases value with
    | inl next =>
        simp only [bind_pure_left, KF]
        dsimp only [Flat, FlatBody]
    | inr result =>
        cases result with
        | inl next =>
            simp only [bind_pure_left, KF]
            dsimp only [Flat, FlatBody]
        | inr result => simp only [bind_pure_left, KF]
  let R : ITree F β → ITree F β → Prop := fun x y =>
    (∃ a, x = Nested a ∧ y = Flat a) ∨
    (∃ u : ITree F (α ⊕ (α ⊕ β)), x = bind u KN ∧ y = bind u KF)
  have hA : ∀ a, R (Nested a) (Flat a) :=
    fun a => Or.inl ⟨a, rfl, rfl⟩
  have hC : ∀ u, R (bind u KN) (bind u KF) :=
    fun u => Or.inr ⟨u, rfl, rfl⟩
  change WeakBisim (Nested init) (Flat init)
  refine WeakBisim.coinduct R ?_ (hA init)
  rintro x y (⟨a, rfl, rfl⟩ | ⟨u, rfl, rfl⟩)
  · rw [hnested_unfold, hflat_unfold]
    exact bindGuarded_closure R KN KF hC (fun value => by
      cases value with
      | inl next =>
          exact Or.inl ⟨Nested next, Flat next, rfl, rfl, hA next⟩
      | inr result =>
          cases result with
          | inl next =>
              exact Or.inl ⟨Nested next, Flat next, rfl, rfl, hA next⟩
          | inr result => exact Or.inr ⟨result, rfl, rfl⟩) (body a)
  · exact bindGuarded_closure R KN KF hC (fun value => by
      cases value with
      | inl next =>
          exact Or.inl ⟨Nested next, Flat next, rfl, rfl, hA next⟩
      | inr result =>
          cases result with
          | inl next =>
              exact Or.inl ⟨Nested next, Flat next, rfl, rfl, hA next⟩
          | inr result => exact Or.inr ⟨result, rfl, rfl⟩) u

/-! ## Lawful iteration instance -/

/-- Interaction-tree iteration satisfies the standard lawful iteration
contract over weak bisimulation. -/
instance instLawfulMonadIter {F : PFunctor.{uFA, uFB}} :
    LawfulMonadIter (ITree F) where
  Eqv := WeakBisim
  eqv_refl := WeakBisim.refl
  eqv_symm := WeakBisim.symm
  eqv_trans := WeakBisim.trans
  bind_eqv hxy hfg :=
    bind_weakBisimRel hxy (fun a _ ha => ha ▸ hfg a)
  iter_eqv := iter_weakBisim
  iter_unfold := iter_unfold_weak
  iter_natural := iter_natural_weak
  iter_dinatural := iter_dinatural_weak
  iter_codiagonal := iter_codiagonal_weak

end ITree
