/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Order.FixedPoints
public import PolyFun.ITree.Construct
public import PolyFun.PFunctor.Free.WP

/-!
# Weakest preconditions over interaction trees

A per-operation specification `Φ : OpSpec F l` says what one call to each operation guarantees.
On a finite program, `PFunctor.FreeM.wpFold` folds it over the tree. An interaction tree may run
forever, through infinitely many silent steps or queries, so a fold needs a fixed point, and there
are two canonical ones:

* `ITree.wpTotal Φ t post`, the least fixed point, reads total correctness: every run must return,
  and divergence reads `⊥`.
* `ITree.wpPartial Φ t post`, the greatest fixed point, reads partial correctness: divergence reads
  `⊤`.

Both solve the same one-step equations (`ITree.wpStepFun`). A leaf reads the postcondition, a
silent step reads its continuation, and a query reads `Φ` applied to its continuations. Every
solution lies between the two (`ITree.wpTotal_le_le_wpPartial`). The definitions are Mathlib's
Knaster–Tarski formulas, so they need no hypothesis on `Φ`. The fixed-point equations need
`Φ.Monotone`.

## Main definitions

* `ITree.wpLayer`, `ITree.wpStepFun`: one layer of the readings, on a coalgebra layer and on a
  tree, and `ITree.wpStep` as an order homomorphism.
* `ITree.wpTotal`, `ITree.wpPartial`: the total and partial readings.

## Main results

* `ITree.wpTotal_le_of_wpStepFun_le`, `ITree.le_wpPartial_of_le_wpStepFun`: induction and
  coinduction.
* `ITree.wpTotal_pure`, `_step`, `_query`, `_lift` and their partial counterparts: the one-step
  equations.
* `ITree.wpTotal_diverge`, `ITree.wpPartial_diverge`: silent divergence reads `⊥` and `⊤`.
* `ITree.wpTotal_le_le_wpPartial`: every solution of the equations lies between the readings.
* `ITree.wpTotal_le_wpPartial`: total correctness implies partial correctness, for a monotone spec.
* `ITree.wpTotal_corec_le`, `ITree.le_wpPartial_corec`: bounds for corecursively defined trees.
-/

@[expose] public section

universe uA uB uα uS uT w

namespace ITree

open PFunctor

variable {F : PFunctor.{uA, uB}} {α : Type uα} {l : Type w}

/-! ## The one-step functional -/

/-- One layer of the readings, on a coalgebra layer whose children lie in `S` and are read by `Y`.
A leaf reads `post`, a silent step reads its continuation, and a query reads `Φ` applied to its
continuations. -/
def wpLayer (Φ : OpSpec F l) (post : α → l) {S : Type uS} (Y : S → l) :
    (ViewPoly F α).Obj S → l
  | ⟨.pure r, _⟩ => post r
  | ⟨.step, next⟩ => Y (next PUnit.unit)
  | ⟨.query a, next⟩ => Φ a fun b => Y (next b)

/-- The one-step functional on readings of trees. -/
def wpStepFun (Φ : OpSpec F l) (post : α → l) (X : ITree F α → l) (t : ITree F α) : l :=
  wpLayer Φ post X (shape' t)

section Layer

variable (Φ : OpSpec F l) (post : α → l)

@[simp] theorem wpStepFun_pure (X : ITree F α → l) (r : α) :
    wpStepFun Φ post X (pure r) = post r := by
  rw [wpStepFun, shape'_pure]
  rfl

@[simp] theorem wpStepFun_step (X : ITree F α → l) (t : ITree F α) :
    wpStepFun Φ post X (step t) = X t := by
  rw [wpStepFun, shape'_step]
  rfl

@[simp] theorem wpStepFun_query (X : ITree F α → l) (a : F.A) (k : F.B a → ITree F α) :
    wpStepFun Φ post X (query a k) = Φ a fun b => X (k b) := by
  rw [wpStepFun, shape'_query]
  rfl

theorem wpLayer_map {S : Type uS} {T : Type uT} (Y : T → l) (f : S → T)
    (x : (ViewPoly F α).Obj S) :
    wpLayer Φ post Y ((ViewPoly F α).map f x) = wpLayer Φ post (Y ∘ f) x := by
  rcases x with ⟨_ | _ | _, _⟩ <;> rfl

theorem wpStepFun_corec {S : Type uS} (next : S → (ViewPoly F α).Obj S) (X : ITree F α → l)
    (s : S) :
    wpStepFun Φ post X (corec next s) = wpLayer Φ post (X ∘ corec next) (next s) := by
  rw [wpStepFun, shape'_corec_apply]
  exact wpLayer_map Φ post X (corec next) (next s)

/-- A function solves the one-step equations as soon as it satisfies them at each kind of node. -/
theorem wpStepFun_eq_self {R : ITree F α → l} (hpure : ∀ r, R (pure r) = post r)
    (hstep : ∀ t, R (step t) = R t) (hquery : ∀ a k, R (query a k) = Φ a fun b => R (k b)) :
    wpStepFun Φ post R = R := by
  funext t
  induction t using shape_cases with
  | pure r => rw [wpStepFun_pure, hpure]
  | step _ => rw [wpStepFun_step, hstep]
  | query a k => rw [wpStepFun_query, hquery]

end Layer

section Mono

variable [Preorder l] {Φ : OpSpec F l}

theorem wpLayer_mono (hΦ : Φ.Monotone) (post : α → l) {S : Type uS} {Y Y' : S → l}
    (h : Y ≤ Y') : ∀ x, wpLayer Φ post Y x ≤ wpLayer Φ post Y' x
  | ⟨.pure _, _⟩ => le_rfl
  | ⟨.step, _⟩ => h _
  | ⟨.query a, _⟩ => hΦ a fun _ => h _

theorem wpLayer_mono_post {post post' : α → l} (h : post ≤ post') {S : Type uS} (Y : S → l) :
    ∀ x, wpLayer Φ post Y x ≤ wpLayer Φ post' Y x
  | ⟨.pure r, _⟩ => h r
  | ⟨.step, _⟩ => le_rfl
  | ⟨.query _, _⟩ => le_rfl

theorem wpLayer_mono_spec {Ψ : OpSpec F l} (h : ∀ a k, Φ a k ≤ Ψ a k) (post : α → l)
    {S : Type uS} (Y : S → l) : ∀ x, wpLayer Φ post Y x ≤ wpLayer Ψ post Y x
  | ⟨.pure _, _⟩ => le_rfl
  | ⟨.step, _⟩ => le_rfl
  | ⟨.query a, _⟩ => h a _

/-- The one-step functional of a monotone spec, as an order homomorphism. -/
def wpStep (hΦ : Φ.Monotone) (post : α → l) : (ITree F α → l) →o (ITree F α → l) where
  toFun := wpStepFun Φ post
  monotone' _ _ h _ := wpLayer_mono hΦ post h _

end Mono

/-! ## The total and partial readings -/

section Readings

variable [CompleteLattice l]

/-- Total correctness: the least solution of the one-step equations. A run must return; silent
divergence reads `⊥`. -/
def wpTotal (Φ : OpSpec F l) (t : ITree F α) (post : α → l) : l :=
  sInf {X : ITree F α → l | wpStepFun Φ post X ≤ X} t

/-- Partial correctness: the greatest solution of the one-step equations. Silent divergence
reads `⊤`. -/
def wpPartial (Φ : OpSpec F l) (t : ITree F α) (post : α → l) : l :=
  sSup {X : ITree F α → l | X ≤ wpStepFun Φ post X} t

variable {Φ : OpSpec F l} {post : α → l}

theorem wpTotal_eq_lfp (hΦ : Φ.Monotone) (t : ITree F α) :
    wpTotal Φ t post = (wpStep hΦ post).lfp t :=
  rfl

theorem wpPartial_eq_gfp (hΦ : Φ.Monotone) (t : ITree F α) :
    wpPartial Φ t post = (wpStep hΦ post).gfp t :=
  rfl

/-- The total reading is the infimum of the prefixed points at the tree. -/
theorem wpTotal_eq_iInf (t : ITree F α) :
    wpTotal Φ t post = ⨅ (X : ITree F α → l) (_ : wpStepFun Φ post X ≤ X), X t := by
  rw [wpTotal, sInf_apply, iInf_subtype']
  rfl

/-- The partial reading is the supremum of the postfixed points at the tree. -/
theorem wpPartial_eq_iSup (t : ITree F α) :
    wpPartial Φ t post = ⨆ (X : ITree F α → l) (_ : X ≤ wpStepFun Φ post X), X t := by
  rw [wpPartial, sSup_apply, iSup_subtype']
  rfl

/-- Induction for total correctness: a prefixed point bounds the total reading from above. -/
theorem wpTotal_le_of_wpStepFun_le {X : ITree F α → l} (h : wpStepFun Φ post X ≤ X)
    (t : ITree F α) : wpTotal Φ t post ≤ X t :=
  sInf_le (α := ITree F α → l) h t

/-- Coinduction for partial correctness: a postfixed point bounds the partial reading from
below. -/
theorem le_wpPartial_of_le_wpStepFun {X : ITree F α → l} (h : X ≤ wpStepFun Φ post X)
    (t : ITree F α) : X t ≤ wpPartial Φ t post :=
  le_sSup (α := ITree F α → l) h t

/-- Every solution of the one-step equations lies between the total and partial readings. -/
theorem wpTotal_le_le_wpPartial {R : ITree F α → l} (hR : wpStepFun Φ post R = R)
    (t : ITree F α) : wpTotal Φ t post ≤ R t ∧ R t ≤ wpPartial Φ t post :=
  ⟨wpTotal_le_of_wpStepFun_le hR.le t, le_wpPartial_of_le_wpStepFun hR.ge t⟩

@[simp] theorem wpTotal_diverge : wpTotal Φ (diverge : ITree F α) post = ⊥ := by
  refine le_bot_iff.mp ((wpTotal_le_of_wpStepFun_le
    (X := fun t => ⨆ _ : t ≠ diverge, (⊤ : l)) ?_ diverge).trans (by simp))
  intro t
  by_cases ht : t = diverge
  · subst ht
    rw [wpStepFun, shape'_diverge]
    exact le_rfl
  · simp [ht]

@[simp] theorem wpPartial_diverge : wpPartial Φ (diverge : ITree F α) post = ⊤ := by
  refine top_le_iff.mp ((by simp : (⊤ : l) ≤ ⨅ _ : (diverge : ITree F α) ≠ diverge, ⊥).trans
    (le_wpPartial_of_le_wpStepFun (X := fun t => ⨅ _ : t ≠ diverge, (⊥ : l)) ?_ diverge))
  intro t
  by_cases ht : t = diverge
  · subst ht
    rw [wpStepFun, shape'_diverge]
    exact le_rfl
  · simp [ht]

section Monotone

variable (hΦ : Φ.Monotone)
include hΦ

theorem wpStepFun_wpTotal : wpStepFun Φ post (wpTotal Φ · post) = (wpTotal Φ · post) :=
  (wpStep hΦ post).map_lfp

theorem wpStepFun_wpPartial : wpStepFun Φ post (wpPartial Φ · post) = (wpPartial Φ · post) :=
  (wpStep hΦ post).map_gfp

theorem wpTotal_eq_wpStepFun (t : ITree F α) :
    wpTotal Φ t post = wpStepFun Φ post (wpTotal Φ · post) t :=
  (congrFun (wpStepFun_wpTotal hΦ) t).symm

theorem wpPartial_eq_wpStepFun (t : ITree F α) :
    wpPartial Φ t post = wpStepFun Φ post (wpPartial Φ · post) t :=
  (congrFun (wpStepFun_wpPartial hΦ) t).symm

theorem wpTotal_pure (r : α) : wpTotal Φ (pure r) post = post r := by
  rw [wpTotal_eq_wpStepFun hΦ, wpStepFun_pure]

theorem wpTotal_step (t : ITree F α) : wpTotal Φ (step t) post = wpTotal Φ t post := by
  rw [wpTotal_eq_wpStepFun hΦ, wpStepFun_step]

theorem wpTotal_query (a : F.A) (k : F.B a → ITree F α) :
    wpTotal Φ (query a k) post = Φ a fun b => wpTotal Φ (k b) post := by
  rw [wpTotal_eq_wpStepFun hΦ, wpStepFun_query]

theorem wpTotal_lift (a : F.A) (post : F.B a → l) : wpTotal Φ (lift a) post = Φ a post := by
  rw [lift, wpTotal_query hΦ]
  simp only [wpTotal_pure hΦ]

theorem wpPartial_pure (r : α) : wpPartial Φ (pure r) post = post r := by
  rw [wpPartial_eq_wpStepFun hΦ, wpStepFun_pure]

theorem wpPartial_step (t : ITree F α) : wpPartial Φ (step t) post = wpPartial Φ t post := by
  rw [wpPartial_eq_wpStepFun hΦ, wpStepFun_step]

theorem wpPartial_query (a : F.A) (k : F.B a → ITree F α) :
    wpPartial Φ (query a k) post = Φ a fun b => wpPartial Φ (k b) post := by
  rw [wpPartial_eq_wpStepFun hΦ, wpStepFun_query]

theorem wpPartial_lift (a : F.A) (post : F.B a → l) : wpPartial Φ (lift a) post = Φ a post := by
  rw [lift, wpPartial_query hΦ]
  simp only [wpPartial_pure hΦ]

/-- Total correctness implies partial correctness. The hypothesis is needed: for a spec that
negates its continuation, the infinite query tree reads `True` totally and `False` partially. -/
theorem wpTotal_le_wpPartial (t : ITree F α) : wpTotal Φ t post ≤ wpPartial Φ t post :=
  OrderHom.lfp_le_gfp (wpStep hΦ post) t

theorem wpTotal_mono {post' : α → l} (h : post ≤ post') (t : ITree F α) :
    wpTotal Φ t post ≤ wpTotal Φ t post' :=
  wpTotal_le_of_wpStepFun_le (fun t => (wpLayer_mono_post h _ (shape' t)).trans
    ((wpStepFun_wpTotal (post := post') hΦ).le t)) t

theorem wpPartial_mono {post' : α → l} (h : post ≤ post') (t : ITree F α) :
    wpPartial Φ t post ≤ wpPartial Φ t post' :=
  le_wpPartial_of_le_wpStepFun (fun t => (wpStepFun_wpPartial hΦ).ge t |>.trans
    (wpLayer_mono_post h _ (shape' t))) t

/-- Partial correctness for a smaller monotone spec implies it for a larger spec. -/
theorem wpPartial_le_wpPartial_of_le {Ψ : OpSpec F l} (h : ∀ a k, Φ a k ≤ Ψ a k)
    (t : ITree F α) : wpPartial Φ t post ≤ wpPartial Ψ t post :=
  le_wpPartial_of_le_wpStepFun (fun t => (wpStepFun_wpPartial hΦ).ge t |>.trans
    (wpLayer_mono_spec h post _ (shape' t))) t

end Monotone

/-- Total correctness for a spec implies it for a larger monotone spec. -/
theorem wpTotal_le_wpTotal_of_le {Ψ : OpSpec F l} (hΨ : Ψ.Monotone) (h : ∀ a k, Φ a k ≤ Ψ a k)
    (t : ITree F α) : wpTotal Φ t post ≤ wpTotal Ψ t post :=
  wpTotal_le_of_wpStepFun_le (fun t => (wpLayer_mono_spec h post _ (shape' t)).trans
    ((wpStepFun_wpTotal (post := post) hΨ).le t)) t

/-! ### Corecursively defined trees -/

section Corec

variable {S : Type uS} (next : S → (ViewPoly F α).Obj S)

/-- A prefixed point of a coalgebra's equations bounds the total reading of the trees it
generates. -/
theorem wpTotal_corec_le (hΦ : Φ.Monotone) {Y : S → l}
    (hY : ∀ s, wpLayer Φ post Y (next s) ≤ Y s) (s : S) :
    wpTotal Φ (corec next s) post ≤ Y s := by
  refine (wpTotal_le_of_wpStepFun_le
    (X := fun u => ⨅ (s : S) (_ : corec next s = u), Y s) ?_ (corec next s)).trans ?_
  · intro u
    refine le_iInf₂ fun s hs => ?_
    subst hs
    rw [wpStepFun_corec]
    refine (wpLayer_mono hΦ post ?_ (next s)).trans (hY s)
    refine fun s' => ?_
    change (⨅ (s'' : S) (_ : corec next s'' = corec next s'), Y s'') ≤ Y s'
    exact iInf_le_of_le s' (iInf_le _ rfl)
  · change (⨅ (s' : S) (_ : corec next s' = corec next s), Y s') ≤ Y s
    exact iInf_le_of_le s (iInf_le _ rfl)

/-- A postfixed point of a coalgebra's equations bounds the partial reading of the trees it
generates. -/
theorem le_wpPartial_corec (hΦ : Φ.Monotone) {Y : S → l}
    (hY : ∀ s, Y s ≤ wpLayer Φ post Y (next s)) (s : S) :
    Y s ≤ wpPartial Φ (corec next s) post := by
  refine le_trans ?_ (le_wpPartial_of_le_wpStepFun
    (X := fun u => ⨆ (s : S) (_ : corec next s = u), Y s) ?_ (corec next s))
  · change Y s ≤ ⨆ (s' : S) (_ : corec next s' = corec next s), Y s'
    exact le_iSup_of_le s (le_iSup (fun _ : corec next s = corec next s => Y s) rfl)
  · intro u
    refine iSup₂_le fun s hs => ?_
    subst hs
    rw [wpStepFun_corec]
    refine (hY s).trans (wpLayer_mono hΦ post ?_ (next s))
    refine fun s' => ?_
    change Y s' ≤ ⨆ (s'' : S) (_ : corec next s'' = corec next s'), Y s''
    exact le_iSup_of_le s' (le_iSup (fun _ : corec next s' = corec next s' => Y s') rfl)

/-- The total reading along a coalgebra solves the coalgebra's equations. -/
theorem wpTotal_corec (hΦ : Φ.Monotone) (s : S) :
    wpTotal Φ (corec next s) post =
      wpLayer Φ post (fun s' => wpTotal Φ (corec next s') post) (next s) := by
  rw [wpTotal_eq_wpStepFun hΦ, wpStepFun_corec]
  rfl

/-- The partial reading along a coalgebra solves the coalgebra's equations. -/
theorem wpPartial_corec (hΦ : Φ.Monotone) (s : S) :
    wpPartial Φ (corec next s) post =
      wpLayer Φ post (fun s' => wpPartial Φ (corec next s') post) (next s) := by
  rw [wpPartial_eq_wpStepFun hΦ, wpStepFun_corec]
  rfl

end Corec

end Readings

end ITree
