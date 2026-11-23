/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Interpretation
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Fintype.Defs

/-!
# The constructors a scoped term uses

A `Head` of a binding signature is one of its operations together with the operation's result
sort. `Term.heads t` is the set of heads occurring in `t`, below any number of binders. It is
an indexed fold, like every other syntax function of the scoped layer.

`Term.denote_congr_of_agreeOn_heads` states that a term means the same under two
interpretations that agree on the heads it uses. A side condition `h ∉ t.heads` then gives
each consequence of not using `h` without an induction over `t`.

Renaming keeps the heads of a term (`heads_rename`). Substitution keeps them and adds at most
the heads of the substituted terms (`heads_subset_heads_subst`, `heads_subst_subset`). Over a
signature whose constructors have finitely many arguments, membership in `t.heads` is decidable
for decidable heads, and so is inclusion of `t.heads` in a decidable set. Both decision
procedures are Boolean folds, related to `heads` by `fold_rel`.
-/

public section

universe u v w z

namespace IPFunctor.ScopedSignature

variable {S : Type u}

/-- An operation of a binding signature together with its result sort.

`Head` is a structure, not the sigma type `(a : S) × σ.Op a`, so that instances about sets of
heads are indexed by `Head`. Through the sigma type they would be indexed by the projection
`σ.Op`, which a concrete signature unfolds to its own operation type, and instance search would
not find them. -/
structure Head (σ : ScopedSignature.{u, v, w} S) where
  /-- The sort the operation produces. -/
  sort : S
  /-- The operation. -/
  op : σ.Op sort

instance Head.instDecidableEq [DecidableEq S] (σ : ScopedSignature.{u, v, w} S)
    [∀ a, DecidableEq (σ.Op a)] : DecidableEq σ.Head := fun h h' =>
  decidable_of_iff ((⟨h.sort, h.op⟩ : (a : S) × σ.Op a) = ⟨h'.sort, h'.op⟩) <| by
    cases h; cases h'; simp

namespace Term

variable {σ : ScopedSignature.{u, v, w} S} {Γ Δ : List S} {a : S}

/-- The heads occurring in a term, below any number of binders. Variables use none. -/
@[expose] def heads (t : σ.Term Γ a) : Set σ.Head :=
  t.fold (D := fun _ => Set σ.Head) (fun _ _ => ∅)
    (fun j op next => insert (⟨j.2, op⟩ : σ.Head) (⋃ p, next p))

@[simp] theorem heads_var (x : ScopedVar Γ a) : (var (σ := σ) x).heads = ∅ := rfl

@[simp] theorem heads_node (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) :
    (node op args).heads = insert (⟨a, op⟩ : σ.Head) (⋃ p, (args p).heads) := rfl

theorem mem_heads_node (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) (h : σ.Head) :
    h ∈ (node op args).heads ↔ h = ⟨a, op⟩ ∨ ∃ p, h ∈ (args p).heads := by
  simp

/-- A constructor uses its own head. -/
theorem mem_heads_node_self (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) :
    (⟨a, op⟩ : σ.Head) ∈ (node op args).heads :=
  Set.mem_insert _ _

/-- A constructor uses the heads of each of its arguments. -/
theorem heads_subset_heads_node (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) (p : σ.Arg op) :
    (args p).heads ⊆ (node op args).heads :=
  (Set.subset_iUnion (fun p => (args p).heads) p).trans (Set.subset_insert _ _)

/-- The heads of a constructor lie in a set exactly when its own head and the heads of each of
its arguments do. -/
theorem heads_node_subset_iff (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) {H : Set σ.Head} :
    (node op args).heads ⊆ H ↔ (⟨a, op⟩ : σ.Head) ∈ H ∧ ∀ p, (args p).heads ⊆ H := by
  simp [Set.insert_subset_iff]

/-! ## Renaming and substitution -/

/-- Renaming changes only variables, so it keeps the heads of a term. -/
@[simp] theorem heads_rename (ρ : Renaming Γ Δ) (t : σ.Term Γ a) :
    (t.rename ρ).heads = t.heads := by
  refine IFreeM.fold_rel
    (fun j s (f : ∀ {Δ}, Renaming j.1 Δ → σ.Term Δ j.2) => ∀ Δ (ρ : Renaming j.1 Δ),
      (f ρ).heads = s) _ _ _ _ (fun _ _ _ _ => rfl) ?_ t Δ ρ
  intro j op s f h Δ ρ
  exact congrArg (insert _) (Set.iUnion_congr fun p => h p _ _)

@[simp] theorem heads_weaken (t : σ.Term Γ a) (b : S) : (t.weaken b).heads = t.heads :=
  heads_rename _ t

/-- A lifted substitution uses only heads of the original images: the fresh variables are
sent to variables, and the older images are weakened. -/
theorem heads_liftMany_subset (θ : σ.Substitution Γ Δ) (Ξ : List S) {b : S}
    (x : ScopedVar (Ξ ++ Γ) b) :
    (θ.liftMany Ξ b x).heads ⊆ ⋃ (c : S) (y : ScopedVar Γ c), (θ c y).heads := by
  induction Ξ generalizing b with
  | nil => exact Set.subset_iUnion₂ (s := fun c y => (θ c y).heads) b x
  | cons c Ξ ih =>
    cases x with
    | zero => exact Set.empty_subset _
    | succ x => exact (heads_weaken _ c).subset.trans (ih x)

/-- Substitution keeps every head of the term it acts on. -/
theorem heads_subset_heads_subst (θ : σ.Substitution Γ Δ) (t : σ.Term Γ a) :
    t.heads ⊆ (t.subst θ).heads := by
  refine IFreeM.fold_rel
    (fun j s (f : ∀ {Δ}, σ.Substitution j.1 Δ → σ.Term Δ j.2) =>
      ∀ Δ (θ : σ.Substitution j.1 Δ), s ⊆ (f θ).heads)
    _ _ _ _ (fun _ _ _ _ => Set.empty_subset _) ?_ t Δ θ
  intro j op s f h Δ θ
  exact Set.insert_subset_insert (Set.iUnion_mono fun p => h p _ _)

/-- A substituted term uses only its own heads and those of the substitution's images. -/
theorem heads_subst_subset (θ : σ.Substitution Γ Δ) (t : σ.Term Γ a) :
    (t.subst θ).heads ⊆ t.heads ∪ ⋃ (b : S) (x : ScopedVar Γ b), (θ b x).heads := by
  refine IFreeM.fold_rel
    (fun j s (f : ∀ {Δ}, σ.Substitution j.1 Δ → σ.Term Δ j.2) =>
      ∀ Δ (θ : σ.Substitution j.1 Δ),
        (f θ).heads ⊆ s ∪ ⋃ (b : S) (x : ScopedVar j.1 b), (θ b x).heads)
    _ _ _ _ (fun _ _ _ θ => ?_) ?_ t Δ θ
  · exact (Set.subset_iUnion₂ (s := fun c y => (θ c y).heads) _ _).trans Set.subset_union_right
  intro j op s f h Δ θ
  refine Set.insert_subset_iff.2 ⟨Or.inl (Set.mem_insert _ _), Set.iUnion_subset fun p => ?_⟩
  refine (h p _ _).trans (Set.union_subset ?_ (Set.iUnion₂_subset fun b x => ?_))
  · exact ((Set.subset_iUnion s p).trans (Set.subset_insert _ _)).trans Set.subset_union_left
  · exact (heads_liftMany_subset θ _ x).trans Set.subset_union_right

/-- Closing a body uses only the heads of the body and of the closing term. -/
theorem heads_substOne_subset {b : S} (body : σ.Term (a :: Γ) b) (value : σ.Term Γ a) :
    (body.substOne value).heads ⊆ body.heads ∪ value.heads := by
  refine (heads_subst_subset _ body).trans (Set.union_subset_union_right _ ?_)
  refine Set.iUnion₂_subset fun c x => ?_
  cases x with
  | zero => exact le_rfl
  | succ x => exact Set.empty_subset _

/-! ## Meanings depend only on the heads used -/

/-- **No telepathy.** Interpretations that agree on every head a term uses give it the same
meaning. -/
theorem denote_congr_of_agreeOn_heads {V : S → Type z} {alg₁ alg₂ : Interpretation σ V}
    (t : σ.Term Γ a) (hagree : ∀ h ∈ t.heads, alg₁ h.op = alg₂ h.op) :
    t.denote alg₁ = t.denote alg₂ := by
  induction t using Term.inductionOn with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    funext ρ
    simp only [denote_node]
    rw [hagree _ (mem_heads_node_self op args)]
    congr 1
    funext p η
    rw [ih p fun h hh => hagree h (heads_subset_heads_node op args p hh)]

/-- Interpretations that agree on a set containing every head of a term give it the same
meaning. -/
theorem denote_congr_of_heads_subset {V : S → Type z} {alg₁ alg₂ : Interpretation σ V}
    {H : Set σ.Head} (t : σ.Term Γ a) (hH : t.heads ⊆ H) (hagree : ∀ h ∈ H, alg₁ h.op = alg₂ h.op) :
    t.denote alg₁ = t.denote alg₂ :=
  denote_congr_of_agreeOn_heads t fun h hh => hagree h (hH hh)

/-! ## Decision procedures -/

section Decidable

variable [∀ {a} (op : σ.Op a), Fintype (σ.Arg op)]

/-- Whether every head of a term lies in a decidable set, as a Boolean fold. -/
@[expose] def headsSubsetB (H : Set σ.Head) [DecidablePred (· ∈ H)] (t : σ.Term Γ a) : Bool :=
  t.fold (D := fun _ => Bool) (fun _ _ => true)
    (fun j op next => decide ((⟨j.2, op⟩ : σ.Head) ∈ H) && decide (∀ p, next p = true))

theorem headsSubsetB_iff (H : Set σ.Head) [DecidablePred (· ∈ H)] (t : σ.Term Γ a) :
    t.headsSubsetB H = true ↔ t.heads ⊆ H := by
  refine (IFreeM.fold_rel (fun _ (b : Bool) (s : Set σ.Head) => b = true ↔ s ⊆ H) _ _ _ _
    (fun _ _ => iff_of_true rfl (Set.empty_subset _)) ?_ t)
  intro j op bs ss h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Set.insert_subset_iff, Set.iUnion_subset_iff,
    h]

/-- Whether a head occurs in a term, as a Boolean fold. -/
@[expose] def usesB [DecidableEq σ.Head] (t : σ.Term Γ a) (h : σ.Head) : Bool :=
  t.fold (D := fun _ => Bool) (fun _ _ => false)
    (fun j op next => decide (h = (⟨j.2, op⟩ : σ.Head)) || decide (∃ p, next p = true))

theorem usesB_iff [DecidableEq σ.Head] (t : σ.Term Γ a) (h : σ.Head) :
    t.usesB h = true ↔ h ∈ t.heads := by
  refine (IFreeM.fold_rel (fun _ (b : Bool) (s : Set σ.Head) => b = true ↔ h ∈ s) _ _ _ _
    (fun _ _ => iff_of_false Bool.false_ne_true (Set.notMem_empty h)) ?_ t)
  intro j op bs ss hs
  simp only [Bool.or_eq_true, decide_eq_true_eq, Set.mem_insert_iff, Set.mem_iUnion, hs]

instance decidableHeadsSubset (H : Set σ.Head) [DecidablePred (· ∈ H)] (t : σ.Term Γ a) :
    Decidable (t.heads ⊆ H) :=
  decidable_of_iff _ (t.headsSubsetB_iff H)

instance decidableMemHeads [DecidableEq σ.Head] (t : σ.Term Γ a) (h : σ.Head) :
    Decidable (h ∈ t.heads) :=
  decidable_of_iff _ (t.usesB_iff h)

end Decidable

end Term
end IPFunctor.ScopedSignature
