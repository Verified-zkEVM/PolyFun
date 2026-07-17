/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Sim.Facts
public import PolyFun.PFunctor.Free.Resumption

/-!
# Resumptions as the tau-free fragment of interaction trees

Every `PFunctor.Resumption p β` embeds into `ITree p β` without inserting
silent steps. Its exact image is the greatest invariant containing only pure
and query nodes. This module gives both directions and packages the resulting
equivalence with the tau-free subtype.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uα uβ uγ uX

namespace PFunctor.Resumption

variable {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}
  {α : Type uα} {β : Type uβ} {γ : Type uγ}

/-! ## Embedding into interaction trees -/

/-- One-step ITree coalgebra corresponding to a resumption return/query view. -/
def toITreeStep (computation : Resumption p β) :
    (ITree.Poly p β).Obj (Resumption p β) :=
  match dest computation with
  | Sum.inl value => ⟨.pure value, PEmpty.elim⟩
  | Sum.inr ⟨position, next⟩ => ⟨.query position, next⟩

/-- Embed a resumption as an interaction tree without inserting tau steps. -/
def toITree (computation : Resumption p β) : ITree p β :=
  M.corec toITreeStep computation

@[simp] theorem shape'_toITree (computation : Resumption p β) :
    ITree.shape' (toITree computation) =
      match dest computation with
      | Sum.inl value => ⟨.pure value, PEmpty.elim⟩
      | Sum.inr ⟨position, next⟩ =>
          ⟨.query position, fun direction => toITree (next direction)⟩ := by
  unfold toITree ITree.shape'
  rcases h : dest computation with value | ⟨position, next⟩
  · have hstep : toITreeStep computation =
        (⟨.pure value, PEmpty.elim⟩ : (ITree.Poly p β).Obj (Resumption p β)) := by
      unfold toITreeStep
      rw [h]
    rw [M.dest_corec_eq toITreeStep computation hstep]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext direction
      exact PEmpty.elim direction
  · have hstep : toITreeStep computation =
        (⟨.query position, next⟩ : (ITree.Poly p β).Obj (Resumption p β)) := by
      unfold toITreeStep
      rw [h]
    rw [M.dest_corec_eq toITreeStep computation hstep]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      rfl

@[simp] theorem toITree_pure (value : β) :
    toITree (pure (p := p) value) = ITree.pure value := by
  apply M.eq_of_dest_eq
  change ITree.shape' (toITree (pure (p := p) value)) =
    ITree.shape' (ITree.pure value)
  rw [shape'_toITree, dest_pure, ITree.shape'_pure]

@[simp] theorem toITree_query (position : p.A)
    (next : p.B position → Resumption p β) :
    toITree (query position next) =
      ITree.query position (fun direction => toITree (next direction)) := by
  apply M.eq_of_dest_eq
  simp

theorem toITree_bind (computation : Resumption p α)
    (k : α → Resumption p β) :
    toITree (bind computation k) =
      ITree.bind (toITree computation) (fun value => toITree (k value)) := by
  refine M.bisim
    (fun left right : ITree p β => left = right ∨ ∃ source : Resumption p α,
      left = toITree (bind source k) ∧
      right = ITree.bind (toITree source) (fun value => toITree (k value)))
    ?_ _ _ (Or.inr ⟨computation, rfl, rfl⟩)
  rintro left right (hEq | ⟨source, hleft, hright⟩)
  · subst left
    rcases h : ITree.shape' right with ⟨shape, next⟩
    exact ⟨shape, next, next, h, h, fun _ => Or.inl rfl⟩
  · subst left
    subst right
    rcases h : dest source with value | ⟨position, next⟩
    · have hsource : source = pure value := by
        apply eq_of_dest_eq
        simpa using h
      subst source
      simp only [bind_pure_left, toITree_pure, ITree.bind_pure_left]
      rcases hk : ITree.shape' (toITree (k value)) with ⟨shape, next⟩
      exact ⟨shape, next, next, hk, hk, fun _ => Or.inl rfl⟩
    · have hsource : source = query position next := by
        apply eq_of_dest_eq
        simpa using h
      subst source
      simp only [bind_query, toITree_query, ITree.bind_query]
      refine ⟨.query position,
        fun direction => toITree (bind (next direction) k),
        fun direction => ITree.bind (toITree (next direction))
          (fun value => toITree (k value)),
        ITree.shape'_query _ _, ITree.shape'_query _ _, ?_⟩
      exact fun direction => Or.inr ⟨next direction, rfl, rfl⟩

@[simp] theorem toITree_map (f : α → β) (computation : Resumption p α) :
    toITree (map f computation) = ITree.map f (toITree computation) := by
  unfold map ITree.map
  rw [toITree_bind]
  simp

@[simp] theorem toITree_mapLens (lens : Lens p q)
    (computation : Resumption p β) :
    toITree (mapLens lens computation) = ITree.mapSpec lens (toITree computation) := by
  refine M.bisim
    (fun left right : ITree q β => ∃ source : Resumption p β,
      left = toITree (mapLens lens source) ∧
      right = ITree.mapSpec lens (toITree source))
    ?_ _ _ ⟨computation, rfl, rfl⟩
  rintro left right ⟨source, hleft, hright⟩
  subst left
  subst right
  rcases h : dest source with value | ⟨position, next⟩
  · have hsource : source = pure value := by
      apply eq_of_dest_eq
      simpa using h
    subst source
    simp only [mapLens_pure, toITree_pure, ITree.mapSpec_pure]
    exact ⟨.pure value, PEmpty.elim, PEmpty.elim,
      ITree.shape'_pure _, ITree.shape'_pure _, fun direction => PEmpty.elim direction⟩
  · have hsource : source = query position next := by
      apply eq_of_dest_eq
      simpa using h
    subst source
    simp only [mapLens_query, toITree_query, ITree.mapSpec_query]
    refine ⟨.query (lens.toFunA position),
      fun direction => toITree
        (mapLens lens (next (lens.toFunB position direction))),
      fun direction => ITree.mapSpec lens
        (toITree (next (lens.toFunB position direction))),
      ITree.shape'_query _ _, ITree.shape'_query _ _, ?_⟩
    exact fun direction => ⟨next (lens.toFunB position direction), rfl, rfl⟩

/-! ## The tau-free greatest invariant -/

end PFunctor.Resumption

namespace ITree

variable {p : PFunctor.{uA, uB}} {β : Type uβ}

/-- One layer of the tau-free invariant. Pure nodes are accepted, step nodes
are rejected, and every continuation of a query must satisfy `R`. -/
def TauFreeF (R : _root_.ITree p β → Prop) (tree : _root_.ITree p β) : Prop :=
  match shape' tree with
  | ⟨.pure _, _⟩ => True
  | ⟨.step, _⟩ => False
  | ⟨.query _, next⟩ => ∀ direction, R (next direction)

theorem TauFreeF.mono {R S : _root_.ITree p β → Prop}
    (hRS : ∀ {tree}, R tree → S tree) {tree : _root_.ITree p β}
    (h : TauFreeF R tree) : TauFreeF S tree := by
  rcases hshape : shape' tree with ⟨shape, next⟩
  unfold TauFreeF at h ⊢
  rw [hshape] at h ⊢
  cases shape with
  | pure value => trivial
  | step => exact h
  | query position =>
      intro direction
      exact hRS (h direction)

/-- Greatest postfixed point of `TauFreeF`. This admits infinite visible-query
trees while ruling out a tau at every recursively reachable query child. -/
def TauFree (tree : _root_.ITree p β) : Prop :=
  ∃ R : _root_.ITree p β → Prop,
    (∀ {current}, R current → TauFreeF R current) ∧ R tree

/-- Coinduction into the tau-free greatest invariant. -/
theorem TauFree.coinduct (R : _root_.ITree p β → Prop)
    (closed : ∀ {tree}, R tree → TauFreeF R tree)
    {tree : _root_.ITree p β} (h : R tree) : TauFree tree :=
  ⟨R, closed, h⟩

/-- Unfold one layer of the tau-free greatest invariant. -/
theorem TauFree.unfold {tree : _root_.ITree p β} (h : TauFree tree) :
    TauFreeF TauFree tree := by
  rcases h with ⟨R, closed, htree⟩
  apply TauFreeF.mono (S := TauFree) (h := closed htree)
  intro current hcurrent
  exact ⟨R, closed, hcurrent⟩

/-- Fold one tau-free layer into the greatest invariant. -/
theorem TauFree.fold {tree : _root_.ITree p β}
    (h : TauFreeF TauFree tree) : TauFree tree := by
  let R : _root_.ITree p β → Prop := fun current => current = tree ∨ TauFree current
  apply TauFree.coinduct R
  · intro current hcurrent
    rcases hcurrent with rfl | hcurrent
    · exact TauFreeF.mono (fun hchild => Or.inr hchild) h
    · exact TauFreeF.mono (fun hchild => Or.inr hchild) hcurrent.unfold
  · exact Or.inl rfl

@[simp] theorem tauFree_pure (value : β) :
    TauFree (ITree.pure (F := p) value) := by
  apply TauFree.fold
  simp [TauFreeF]

@[simp] theorem tauFree_query (position : p.A)
    (next : p.B position → _root_.ITree p β) :
    TauFree (ITree.query position next) ↔ ∀ direction, TauFree (next direction) := by
  constructor
  · intro h
    simpa [TauFreeF] using h.unfold
  · intro h
    apply TauFree.fold
    simpa [TauFreeF]

theorem not_tauFree_step (tree : _root_.ITree p β) :
    ¬ TauFree (ITree.step tree) := by
  intro h
  simpa [TauFreeF] using h.unfold

/-- A tau-free tree observed as a query has tau-free children. -/
theorem TauFree.of_shape'_query {tree : _root_.ITree p β} {position : p.A}
    {next : p.B position → _root_.ITree p β}
    (hshape : shape' tree = ⟨.query position, next⟩) (h : TauFree tree) :
    ∀ direction, TauFree (next direction) := by
  have hunfold := h.unfold
  unfold TauFreeF at hunfold
  rw [hshape] at hunfold
  exact hunfold

/-- A tau-free tree cannot be observed as a silent step. -/
theorem TauFree.not_of_shape'_step {tree : _root_.ITree p β}
    {next : PUnit → _root_.ITree p β}
    (hshape : shape' tree = ⟨.step, next⟩) (h : TauFree tree) : False := by
  have hunfold := h.unfold
  unfold TauFreeF at hunfold
  rw [hshape] at hunfold
  exact hunfold

end ITree

/-! ## Exact image and inverse -/

namespace PFunctor.Resumption

variable {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}
  {α : Type uα} {β : Type uβ} {γ : Type uγ}

@[simp] theorem toITree_tauFree (computation : Resumption p β) :
    ITree.TauFree (toITree computation) := by
  apply ITree.TauFree.coinduct
    (fun tree => ∃ source : Resumption p β, tree = toITree source)
  · rintro tree ⟨source, rfl⟩
    rcases h : dest source with value | ⟨position, next⟩
    · simp [ITree.TauFreeF, h]
    · simp only [ITree.TauFreeF, shape'_toITree, h]
      intro direction
      exact ⟨next direction, rfl⟩
  · exact ⟨computation, rfl⟩

/-- The proof carried by one tau-free observation. -/
def TauFreeLayer (observed : (ITree.Poly p β).Obj (_root_.ITree p β)) : Prop :=
  match observed with
  | ⟨.pure _, _⟩ => True
  | ⟨.step, _⟩ => False
  | ⟨.query _, next⟩ => ∀ direction, ITree.TauFree (next direction)

/-- Package a tau-free tree's observation with its one-layer invariant. -/
def tauFreeHead (state : {tree : _root_.ITree p β // ITree.TauFree tree}) :
    Σ' observed : (ITree.Poly p β).Obj (_root_.ITree p β), TauFreeLayer observed :=
  ⟨ITree.shape' state.1, by
    simpa [TauFreeLayer, ITree.TauFreeF] using state.2.unfold⟩

/-- Decode a proof-carrying tau-free observation into a resumption layer. -/
def ofTauFreeHead
    (head : Σ' observed : (ITree.Poly p β).Obj (_root_.ITree p β), TauFreeLayer observed) :
    β ⊕ p.Obj {tree : _root_.ITree p β // ITree.TauFree tree} :=
  match head with
  | ⟨⟨.pure value, _⟩, _⟩ => Sum.inl value
  | ⟨⟨.step, _⟩, impossible⟩ => False.elim impossible
  | ⟨⟨.query position, next⟩, layer⟩ =>
      Sum.inr ⟨position, fun direction => ⟨next direction, layer direction⟩⟩

/-- Coalgebraic inverse for removing the impossible tau case from a tau-free
interaction tree. All observable data comes from `shape'`; the proof is used
only to reject tau and certify query children. The proof-carrying subtype makes
the inverse constructive: its impossible tau case is eliminated by
`False.elim`. -/
def ofTauFreeStep (state : {tree : _root_.ITree p β // ITree.TauFree tree}) :
    β ⊕ p.Obj {tree : _root_.ITree p β // ITree.TauFree tree} :=
  ofTauFreeHead (tauFreeHead state)

/-- Remove the impossible tau case from a tau-free interaction tree. -/
def ofTauFreeITree
    (state : {tree : _root_.ITree p β // ITree.TauFree tree}) : Resumption p β :=
  corec ofTauFreeStep state

theorem ofTauFreeStep_of_shape'_pure
    (state : {tree : _root_.ITree p β // ITree.TauFree tree}) (value : β)
    (next : PEmpty → _root_.ITree p β)
    (hshape : ITree.shape' state.1 = ⟨.pure value, next⟩) :
    ofTauFreeStep state = Sum.inl value := by
  have hhead : tauFreeHead state =
      (⟨⟨.pure value, next⟩, trivial⟩ :
        Σ' observed : (ITree.Poly p β).Obj (_root_.ITree p β), TauFreeLayer observed) := by
    exact PSigma.mk.inj_iff.mpr ⟨hshape, proof_irrel_heq _ _⟩
  rw [ofTauFreeStep, hhead]
  rfl

theorem ofTauFreeStep_of_shape'_query
    (state : {tree : _root_.ITree p β // ITree.TauFree tree}) (position : p.A)
    (next : p.B position → _root_.ITree p β)
    (hshape : ITree.shape' state.1 = ⟨.query position, next⟩) :
    ofTauFreeStep state = Sum.inr ⟨position, fun direction =>
      ⟨next direction, state.2.of_shape'_query hshape direction⟩⟩ := by
  have hhead : tauFreeHead state =
      (⟨⟨.query position, next⟩,
        fun direction => state.2.of_shape'_query hshape direction⟩ :
        Σ' observed : (ITree.Poly p β).Obj (_root_.ITree p β), TauFreeLayer observed) := by
    exact PSigma.mk.inj_iff.mpr ⟨hshape, proof_irrel_heq _ _⟩
  rw [ofTauFreeStep, hhead]
  rfl

@[simp] theorem dest_ofTauFreeITree
    (state : {tree : _root_.ITree p β // ITree.TauFree tree}) :
    dest (ofTauFreeITree state) =
      Sum.map (fun value : β => value) (p.map ofTauFreeITree) (ofTauFreeStep state) :=
  dest_corec ofTauFreeStep state

theorem toITree_ofTauFreeITree
    (state : {tree : _root_.ITree p β // ITree.TauFree tree}) :
    toITree (ofTauFreeITree state) = state.1 := by
  refine M.bisim
    (fun left right : _root_.ITree p β => ∃ current,
      left = toITree (ofTauFreeITree current) ∧ right = current.1)
    ?_ _ _ ⟨state, rfl, rfl⟩
  rintro left right ⟨current, hleft, hright⟩
  subst left
  subst right
  rcases hshape : ITree.shape' current.1 with ⟨shape, next⟩
  cases shape with
  | pure value =>
      refine ⟨.pure value, PEmpty.elim, next, ?_, hshape, fun direction => ?_⟩
      · change ITree.shape' (toITree (ofTauFreeITree current)) = _
        rw [shape'_toITree, dest_ofTauFreeITree]
        rw [ofTauFreeStep_of_shape'_pure current value next hshape]
        rfl
      · exact PEmpty.elim direction
  | step =>
      exfalso
      exact current.2.not_of_shape'_step hshape
  | query position =>
      have hchildren : ∀ direction, ITree.TauFree (next direction) :=
        current.2.of_shape'_query hshape
      refine ⟨.query position,
        fun direction => toITree
          (ofTauFreeITree ⟨next direction, hchildren direction⟩),
        next, ?_, hshape, ?_⟩
      · change ITree.shape' (toITree (ofTauFreeITree current)) = _
        rw [shape'_toITree, dest_ofTauFreeITree]
        rw [ofTauFreeStep_of_shape'_query current position next hshape]
        rfl
      · exact fun direction =>
          ⟨⟨next direction, hchildren direction⟩, rfl, rfl⟩

theorem ofTauFreeITree_toITree (computation : Resumption p β) :
    ofTauFreeITree ⟨toITree computation, toITree_tauFree computation⟩ = computation := by
  apply bisim
    (fun left right => ∃ source : Resumption p β,
      left = ofTauFreeITree ⟨toITree source, toITree_tauFree source⟩ ∧ right = source)
  · rintro left right ⟨source, hleft, hright⟩
    subst left
    subst right
    rcases h : dest source with value | ⟨position, next⟩
    · refine .pure value ?_ h
      have hshape := shape'_toITree source
      rw [h] at hshape
      rw [dest_ofTauFreeITree]
      rw [ofTauFreeStep_of_shape'_pure _ value _ hshape]
      rfl
    · refine .query position
        (fun direction => ofTauFreeITree
          ⟨toITree (next direction), toITree_tauFree (next direction)⟩)
        next ?_ h (fun direction => ⟨next direction, rfl, rfl⟩)
      have hshape := shape'_toITree source
      rw [h] at hshape
      rw [dest_ofTauFreeITree]
      rw [ofTauFreeStep_of_shape'_query _ position _ hshape]
      rfl
  · exact ⟨computation, rfl, rfl⟩

/-- Resumptions are exactly the tau-free interaction trees. -/
def equivTauFreeITree :
    Resumption p β ≃ {tree : _root_.ITree p β // ITree.TauFree tree} where
  toFun computation := ⟨toITree computation, toITree_tauFree computation⟩
  invFun := ofTauFreeITree
  left_inv := ofTauFreeITree_toITree
  right_inv state := Subtype.ext (toITree_ofTauFreeITree state)

theorem toITree_injective : Function.Injective (toITree (p := p) (β := β)) :=
  fun _ _ h => equivTauFreeITree.injective (Subtype.ext h)

end PFunctor.Resumption
