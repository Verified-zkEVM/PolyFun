/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Family

/-!
# Parameter substitutions for binding families

A family homomorphism supplies constructor-local compatibility with changing
parameter contexts. Its finite-tree action is an indexed traversal, so generic
traversal fusion and relational interpretation laws apply to it.
-/

public section

universe u v w z m n d e

namespace IPFunctor.ScopedFamily

variable {W : Type u} {S : W → Type v}

/-- A constructor translation that lifts its parameter map at each child. -/
structure Hom (σ τ : ScopedFamily.{u, v, w, z} W S)
    (M : W → W → Type m) (f : ∀ {w z}, M w z → S w → S z) where
  /-- Translate a constructor's head. -/
  op : ∀ {w z} (μ : M w z) {a}, σ.Op w a → τ.Op z (f μ a)
  /-- Select the original child supplying each target child. -/
  arg : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a), τ.Arg (op μ o) → σ.Arg o
  /-- Lift the parameter map into each recursive argument. -/
  next : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a) (p : τ.Arg (op μ o)),
    M (σ.world o (arg μ o p)) (τ.world (op μ o) p)
  /-- Preserve the positions and translated sorts of freshly bound variables. -/
  binders : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a) (p : τ.Arg (op μ o)),
    (σ.binders o (arg μ o p)).map (f (next μ o p)) = τ.binders (op μ o) p
  /-- Parameter substitution commutes with entering the child's context. -/
  reindex : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a) (p : τ.Arg (op μ o)) (b : S w),
    f (next μ o p) (σ.reindex o (arg μ o p) b) = τ.reindex (op μ o) p (f μ b)
  /-- Preserve each child's translated result sort. -/
  sort : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a) (p : τ.Arg (op μ o)),
    f (next μ o p) (σ.sort o (arg μ o p)) = τ.sort (op μ o) p

/-- A parameter map together with the local context and result it transports. -/
inductive MapState (M : W → W → Type m) (f : ∀ {w z}, M w z → S w → S z) :
    Judgment S → Judgment S → Type (max u v m) where
  | mk {w z} (μ : M w z) (Γ : List (S w)) (a : S w) :
      MapState M f ⟨w, Γ, a⟩ ⟨z, Γ.map (f μ), f μ a⟩

namespace Hom

/-- The identity family map transports only along equality of parameter contexts. -/
@[expose] def identity (σ : ScopedFamily.{u, v, w, z} W S) :
    Hom σ σ (fun w z => PLift (w = z)) (fun {_ _} e a => e.down ▸ a) where
  op := fun {_ _} e {_} op => by cases e.down; exact op
  arg := fun {_ _} e {_} op p => by cases e.down; exact p
  next := fun {_ _} e {_} op p => by cases e.down; exact ⟨rfl⟩
  binders := fun {_ _} e {_} op p => by cases e.down; exact List.map_id _
  reindex := fun {_ _} e {_} op p a => by cases e.down; rfl
  sort := fun {_ _} e {_} op p => by cases e.down; rfl

/-- Two parameter maps with their shared intermediate parameter context. -/
abbrev Composite (M : W → W → Type m) (N : W → W → Type n) (a c : W) :=
  (b : W) × M a b × N b c

variable {σ τ : ScopedFamily.{u, v, w, z} W S}
  {M : W → W → Type m} {f : ∀ {w z}, M w z → S w → S z}

/-- Compose family maps, lifting both parameter maps into each selected child. -/
@[expose] def comp {υ : ScopedFamily.{u, v, w, z} W S} {N : W → W → Type n}
    {g : ∀ {w z}, N w z → S w → S z} (h : Hom σ τ M f) (k : Hom τ υ N g) :
    Hom σ υ (Composite M N) (fun {_ _} μ => g μ.2.2 ∘ f μ.2.1) where
  op := fun {_ _} μ {_} op => k.op μ.2.2 (h.op μ.2.1 op)
  arg := fun {_ _} μ {_} op p => h.arg μ.2.1 op (k.arg μ.2.2 (h.op μ.2.1 op) p)
  next := fun {_ _} μ {_} op p => ⟨_, h.next μ.2.1 op (k.arg μ.2.2 (h.op μ.2.1 op) p),
    k.next μ.2.2 (h.op μ.2.1 op) p⟩
  binders := fun {_ _} μ {_} op p => by
    rw [← List.map_map, h.binders, k.binders]
  reindex := fun {_ _} μ {_} op p b => by
    change g _ (f _ _) = _
    rw [h.reindex, k.reindex]
    rfl
  sort := fun {_ _} μ {_} op p => by
    change g _ (f _ _) = _
    rw [h.sort, k.sort]

/-- The child's complete context, including both fresh and ambient bindings. -/
theorem context (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ : List (S w)} {a : S w} (o : σ.Op w a) (p : τ.Arg (h.op μ o)) :
    (σ.binders o (h.arg μ o p) ++ Γ.map (σ.reindex o (h.arg μ o p))).map
        (f (h.next μ o p)) =
      τ.binders (h.op μ o) p ++ (Γ.map (f μ)).map (τ.reindex (h.op μ o) p) := by
  rw [List.map_append, h.binders, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  exact h.reindex μ o p b

/-- The complete child-context square also commutes on value renamings. -/
theorem context_renaming (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} (ρ : ScopedSignature.Renaming Γ Δ)
    {a : S w} (o : σ.Op w a) (p : τ.Arg (h.op μ o)) :
    (ScopedSignature.Renaming.cast (h.context μ o p) (h.context μ o p)
      (ScopedSignature.Renaming.map (f (h.next μ o p))
        (ScopedSignature.Renaming.liftMany
          (ScopedSignature.Renaming.map (σ.reindex o (h.arg μ o p)) ρ)
          (σ.binders o (h.arg μ o p)))) : ScopedSignature.Renaming _ _) =
      (fun {_} x => ScopedSignature.Renaming.liftMany
        (ScopedSignature.Renaming.map (τ.reindex (h.op μ o) p)
          (ScopedSignature.Renaming.map (f μ) ρ)) (τ.binders (h.op μ o) p) x) := by
  let r := σ.reindex o (h.arg μ o p)
  let g := f (h.next μ o p)
  let k := τ.reindex (h.op μ o) p
  have hs : g ∘ r = k ∘ f μ := funext (h.reindex μ o p)
  have hc (Γ : List (S w)) : (Γ.map r).map g = (Γ.map (f μ)).map k := by
    simp only [List.map_map, hs]
  have hm : HEq (ScopedSignature.Renaming.map g (ScopedSignature.Renaming.map r ρ) :
      ScopedSignature.Renaming _ _)
      (ScopedSignature.Renaming.map k (ScopedSignature.Renaming.map (f μ) ρ) :
        ScopedSignature.Renaming _ _) := by
    have h1 := ScopedSignature.Renaming.map_map r g ρ
    have h2 := ScopedSignature.Renaming.map_map (f μ) k ρ
    exact (ScopedSignature.Renaming.cast_heq _ _ _).symm.trans
      ((heq_of_eq h1).trans ((ScopedSignature.Renaming.map_heq hs ρ).trans
        ((heq_of_eq h2).symm.trans (ScopedSignature.Renaming.cast_heq _ _ _))))
  apply eq_of_heq
  apply (ScopedSignature.Renaming.cast_heq _ _ _).trans
  apply (ScopedSignature.Renaming.cast_heq List.map_append List.map_append _).symm.trans
  apply (heq_of_eq (ScopedSignature.Renaming.map_liftMany _ _ _)).trans
  exact ScopedSignature.Renaming.liftMany_heq (hc Γ) (hc Δ) hm (h.binders μ o p)

/-- Assemble the local context equations into an indexed traversal. -/
@[expose] def toTraversal (h : Hom σ τ M f) :
    Traversal σ.polynomial τ.polynomial (MapState M f) where
  op s o := match s with
    | .mk μ _ _ => h.op μ o
  arg s o p := match s with
    | .mk μ _ _ => h.arg μ o p
  next s o p := by
    cases s with
    | @mk w z μ Γ a =>
        have he : (⟨τ.world (h.op μ o) p,
            (σ.binders o (h.arg μ o p) ++ Γ.map (σ.reindex o (h.arg μ o p))).map
              (f (h.next μ o p)), f (h.next μ o p) (σ.sort o (h.arg μ o p))⟩ : Judgment S) =
            τ.polynomial.src ⟨z, Γ.map (f μ), f μ a⟩ (h.op μ o) p := by
          exact congrArg (fun q => (⟨τ.world (h.op μ o) p, q⟩ : Judgment S))
            (Prod.ext (h.context μ o p) (h.sort μ o p))
        exact he ▸ MapState.mk (h.next μ o p) _ _

/-- Translate variable leaves by their original positions. -/
@[expose] def leaf {i j : Judgment S} (s : MapState M f i j) (x : ScopedVar i.2.1 i.2.2) :
    IFreeM τ.polynomial (fun j => ScopedVar j.2.1 j.2.2) j :=
  match s with
  | .mk μ _ _ => .pure (x.map (f μ))

end Hom

/-- Substitute parameters in finite syntax using the language's constructor laws. -/
@[expose] def Term.map {σ τ : ScopedFamily.{u, v, w, z} W S}
    {M : W → W → Type m} {f : ∀ {w z}, M w z → S w → S z}
    (h : Hom σ τ M f) {w z : W} (μ : M w z) {Γ : List (S w)} {a : S w}
    (t : σ.Term w Γ a) : τ.Term z (Γ.map (f μ)) (f μ a) :=
  t.traverse h.toTraversal Hom.leaf (.mk μ Γ a)

@[simp] theorem Term.map_var {σ τ : ScopedFamily.{u, v, w, z} W S}
    {M : W → W → Type m} {f : ∀ {w z}, M w z → S w → S z}
    (h : Hom σ τ M f) {w z : W} (μ : M w z) {Γ : List (S w)} {a : S w}
    (x : ScopedVar Γ a) : (var x).map h μ = var (x.map (f μ)) := rfl

namespace Term

variable {σ τ : ScopedFamily.{u, v, w, z} W S}
  {M : W → W → Type m} {f : ∀ {w z}, M w z → S w → S z}

/-- Normalize a context and result sort without changing the syntax tree. -/
@[expose] def cast {w : W} {Γ Δ : List (S w)} {a b : S w}
    (hΓ : Γ = Δ) (ha : a = b) (t : σ.Term w Γ a) : σ.Term w Δ b := ha ▸ hΓ ▸ t

@[simp] theorem cast_self {w : W} {Γ : List (S w)} {a : S w}
    (hΓ : Γ = Γ) (ha : a = a) (t : σ.Term w Γ a) : t.cast hΓ ha = t := rfl

/-- Transport across possibly different contexts and sorts retains the same tree. -/
@[simp] theorem cast_heq {w : W} {Γ Δ : List (S w)} {a b : S w}
    (hΓ : Γ = Δ) (ha : a = b) (t : σ.Term w Γ a) : HEq (t.cast hΓ ha) t := by
  cases hΓ
  cases ha
  rfl

/-- Context normalization commutes with renaming. -/
theorem cast_rename {w : W} {Γ Δ Γ' Δ' : List (S w)} {a b : S w}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (ha : a = b)
    (ρ : ScopedSignature.Renaming Γ Δ) (t : σ.Term w Γ a) :
    (t.rename ρ).cast hΔ ha =
      (t.cast hΓ ha).rename (ScopedSignature.Renaming.cast hΓ hΔ ρ) := by
  cases hΓ
  cases hΔ
  cases ha
  rfl

/-- Successive context and result transports compose. -/
theorem cast_cast {w : W} {Γ Δ Θ : List (S w)} {a b c : S w}
    (hΓ : Γ = Δ) (hΔ : Δ = Θ) (ha : a = b) (hb : b = c) (t : σ.Term w Γ a) :
    (t.cast hΓ ha).cast hΔ hb = t.cast (hΓ.trans hΔ) (ha.trans hb) := by
  cases hΓ
  cases hΔ
  cases ha
  cases hb
  rfl

/-- Parameter maps commute with context and result normalization. -/
theorem map_cast (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} {a b : S w} (hΓ : Γ = Δ) (ha : a = b) (t : σ.Term w Γ a) :
    (t.cast hΓ ha).map h μ =
      (t.map h μ).cast (congrArg (List.map (f μ)) hΓ) (congrArg (f μ) ha) := by
  cases hΓ
  cases ha
  rfl

/-- Transport a variable by transporting its context and sort. -/
theorem cast_var {w : W} {Γ Δ : List (S w)} {a b : S w}
    (hΓ : Γ = Δ) (ha : a = b) (x : ScopedVar Γ a) :
    (var (σ := σ) x).cast hΓ ha = var (ha ▸ hΓ ▸ x) := by
  cases hΓ
  cases ha
  rfl

/-- Transport an ambient context through each constructor's child contexts. -/
theorem cast_node {w : W} {Γ Δ : List (S w)} {a : S w}
    (hΓ : Γ = Δ) (op : σ.Op w a)
    (args : (p : σ.Arg op) → σ.Term (σ.world op p)
      (σ.binders op p ++ Γ.map (σ.reindex op p)) (σ.sort op p)) :
    (node op args).cast hΓ rfl = node op (fun p => (args p).cast
      (congrArg (fun Γ => σ.binders op p ++ Γ.map (σ.reindex op p)) hΓ) rfl) := by
  cases hΓ
  rfl

/-- A family map translates each child at its lifted parameter map. -/
theorem map_node (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ : List (S w)} {a : S w} (op : σ.Op w a)
    (args : (p : σ.Arg op) → σ.Term (σ.world op p)
      (σ.binders op p ++ Γ.map (σ.reindex op p)) (σ.sort op p)) :
    (node op args).map h μ = node (h.op μ op) (fun p =>
      ((args (h.arg μ op p)).map h (h.next μ op p)).cast
        (h.context μ op p) (h.sort μ op p)) := by
  change IFreeM.liftBind _ _ = IFreeM.liftBind _ _
  congr 1
  funext p
  exact transport h _ _ _ _ _
where
  transport (h : Hom σ τ M f) {w z : W} (μ : M w z)
      {Γ : List (S w)} {a : S w} {Δ : List (S z)} {b : S z}
      (hΓ : Γ.map (f μ) = Δ) (ha : f μ a = b) (t : σ.Term w Γ a)
      (e : (⟨z, Γ.map (f μ), f μ a⟩ : Judgment S) = ⟨z, Δ, b⟩) :
      t.traverse h.toTraversal Hom.leaf (e ▸ MapState.mk μ Γ a) =
        (t.map h μ).cast hΓ ha := by
    cases hΓ
    cases ha
    rfl

/-- Parameter maps commute with value renaming, including under mixed binders. -/
theorem map_rename (h : Hom σ τ M f) {w z : W} (μ : M w z)
    {Γ Δ : List (S w)} {a : S w} (ρ : ScopedSignature.Renaming Γ Δ)
    (t : σ.Term w Γ a) :
    (t.rename ρ).map h μ = (t.map h μ).rename (ScopedSignature.Renaming.map (f μ) ρ) := by
  induction t using Term.inductionOn generalizing z with
  | hvar => simp only [rename_var, map_var, ScopedSignature.Renaming.map_apply]
  | hnode w Γ a op args ih =>
      simp only [rename_node, map_node]
      congr 1
      funext p
      rw [ih (h.arg μ op p), cast_rename (h.context μ op p), h.context_renaming]

/-- Identity family maps disappear after normalizing the ambient context. -/
@[simp] theorem map_identity {w : W} (e : PLift (w = w))
    {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a)
    (hΓ : Γ.map id = Γ) (ha : a = a) :
    (t.map (Hom.identity σ) e).cast hΓ ha = t := by
  induction t using Term.inductionOn with
  | hvar w Γ a x =>
      simp only [map_var, cast_var]
      change var (List.map_id Γ ▸ x.map id) = var x
      rw [ScopedVar.map_id]
      exact congrArg var (eq_of_heq
        ((eqRec_heq (φ := fun Δ => ScopedVar Δ a) (List.map_id Γ) _).trans
          (eqRec_heq (φ := fun Δ => ScopedVar Δ a) (List.map_id Γ).symm x)))
  | hnode w Γ a op args ih =>
      simp only [map_node, cast_node]
      change node op _ = node op _
      congr 1
      funext p
      apply eq_of_heq
      apply (cast_heq _ _ _).trans
      apply (cast_heq _ _ _).trans
      exact (cast_heq _ _ _).symm.trans (heq_of_eq (ih p ⟨rfl⟩ (List.map_id _) rfl))

/-- Identity family maps retain the tree across possibly different equal parameter contexts. -/
@[simp] theorem map_identity_heq {w z : W} (e : PLift (w = z))
    {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a) :
    HEq (t.map (Hom.identity σ) e) t := by
  rcases e with ⟨h⟩
  cases h
  exact (cast_heq _ _ _).symm.trans (heq_of_eq
    (map_identity ⟨rfl⟩ t (List.map_id Γ) rfl))

/-- Successive family maps compose after normalizing the mapped ambient context. -/
theorem map_map {υ : ScopedFamily.{u, v, w, z} W S} {N : W → W → Type n}
    {g : ∀ {w z}, N w z → S w → S z} (h : Hom σ τ M f) (k : Hom τ υ N g)
    {w z y : W} (μ : M w z) (ν : N z y) {Γ : List (S w)} {a : S w}
    (t : σ.Term w Γ a) :
    ((t.map h μ).map k ν).cast List.map_map rfl = t.map (h.comp k) ⟨z, μ, ν⟩ := by
  induction t using Term.inductionOn generalizing z y with
  | hvar w Γ a x =>
      simp only [map_var, cast_var]
      exact congrArg var (ScopedVar.map_map (f μ) (g ν) x)
  | hnode w Γ a op args ih =>
      simp only [map_node, cast_node, map_cast, cast_cast]
      change node _ _ = node _ _
      congr 1
      funext p
      have hp := ih (h.arg μ op (k.arg ν (h.op μ op) p))
        (h.next μ op (k.arg ν (h.op μ op) p)) (k.next ν (h.op μ op) p)
      exact eq_of_heq ((cast_heq _ _ _).trans
        (((cast_heq _ _ _).symm.trans (heq_of_eq hp)).trans (cast_heq _ _ _).symm))

/-- Constructor-local compatibility transports interpretations through a family map.
The relation may compare different domains at different parameter assignments. -/
theorem fold_map_rel (h : Hom σ τ M f)
    {D : Judgment S → Type d} {E : Judgment S → Type e}
    (sourceVars : ∀ j, ScopedVar j.2.1 j.2.2 → D j) (sourceAlg : FoldAlgebra σ.polynomial D)
    (targetVars : ∀ j, ScopedVar j.2.1 j.2.2 → E j) (targetAlg : FoldAlgebra τ.polynomial E)
    (Rel : ∀ {i j}, MapState M f i j → D i → E j → Prop)
    (hvar : ∀ {w z} (μ : M w z) (Γ : List (S w)) (a : S w) (x : ScopedVar Γ a),
      Rel (.mk μ Γ a) (sourceVars _ x) (targetVars _ (x.map (f μ))))
    (hnode : ∀ {i j} (s : MapState M f i j) (op : σ.polynomial.A i)
      (ds : (p : σ.polynomial.B i op) → D (σ.polynomial.src i op p))
      (es : (p : τ.polynomial.B j (h.toTraversal.op s op)) →
        E (τ.polynomial.src j (h.toTraversal.op s op) p)),
      (∀ p, Rel (h.toTraversal.next s op p) (ds (h.toTraversal.arg s op p)) (es p)) →
      Rel s (sourceAlg i op ds) (targetAlg j (h.toTraversal.op s op) es))
    {w z : W} (μ : M w z) {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a) :
    Rel (.mk μ Γ a) (t.fold sourceVars sourceAlg) ((t.map h μ).fold targetVars targetAlg) := by
  apply IFreeM.fold_traverse_rel h.toTraversal Hom.leaf
    sourceVars sourceAlg targetVars targetAlg Rel ?_ hnode (.mk μ Γ a) t
  intro i j s x
  cases s
  exact hvar _ _ _ x

end Term

end IPFunctor.ScopedFamily
