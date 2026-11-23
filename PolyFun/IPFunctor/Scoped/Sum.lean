/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.CBVInterpretation
public import PolyFun.IPFunctor.Free.Lens
public import ToCslib.Data.Fintype.Sum

/-!
# Sums of binding signatures

Two binding signatures over the same sorts combine into one whose constructors are those of
either summand, each with its own arguments, binders and argument sorts (`ScopedSignature.sum`).
As in `IPFunctor.sum`, the argument, binder and sort maps are `Sum` recursors written directly,
so at a constructor of one summand they reduce to that summand's maps. When each constructor of
both summands has finitely many arguments, so does each constructor of the sum, by
`Sum.instFintypeRec`, and `decide` checks the heads of concrete terms of the sum. Interpretations
of the two summands in one carrier combine into an interpretation of the sum:
`Interpretation.sum`, and `CBVInterpretation.sum` for call-by-value readings.

Both combined interpretations are reducible too. At a constructor of one summand, each reduces
to that summand's algebra, so `simp` with the summands' equations normalizes the reading of a
concrete term. An equation stated for arbitrary summands would not fire there, because `simp`
indexes the type arguments of `Sum.inl`. In such an equation they are the operation types of the
summand variables, but in a concrete term they reduce to concrete types.

A term of a summand is a term of the sum. `Term.inl` and `Term.inr` transport it with
`IFreeM.mapLens` along the injections `ScopedSignature.inl` and `ScopedSignature.inr` of the
syntax polynomials. The embedded term means what the original means in the summand's
interpretation (`Term.denote_inl`, `Term.denoteCBV_inl` and their right counterparts), by
`IFreeM.fold_reindex`. It uses exactly the images of the original's heads (`Term.heads_inl`,
`Term.heads_inr`). Algebras related at a set of heads of each summand are related at the union
of the images of the two sets (`CBVInterpretation.RelatedOn.sum`). A term embedded from one
summand therefore lies in a fragment of the sum to which `Term.denoteCBV_related` applies.
-/

public section

universe u v₁ v₂ w z z' z''

namespace IPFunctor.ScopedSignature

variable {S : Type u}

/-- The constructors of both signatures, over the same sorts. -/
@[expose, reducible] def sum (σ : ScopedSignature.{u, v₁, w} S)
    (τ : ScopedSignature.{u, v₂, w} S) : ScopedSignature.{u, max v₁ v₂, w} S where
  Op a := σ.Op a ⊕ τ.Op a
  Arg {a} := @Sum.rec (σ.Op a) (τ.Op a) (fun _ => Type w) (@σ.Arg a) (@τ.Arg a)
  binders {a} := @Sum.rec (σ.Op a) (τ.Op a)
    (fun o => @Sum.rec (σ.Op a) (τ.Op a) (fun _ => Type w) (@σ.Arg a) (@τ.Arg a) o → List S)
    (@σ.binders a) (@τ.binders a)
  sort {a} := @Sum.rec (σ.Op a) (τ.Op a)
    (fun o => @Sum.rec (σ.Op a) (τ.Op a) (fun _ => Type w) (@σ.Arg a) (@τ.Arg a) o → S)
    (@σ.sort a) (@τ.sort a)

variable {σ : ScopedSignature.{u, v₁, w} S} {τ : ScopedSignature.{u, v₂, w} S}

/-- The left injection of the syntax polynomial of `σ` into that of a sum. -/
@[expose] def inl : Lens σ.polynomial (σ.sum τ).polynomial where
  toFunA _ := Sum.inl
  toFunB _ _ := id
  src_eq _ _ _ := rfl

/-- The right injection of the syntax polynomial of `τ` into that of a sum. -/
@[expose] def inr : Lens τ.polynomial (σ.sum τ).polynomial where
  toFunA _ := Sum.inr
  toFunB _ _ := id
  src_eq _ _ _ := rfl

/-- A head of the left summand, as a head of the sum. -/
@[expose] def Head.inl (h : σ.Head) : (σ.sum τ).Head := ⟨h.sort, .inl h.op⟩

/-- A head of the right summand, as a head of the sum. -/
@[expose] def Head.inr (h : τ.Head) : (σ.sum τ).Head := ⟨h.sort, .inr h.op⟩

/-! ## Interpretations of a sum -/

section Interpretations

variable {V : S → Type z} {m : Type z → Type z'}

/-- Interpret each summand's constructors with its own algebra. -/
@[expose, reducible] def Interpretation.sum (alg₁ : Interpretation σ V)
    (alg₂ : Interpretation τ V) : Interpretation (σ.sum τ) V
  | _, .inl o, next => alg₁ o next
  | _, .inr o, next => alg₂ o next

/-- Interpret each summand's constructors with its own call-by-value algebra. -/
@[expose, reducible] def CBVInterpretation.sum (alg₁ : CBVInterpretation σ m V)
    (alg₂ : CBVInterpretation τ m V) : CBVInterpretation (σ.sum τ) m V
  | _, .inl o, next => alg₁ o next
  | _, .inr o, next => alg₂ o next

/-- Algebras related at a set of heads of each summand are related, as algebras of the sum, at
the union of the images of the two sets. -/
theorem CBVInterpretation.RelatedOn.sum {W : S → Type z''} {H₁ : Set σ.Head} {H₂ : Set τ.Head}
    {RV : ∀ a, V a → W a → Prop} {RC : ∀ a, m (V a) → W a → Prop}
    {alg₁ : CBVInterpretation σ m V} {alg₂ : CBVInterpretation τ m V}
    {alg₁' : Interpretation σ W} {alg₂' : Interpretation τ W}
    (h₁ : RelatedOn H₁ RV RC alg₁ alg₁') (h₂ : RelatedOn H₂ RV RC alg₂ alg₂') :
    RelatedOn (Head.inl '' H₁ ∪ Head.inr '' H₂) RV RC (alg₁.sum alg₂) (alg₁'.sum alg₂') := by
  rintro _ (⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩)
  · exact h₁ h hh
  · exact h₂ h hh

end Interpretations

/-! ## Terms of a summand -/

namespace Term

variable {Γ : List S} {a : S}

/-- A term of the left summand, read in the sum. -/
@[expose] def inl (t : σ.Term Γ a) : (σ.sum τ).Term Γ a :=
  IFreeM.mapLens ScopedSignature.inl t

/-- A term of the right summand, read in the sum. -/
@[expose] def inr (t : τ.Term Γ a) : (σ.sum τ).Term Γ a :=
  IFreeM.mapLens ScopedSignature.inr t

@[simp] theorem inl_var (x : ScopedVar Γ a) : inl (τ := τ) (var (σ := σ) x) = var x := rfl

@[simp] theorem inl_node (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) :
    inl (τ := τ) (node op args) = node (σ := σ.sum τ) (.inl op) fun p => inl (args p) := rfl

@[simp] theorem inr_var (x : ScopedVar Γ a) : inr (σ := σ) (var (σ := τ) x) = var x := rfl

@[simp] theorem inr_node (op : τ.Op a)
    (args : (p : τ.Arg op) → τ.Term (τ.binders op p ++ Γ) (τ.sort op p)) :
    inr (σ := σ) (node op args) = node (σ := σ.sum τ) (.inr op) fun p => inr (args p) := rfl

/-- An embedded left-summand term uses the left images of the original's heads. -/
theorem heads_inl (t : σ.Term Γ a) : (inl (τ := τ) t).heads = Head.inl '' t.heads := by
  refine (IFreeM.fold_reindex _ _ _ _ t).trans (IFreeM.fold_fusion (fun _ s => Head.inl '' s)
    _ _ _ _ (fun _ _ => Set.image_empty _) (fun j op ds => ?_) t).symm
  rw [Set.image_insert_eq, Set.image_iUnion]
  rfl

/-- An embedded right-summand term uses the right images of the original's heads. -/
theorem heads_inr (t : τ.Term Γ a) : (inr (σ := σ) t).heads = Head.inr '' t.heads := by
  refine (IFreeM.fold_reindex _ _ _ _ t).trans (IFreeM.fold_fusion (fun _ s => Head.inr '' s)
    _ _ _ _ (fun _ _ => Set.image_empty _) (fun j op ds => ?_) t).symm
  rw [Set.image_insert_eq, Set.image_iUnion]
  rfl

section Meanings

variable {V : S → Type z}

/-- A left-summand term means in the sum what it means in its own signature. -/
theorem denote_inl (alg₁ : Interpretation σ V) (alg₂ : Interpretation τ V) (t : σ.Term Γ a)
    (η : Env V Γ) : (inl (τ := τ) t).denote (alg₁.sum alg₂) η = t.denote alg₁ η := by
  unfold denote inl
  exact congrFun (IFreeM.fold_reindex _ _ _ _ t) η

/-- A right-summand term means in the sum what it means in its own signature. -/
theorem denote_inr (alg₁ : Interpretation σ V) (alg₂ : Interpretation τ V) (t : τ.Term Γ a)
    (η : Env V Γ) : (inr (σ := σ) t).denote (alg₁.sum alg₂) η = t.denote alg₂ η := by
  unfold denote inr
  exact congrFun (IFreeM.fold_reindex _ _ _ _ t) η

variable {m : Type z → Type z'} [Pure m]

/-- A left-summand term has in the sum the call-by-value meaning it has in its own
signature. -/
theorem denoteCBV_inl (alg₁ : CBVInterpretation σ m V) (alg₂ : CBVInterpretation τ m V)
    (t : σ.Term Γ a) (η : Env V Γ) :
    (inl (τ := τ) t).denoteCBV (alg₁.sum alg₂) η = t.denoteCBV alg₁ η := by
  unfold denoteCBV inl
  exact congrFun (IFreeM.fold_reindex _ _ _ _ t) η

/-- A right-summand term has in the sum the call-by-value meaning it has in its own
signature. -/
theorem denoteCBV_inr (alg₁ : CBVInterpretation σ m V) (alg₂ : CBVInterpretation τ m V)
    (t : τ.Term Γ a) (η : Env V Γ) :
    (inr (σ := σ) t).denoteCBV (alg₁.sum alg₂) η = t.denoteCBV alg₂ η := by
  unfold denoteCBV inr
  exact congrFun (IFreeM.fold_reindex _ _ _ _ t) η

end Meanings

end Term

end IPFunctor.ScopedSignature
