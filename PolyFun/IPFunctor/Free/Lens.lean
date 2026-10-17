/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Bound.Reindex

/-!
# Transporting State-Indexed Free Trees Along Lenses

`IPFunctor.IFreeM.mapLens l` transports a tree over `P` to a tree over `Q` along a lens
`l : Lens P Q`: each shape is relabelled forward by `l.toFunA`, and each response is read back by
`l.toFunB`. The source-index law `l.src_eq` is an equality of states, so each continuation is
transported along it. Leaves, and therefore leaf states, are unchanged.

Along a coproduct injection the source-index law is `rfl`. `mapLens` along `Lens.inl` or
`Lens.inr` then commutes with `liftBind` with no cast (`mapLens_inl_liftBind`), embeds programs
over a summand injectively into programs over the sum (`mapLens_inl_injective`), and leaves
their roll bounds unchanged (`isRollBound_mapLens_inl_iff`). Along an arbitrary lens, a roll bound
whose check and cost are read through `l.toFunA` transports forward (`IsRollBound.mapLens`).
-/

public section

universe uI uA₁ uA₂ uB uB₁ uB₂ v

namespace IPFunctor.IFreeM

variable {I : Type uI} {X : I → Type v}

/-- Transport a tree along a lens: relabel each shape forward and read each response back,
transporting each continuation along the source-index law. -/
@[expose] def mapLens {P : Endo.{uI, uA₁, uB₁} I} {Q : Endo.{uI, uA₂, uB₂} I}
    (l : Lens P Q) {s : I} (x : IFreeM P X s) : IFreeM Q X s :=
  x.reindex l.toReindexing (fun _ value => value)

section mapLens

variable {P : Endo.{uI, uA₁, uB₁} I} {Q : Endo.{uI, uA₂, uB₂} I} (l : Lens P Q) {s : I}

@[simp]
lemma mapLens_pure (x : X s) : (IFreeM.pure (P := P) x).mapLens l = .pure x := rfl

lemma mapLens_liftBind (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.liftBind a r).mapLens l =
      .liftBind (l.toFunA s a) fun d => l.src_eq s a d ▸ (r (l.toFunB s a d)).mapLens l :=
  rfl

/-- A lens carries a roll bound whose check and cost are read through `l.toFunA` to the
transported tree. -/
theorem IsRollBound.mapLens {B : Type*} {canRoll : (s : I) → Q.A s → B → Prop}
    {cost : (s : I) → Q.A s → B → B} {x : IFreeM P X s} {b : B}
    (h : x.IsRollBound b (fun s a => canRoll s (l.toFunA s a))
      (fun s a => cost s (l.toFunA s a))) :
    (x.mapLens l).IsRollBound b canRoll cost :=
  h.reindex l.toReindexing (fun _ value => value)

/-- A lens carries a charge bound whose charge is read through `l.toFunA` to the transported
tree. -/
theorem IsChargeBound.mapLens {c : (s : I) → Q.A s → ℕ} {x : IFreeM P X s} {n : ℕ}
    (h : x.IsChargeBound (fun s a => c s (l.toFunA s a)) n) :
    (x.mapLens l).IsChargeBound c n :=
  IsRollBound.mapLens l h

/-- A lens preserves total roll bounds: it relabels shapes and selects source branches. -/
theorem IsTotalRollBound.mapLens {x : IFreeM P X s} {n : ℕ} (h : x.IsTotalRollBound n) :
    (x.mapLens l).IsTotalRollBound n :=
  IsRollBound.mapLens l h

end mapLens

/-! ## Along coproduct injections -/

section sum

variable {P : Endo.{uI, uA₁, uB} I} {Q : Endo.{uI, uA₂, uB} I} {s : I}

/-- Along the left injection the transport is trivial: `mapLens` commutes with `liftBind` with
no cast. -/
@[simp]
lemma mapLens_inl_liftBind (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.liftBind a r).mapLens (Lens.inl (Q := Q)) =
      IFreeM.liftBind (P := P.sum Q) (.inl a) fun b => (r b).mapLens Lens.inl :=
  rfl

/-- Along the right injection the transport is trivial: `mapLens` commutes with `liftBind` with
no cast. -/
@[simp]
lemma mapLens_inr_liftBind (a : Q.A s) (r : (b : Q.B s a) → IFreeM Q X (Q.src s a b)) :
    (IFreeM.liftBind a r).mapLens (Lens.inr (P := P)) =
      IFreeM.liftBind (P := P.sum Q) (.inr a) fun b => (r b).mapLens Lens.inr :=
  rfl

/-- Programs over `P` embed injectively into programs over `P.sum Q`. -/
theorem mapLens_inl_injective :
    Function.Injective (mapLens (X := X) (Lens.inl (P := P) (Q := Q)) (s := s)) := by
  intro x y hxy
  induction x using IFreeM.inductionOn with
  | pure t x =>
      cases y with
      | pure y => cases hxy; rfl
      | liftBind _ _ => cases hxy
  | liftBind t a r ih =>
      cases y with
      | pure _ => cases hxy
      | liftBind a' r' =>
          rw [mapLens_inl_liftBind, mapLens_inl_liftBind] at hxy
          obtain ⟨ha, hr⟩ := (liftBind_inj _ _ _ _).1 hxy
          cases Sum.inl_injective ha
          exact congrArg (IFreeM.liftBind a) (funext fun b => ih b (congrFun hr b))

/-- Programs over `Q` embed injectively into programs over `P.sum Q`. -/
theorem mapLens_inr_injective :
    Function.Injective (mapLens (X := X) (Lens.inr (P := P) (Q := Q)) (s := s)) := by
  intro x y hxy
  induction x using IFreeM.inductionOn with
  | pure t x =>
      cases y with
      | pure y => cases hxy; rfl
      | liftBind _ _ => cases hxy
  | liftBind t a r ih =>
      cases y with
      | pure _ => cases hxy
      | liftBind a' r' =>
          rw [mapLens_inr_liftBind, mapLens_inr_liftBind] at hxy
          obtain ⟨ha, hr⟩ := (liftBind_inj _ _ _ _).1 hxy
          cases Sum.inr_injective ha
          exact congrArg (IFreeM.liftBind a) (funext fun b => ih b (congrFun hr b))

/-- A roll bound on a program embedded by the left injection is a roll bound on the program,
with the checks and costs of the left summand. -/
theorem isRollBound_mapLens_inl_iff {B : Type*}
    {canRoll : (s : I) → (P.sum Q).A s → B → Prop} {cost : (s : I) → (P.sum Q).A s → B → B}
    (x : IFreeM P X s) (b : B) :
    (x.mapLens Lens.inl).IsRollBound b canRoll cost ↔
      x.IsRollBound b (fun s a => canRoll s (.inl a)) (fun s a => cost s (.inl a)) :=
  isRollBound_reindex_iff Lens.inl.toReindexing (fun _ value => value)
    (fun _ _ answer => ⟨answer, rfl⟩) x b

/-- A roll bound on a program embedded by the right injection is a roll bound on the program,
with the checks and costs of the right summand. -/
theorem isRollBound_mapLens_inr_iff {B : Type*}
    {canRoll : (s : I) → (P.sum Q).A s → B → Prop} {cost : (s : I) → (P.sum Q).A s → B → B}
    (x : IFreeM Q X s) (b : B) :
    (x.mapLens Lens.inr).IsRollBound b canRoll cost ↔
      x.IsRollBound b (fun s a => canRoll s (.inr a)) (fun s a => cost s (.inr a)) :=
  isRollBound_reindex_iff Lens.inr.toReindexing (fun _ value => value)
    (fun _ _ answer => ⟨answer, rfl⟩) x b

end sum

end IPFunctor.IFreeM
