/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Free.Indexed
public import PolyFun.IPFunctor.Lens.Basic

/-!
# Transport of Indexed Free Monads Along Lenses

A lens `l : Lens P Q` between endomorphic indexed polynomials acts on free-monad trees:
`IFreeM.mapLens` rewrites each node's shape forward along `l.toFunA` and selects the source
branch by pulling the runtime response back along `l.toFunB`, leaving leaves untouched.
Because the source-index preservation law `src_eq` is propositional, each child's pre-state
agrees with the target only up to the pre-state transport `IFreeM.castPre`; the lens never
casts *at* a node, since shapes map within a fixed pre-state.

The single-index [`FreeM.mapLens`](Basic.lean) and two-index
[`FreeM₂.mapLens`](Indexed.lean) actions are leaf-family specializations of the primitive.
All three are functorial (`mapLens_id`, `mapLens_comp`) and are morphisms of the respective
monad structures (`mapLens_bind`).
-/

@[expose] public section

universe uI uA₁ uA₂ uA₃ uB₁ uB₂ uB₃ v

namespace IPFunctor

variable {I : Type uI}

namespace IFreeM

variable {P : Endo.{uI, uA₁, uB₁} I} {Q : Endo.{uI, uA₂, uB₂} I} {R : Endo.{uI, uA₃, uB₃} I}
  {X Y : I → Type v}

/-! ## Pre-state transport on the primitive -/

/-- Transport an `IFreeM` along an equality of pre-states. The specialization to the
terminal-state-marker family is [`FreeM₂.castPre`](Indexed.lean), definitionally. -/
def castPre {s s' : I} (e : s = s') (x : IFreeM P X s) : IFreeM P X s' :=
  e ▸ x

@[simp]
lemma castPre_rfl {s : I} (e : s = s) (x : IFreeM P X s) :
    castPre e x = x := rfl

@[simp]
lemma castPre_castPre {s s' s'' : I} (e : s = s') (e' : s' = s'') (x : IFreeM P X s) :
    castPre e' (castPre e x) = castPre (e.trans e') x := by
  subst e'; subst e; rfl

/-- Pre-state transports float out of the tree argument of `bind`. -/
@[simp]
lemma bind_castPre {s s' : I} (e : s = s') (x : IFreeM P X s)
    (g : ∀ u, X u → IFreeM P Y u) :
    (castPre e x).bind g = castPre e (x.bind g) := by
  subst e; rfl

/-- Pre-state transports commute with the family map. -/
@[simp]
lemma imap_castPre (f : ∀ u, X u → Y u) {s s' : I} (e : s = s') (x : IFreeM P X s) :
    (castPre e x).imap f = castPre e (x.imap f) := by
  subst e; rfl

/-! ## Transport along a lens -/

/-- Transport an `IFreeM` tree along a lens: shapes map forward, the runtime response at the
image shape selects the source branch via the backward map, and each child is carried to the
image source index along `src_eq`. Leaves are untouched. -/
protected def mapLens (l : Lens P Q) : {s : I} → IFreeM P X s → IFreeM Q X s
  | _, .pure x => .pure x
  | _, .roll (s := s) a r =>
      .roll (l.toFunA s a) fun d =>
        castPre (l.src_eq s a d) ((r (l.toFunB s a d)).mapLens l)

@[simp]
lemma mapLens_pure (l : Lens P Q) {s : I} (x : X s) :
    (IFreeM.pure (P := P) x).mapLens l = IFreeM.pure x := rfl

@[simp]
lemma mapLens_roll (l : Lens P Q) {s : I} (a : P.A s)
    (r : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.roll a r).mapLens l =
      IFreeM.roll (l.toFunA s a) (fun d =>
        castPre (l.src_eq s a d) ((r (l.toFunB s a d)).mapLens l)) := rfl

/-- Pre-state transports float out of `mapLens`. -/
@[simp]
lemma mapLens_castPre (l : Lens P Q) {s s' : I} (e : s = s') (x : IFreeM P X s) :
    (castPre e x).mapLens l = castPre e (x.mapLens l) := by
  subst e; rfl

@[simp]
lemma mapLens_id {s : I} (x : IFreeM P X s) :
    x.mapLens (Lens.id P) = x := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | roll s a r ih =>
    exact congrArg _ (funext fun d => (castPre_rfl _ _).trans (ih d))

@[simp]
lemma mapLens_comp (l : Lens Q R) (l' : Lens P Q) {s : I} (x : IFreeM P X s) :
    (x.mapLens l').mapLens l = x.mapLens (Lens.comp l l') := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | roll s a r ih =>
    simp only [mapLens_roll, mapLens_castPre, castPre_castPre]
    exact congrArg _ (funext fun d => congrArg (castPre _) (ih _))

/-- Transport along a lens is a morphism of the (family-polymorphic) monad structure. -/
lemma mapLens_bind (l : Lens P Q) {s : I} (x : IFreeM P X s)
    (g : ∀ u, X u → IFreeM P Y u) :
    (x.bind g).mapLens l = (x.mapLens l).bind (fun u y => (g u y).mapLens l) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | roll s a r ih =>
    simp only [bind_roll, mapLens_roll, bind_castPre]
    exact congrArg _ (funext fun d => congrArg (castPre _) (ih _))

/-- Transport along a lens commutes with the family map. -/
lemma mapLens_imap (l : Lens P Q) (f : ∀ u, X u → Y u) {s : I} (x : IFreeM P X s) :
    (x.imap f).mapLens l = (x.mapLens l).imap f := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | roll s a r ih =>
    simp only [imap_roll, mapLens_roll, imap_castPre]
    exact congrArg _ (funext fun d => congrArg (castPre _) (ih _))

end IFreeM

/-! ## Single-index specialization -/

namespace FreeM

variable {P : Endo.{uI, uA₁, uB₁} I} {Q : Endo.{uI, uA₂, uB₂} I} {R : Endo.{uI, uA₃, uB₃} I}
  {α β : Type v}

/-- Transport a single-index `FreeM` tree along a lens. -/
protected def mapLens (l : Lens P Q) {s : I} (x : FreeM P s α) : FreeM Q s α :=
  IFreeM.mapLens l x

@[simp]
lemma mapLens_pure (l : Lens P Q) (s : I) (x : α) :
    (FreeM.pure (P := P) s x).mapLens l = FreeM.pure s x := rfl

@[simp]
lemma mapLens_roll (l : Lens P Q) (s : I) (a : P.A s)
    (r : (b : P.B s a) → FreeM P (P.src s a b) α) :
    (FreeM.roll s a r).mapLens l =
      FreeM.roll s (l.toFunA s a) (fun d =>
        IFreeM.castPre (l.src_eq s a d) ((r (l.toFunB s a d)).mapLens l)) := rfl

@[simp]
lemma mapLens_id {s : I} (x : FreeM P s α) :
    x.mapLens (Lens.id P) = x :=
  IFreeM.mapLens_id x

@[simp]
lemma mapLens_comp (l : Lens Q R) (l' : Lens P Q) {s : I} (x : FreeM P s α) :
    (x.mapLens l').mapLens l = x.mapLens (Lens.comp l l') :=
  IFreeM.mapLens_comp l l' x

/-- Transport along a lens is a morphism of the state-polymorphic monad structure. -/
lemma mapLens_bind (l : Lens P Q) {s : I} (x : FreeM P s α)
    (g : (s' : I) → α → FreeM P s' β) :
    (x.bind g).mapLens l = (x.mapLens l).bind (fun s' y => (g s' y).mapLens l) :=
  IFreeM.mapLens_bind l x g

end FreeM

/-! ## Two-index specialization -/

namespace FreeM₂

variable {P : Endo.{uI, uA₁, uB₁} I} {Q : Endo.{uI, uA₂, uB₂} I} {R : Endo.{uI, uA₃, uB₃} I}
  {α β : Type v} {s t u : I}

/-- Transport a two-index `FreeM₂` tree along a lens. The post-state is untouched: the lens
acts on nodes only, and leaves carry their witnesses unchanged. -/
protected def mapLens (l : Lens P Q) {s t : I} (x : FreeM₂ P s t α) : FreeM₂ Q s t α :=
  IFreeM.mapLens l x

@[simp]
lemma mapLens_pure (l : Lens P Q) (x : α) :
    (FreeM₂.pure (P := P) (s := s) x).mapLens l = FreeM₂.pure x := rfl

@[simp]
lemma mapLens_pureCast (l : Lens P Q) (w : s = t) (x : α) :
    (pureCast (P := P) w x).mapLens l = pureCast w x := rfl

@[simp]
lemma mapLens_roll (l : Lens P Q) (a : P.A s)
    (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α) :
    (FreeM₂.roll a r).mapLens l =
      FreeM₂.roll (l.toFunA s a) (fun d =>
        castPre (l.src_eq s a d) ((r (l.toFunB s a d)).mapLens l)) := rfl

/-- Pre-state transports float out of `mapLens`. -/
@[simp]
lemma mapLens_castPre (l : Lens P Q) {s s' : I} (e : s = s') (x : FreeM₂ P s t α) :
    (castPre e x).mapLens l = castPre e (x.mapLens l) := by
  subst e; rfl

@[simp]
lemma mapLens_id (x : FreeM₂ P s t α) :
    x.mapLens (Lens.id P) = x :=
  IFreeM.mapLens_id x

@[simp]
lemma mapLens_comp (l : Lens Q R) (l' : Lens P Q) (x : FreeM₂ P s t α) :
    (x.mapLens l').mapLens l = x.mapLens (Lens.comp l l') :=
  IFreeM.mapLens_comp l l' x

/-- Transport along a lens is a morphism of the indexed monad structure. -/
lemma mapLens_bind (l : Lens P Q) (x : FreeM₂ P s t α) (g : α → FreeM₂ P t u β) :
    (x.bind g).mapLens l = (x.mapLens l).bind (fun a => (g a).mapLens l) := by
  refine (IFreeM.mapLens_bind l x _).trans ?_
  congr 1
  funext u' p
  obtain ⟨h, a⟩ := p
  subst h
  rfl

/-- Transport along a lens commutes with forgetting the post-state. -/
@[simp]
lemma toFreeM_mapLens (l : Lens P Q) (x : FreeM₂ P s t α) :
    (x.mapLens l).toFreeM = x.toFreeM.mapLens l :=
  (IFreeM.mapLens_imap l _ x).symm

end FreeM₂

end IPFunctor
