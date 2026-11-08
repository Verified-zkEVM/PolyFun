/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

-- Product transports recurse through the existing append families.
import all PolyFun.PFunctor.Free.Path
public import PolyFun.PFunctor.Free.Path

/-!
# Runtime append payloads

Product transports preserve separate output families across a projection-indexed append.
The identity projection theorem identifies runtime and shape paths at the identity lens.
-/

public section

universe uA uB uA₂ uB₂ v t w

namespace PFunctor.FreeM
variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {α : Type v}

/-- Projecting an identity-lens path preserves every branch choice. -/
@[simp] theorem projectPathAlong_id : (s : FreeM P α) → (tr : PathAlong (Lens.id P) s) →
    projectPathAlong (Lens.id P) s tr = tr
  | .pure _, ⟨⟩ => rfl
  | .liftBind _ rest, ⟨x, tr⟩ =>
    congrArg (Sigma.mk x) (projectPathAlong_id (rest x) tr)

-- Projection indices must reduce when descending to a source branch.
attribute [local implicit_reducible] Displayed.LocalMap.toHom
  Displayed.LocalMap.toHomFun projectPathAlongLocalMap projectPathAlong

namespace PathAlong
/-- Split a lifted product into separately lifted output payloads. -/
@[expose] def liftAppendProd {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path : PathAlong l (FreeM.append s₁ s₂)) →
    LiftAppend l s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path →
      LiftAppend l s₁ s₂ A path × LiftAppend l s₁ s₂ B path
  | .pure _, _, _, _, _, x => x
  | .liftBind a rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProd l (rest (l.toFunB a b))
        (fun path₁ => s₂ ⟨l.toFunB a b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

/-- Combine separately lifted output payloads into a lifted product. -/
@[expose] def liftAppendProdMk {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path : PathAlong l (FreeM.append s₁ s₂)) →
    LiftAppend l s₁ s₂ A path × LiftAppend l s₁ s₂ B path →
      LiftAppend l s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path
  | .pure _, _, _, _, _, x => x
  | .liftBind a rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProdMk l (rest (l.toFunB a b))
        (fun path₁ => s₂ ⟨l.toFunB a b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

/-- Combining the components of a lifted product recovers its payload. -/
@[simp]
theorem liftAppendProdMk_liftAppendProd {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path : PathAlong l (FreeM.append s₁ s₂)) →
    (x : LiftAppend l s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path) →
      liftAppendProdMk l s₁ s₂ A B path (liftAppendProd l s₁ s₂ A B path x) = x
  | .pure _, _, _, _, _, _ => rfl
  | .liftBind a rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProdMk_liftAppendProd l (rest (l.toFunB a b))
        (fun path₁ => s₂ ⟨l.toFunB a b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

/-- Splitting a combined product recovers both lifted payloads. -/
@[simp]
theorem liftAppendProd_liftAppendProdMk {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path : PathAlong l (FreeM.append s₁ s₂)) →
    (x : LiftAppend l s₁ s₂ A path × LiftAppend l s₁ s₂ B path) →
      liftAppendProd l s₁ s₂ A B path (liftAppendProdMk l s₁ s₂ A B path x) = x
  | .pure _, _, _, _, _, _ => rfl
  | .liftBind a rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProd_liftAppendProdMk l (rest (l.toFunB a b))
        (fun path₁ => s₂ ⟨l.toFunB a b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

/-- Splitting a packed product packs each component separately. -/
@[simp]
theorem liftAppendProd_packAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) → (x : A path₁ path₂ × B path₁ path₂) →
      liftAppendProd l s₁ s₂ A B (append l s₁ s₂ path₁ path₂)
        (packAppend l s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path₁ path₂ x) =
          (packAppend l s₁ s₂ A path₁ path₂ x.1, packAppend l s₁ s₂ B path₁ path₂ x.2)
  | .pure _, _, _, _, ⟨⟩, _, _ => rfl
  | .liftBind a rest, s₂, A, B, ⟨b, path₁⟩, path₂, x =>
      liftAppendProd_packAppend l (rest (l.toFunB a b)) (fun path => s₂ ⟨l.toFunB a b, path⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path₁ path₂ x


/-- Appending an empty runtime prefix returns the suffix transcript. -/
@[simp] theorem append_pure {β : Type t} (l : Lens P Q) (a : α)
    (s₂ : Path (Pure.pure (f := FreeM P) a) → FreeM P β)
    (tr : PathAlong l (s₂ ⟨⟩)) : append l (Pure.pure (f := FreeM P) a) s₂ ⟨⟩ tr = tr := rfl

/-- Runtime append preserves the first move and descends through its selected source branch. -/
theorem append_liftBind {β : Type t} (l : Lens P Q) (a : P.A)
    (rest : P.B a → FreeM P α) (s₂ : Path (.liftBind a rest) → FreeM P β)
    (x : Q.B (l.toFunA a)) (tr : PathAlong l (rest (l.toFunB a x)))
    (tail : PathAlong l (s₂ (projectPathAlong l (.liftBind a rest) ⟨x, tr⟩))) :
    append l (.liftBind a rest) s₂ ⟨x, tr⟩ tail =
      ⟨x, append l (rest (l.toFunB a x)) (fun t => s₂ ⟨l.toFunB a x, t⟩) tr tail⟩ := rfl

/-- Splitting at an empty prefix retains the complete suffix transcript. -/
@[simp] theorem split_pure {β : Type t} (l : Lens P Q) (a : α)
    (s₂ : Path (Pure.pure (f := FreeM P) a) → FreeM P β)
    (tr : PathAlong l (s₂ ⟨⟩)) : split l (Pure.pure (f := FreeM P) a) s₂ tr = ⟨⟨⟩, tr⟩ := rfl

/-- Splitting a node transcript preserves its first runtime move. -/
theorem split_liftBind {β : Type t} (l : Lens P Q) (a : P.A)
    (rest : P.B a → FreeM P α) (s₂ : Path (.liftBind a rest) → FreeM P β)
    (x : Q.B (l.toFunA a))
    (tr : PathAlong l ((rest (l.toFunB a x)).append
      (fun t => s₂ ⟨l.toFunB a x, t⟩))) :
    split l (.liftBind a rest) s₂ ⟨x, tr⟩ =
      let v := split l (rest (l.toFunB a x)) (fun t => s₂ ⟨l.toFunB a x, t⟩) tr
      ⟨⟨x, v.1⟩, v.2⟩ := rfl

/-- Packing at an empty prefix preserves the suffix payload. -/
@[simp] theorem packAppend_pure {β : Type t} (l : Lens P Q) (a : α)
    (s₂ : Path (Pure.pure (f := FreeM P) a) → FreeM P β)
    (F : (tr : PathAlong l (Pure.pure (f := FreeM P) a)) →
      PathAlong l (s₂ (projectPathAlong l (Pure.pure (f := FreeM P) a) tr)) → Type w)
    (tr : PathAlong l (s₂ ⟨⟩)) (x : F ⟨⟩ tr) :
    packAppend l (Pure.pure (f := FreeM P) a) s₂ F ⟨⟩ tr x = x := rfl

/-- Packing a node payload descends through the runtime-selected branch. -/
theorem packAppend_liftBind {β : Type t} (l : Lens P Q) (a : P.A)
    (rest : P.B a → FreeM P α) (s₂ : Path (.liftBind a rest) → FreeM P β)
    (F : (tr : PathAlong l (.liftBind a rest)) →
      PathAlong l (s₂ (projectPathAlong l (.liftBind a rest) tr)) → Type w)
    (x : Q.B (l.toFunA a)) (tr : PathAlong l (rest (l.toFunB a x)))
    (tail : PathAlong l (s₂ (projectPathAlong l (.liftBind a rest) ⟨x, tr⟩)))
    (value : F ⟨x, tr⟩ tail) :
    packAppend l (.liftBind a rest) s₂ F ⟨x, tr⟩ tail value =
      packAppend l (rest (l.toFunB a x)) (fun t => s₂ ⟨l.toFunB a x, t⟩)
        (fun t => F ⟨x, t⟩) tr tail value := rfl

end PathAlong
end PFunctor.FreeM
