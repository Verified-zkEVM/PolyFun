/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Family
public import PolyFun.IPFunctor.Free.Reindex

/-!
# Ordinary binding signatures as constant parameter families

The two representations convert by polynomial reindexing. Both round trips are
identity, so clients of the ordinary scoped API can use the family machinery
without changing their syntax or trusting a new representation theorem.
-/

public section

universe u v w

namespace IPFunctor.ScopedSignature

variable {S : Type u}

/-- A binding signature with a single, unchanged parameter context. -/
@[expose, reducible] def asFamily (σ : ScopedSignature.{u, v, w} S) :
    ScopedFamily Unit (fun _ => S) where
  Op _ := σ.Op
  Arg := σ.Arg
  world _ _ := ()
  reindex _ _ := id
  binders := σ.binders
  sort := σ.sort

/-- Embed ordinary judgments into the constant family. -/
@[expose] def toFamilyReindexing (σ : ScopedSignature.{u, v, w} S) :
    Reindexing σ.polynomial σ.asFamily.polynomial (fun j => ⟨(), j⟩) where
  op _ o := o
  arg _ _ p := p
  source j o p := by
    change (⟨(), (σ.binders o p ++ j.1, σ.sort o p)⟩ :
      ScopedFamily.Judgment (fun _ : Unit => S)) =
      ⟨(), (σ.binders o p ++ j.1.map id, σ.sort o p)⟩
    rw [List.map_id]

/-- Forget the unique parameter context. -/
@[expose] def fromFamilyReindexing (σ : ScopedSignature.{u, v, w} S) :
    Reindexing σ.asFamily.polynomial σ.polynomial (fun j => j.2) where
  op _ o := o
  arg _ _ p := p
  source j o p := by
    change (σ.binders o p ++ j.2.1.map id, σ.sort o p) =
      (σ.binders o p ++ j.2.1, σ.sort o p)
    rw [List.map_id]

namespace Term

variable {σ : ScopedSignature.{u, v, w} S} {Γ : List S} {a : S}

/-- Use the context-changing API on an ordinary scoped description. -/
@[expose] def toFamily (t : σ.Term Γ a) : σ.asFamily.Term () Γ a :=
  t.reindex σ.toFamilyReindexing (fun _ x => x)

/-- Recover an ordinary scoped description from the constant family. -/
@[expose] def fromFamily (t : σ.asFamily.Term () Γ a) : σ.Term Γ a :=
  t.reindex (Y := fun j : Judgment S => ScopedVar j.1 j.2)
    σ.fromFamilyReindexing (fun _ x => x)

@[simp] theorem fromFamily_toFamily (t : σ.Term Γ a) : fromFamily t.toFamily = t := by
  rw [fromFamily, toFamily, IFreeM.reindex_comp]
  exact IFreeM.reindex_id t

@[simp] theorem toFamily_fromFamily (t : σ.asFamily.Term () Γ a) :
    (fromFamily t).toFamily = t := by
  rw [fromFamily, toFamily, IFreeM.reindex_comp]
  have h : σ.fromFamilyReindexing.comp σ.toFamilyReindexing =
      Reindexing.id σ.asFamily.polynomial := rfl
  rw [h]
  exact IFreeM.reindex_id t

end Term
end IPFunctor.ScopedSignature
