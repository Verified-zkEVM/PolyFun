/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Free.QuotientRel

/-!
# Relations between free monads modulo equational theories

Examples for `QFreeRel`: the relational lifting of `Id` by the relation itself, related handlers
on the free monads and on the quotients, representative independence for theories without
equations, and identity extension.
-/

@[expose] public section

namespace PFunctorTest.QuotientRel

open PFunctor

/-- The relational lifting of `Id`: computations are related when their values are. -/
def idRelLift : RelLift Id Id where
  rel R a b := R (Id.run a) (Id.run b)
  rel_pure h := h
  rel_bind h hf := hf _ _ h

/-- One operation with Boolean answers. -/
def boolSig : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- The theory without equations over `boolSig`. -/
def emptyTheory : EqTheory.{0, 0, 0} boolSig where
  Eqn := Empty
  ctx _ := PUnit
  lhs e := e.elim
  rhs e := e.elim

instance : IsEmpty emptyTheory.Eqn := inferInstanceAs (IsEmpty Empty)

/-- The identity signature relation on `boolSig`. -/
def idSigRel : SigRel boolSig boolSig where
  pos a a' := a = a'
  dir _ _ d d' := HEq d d'

/-- `idSigRel` is an identity signature relation. -/
theorem idSigRel_isId : idSigRel.IsId where
  pos_iff _ _ := Iff.rfl
  dir_iff _ _ _ := heq_iff_eq

/-- The handler answering `b`. -/
def answer (b : Bool) : (a : boolSig.A) → Id (boolSig.B a) := fun _ => pure b

/-- Every handler validates the theory without equations. -/
theorem answer_validates (b : Bool) : emptyTheory.Validates (answer b) :=
  fun e => e.elim

/-- The handler answering `b` is related to itself along `idSigRel`. -/
theorem answer_rel (b : Bool) :
    ∀ a a', idSigRel.pos a a' → idRelLift.rel (idSigRel.dir a a') (answer b a) (answer b a') := by
  rintro a a' rfl
  exact HEq.rfl

example {x y : boolSig.FreeM Bool} (hxy : HFreeRel idSigRel (· = ·) x y) :
    Id.run (x.liftM (answer true)) = Id.run (y.liftM (answer true)) :=
  hxy.liftM_rel idRelLift (answer_rel true)

example {q₁ q₂ : QFreeM emptyTheory Bool}
    (hq : QFreeRel idSigRel emptyTheory emptyTheory (· = ·) q₁ q₂) :
    Id.run (QFreeM.lift (answer false) (answer_validates false) q₁) =
      Id.run (QFreeM.lift (answer false) (answer_validates false) q₂) :=
  QFreeRel.lift_rel idRelLift (answer_validates false) (answer_validates false) (answer_rel false)
    hq

example {x y : boolSig.FreeM Bool} :
    QFreeRel idSigRel emptyTheory emptyTheory (· = ·) (QFreeM.mk x) (QFreeM.mk y) ↔
      ∃ y', emptyTheory.Cong y y' ∧ HFreeRel idSigRel (· = ·) x y' :=
  QFreeRel.mk_iff_left (SigRel.compat_of_isEmpty _ _ _)

example {x y : boolSig.FreeM Bool} :
    QFreeRel idSigRel emptyTheory emptyTheory (· = ·) (QFreeM.mk x) (QFreeM.mk y) ↔
      ∃ x', emptyTheory.Cong x x' ∧ HFreeRel idSigRel (· = ·) x' y :=
  QFreeRel.mk_iff_right (SigRel.compat_of_isEmpty _ _ _)

example {q q' : QFreeM emptyTheory Bool} :
    QFreeRel idSigRel emptyTheory emptyTheory (· = ·) q q' ↔ q = q' :=
  QFreeRel.eq_iff idSigRel_isId

example : QFreeRel idSigRel emptyTheory emptyTheory (idSigRel.dir () ())
    (QFreeM.op ()) (QFreeM.op ()) :=
  QFreeRel.op rfl

example {x x' : boolSig.FreeM Bool} : emptyTheory.Cong x x' ↔ x = x' :=
  emptyTheory.cong_iff_eq_of_isEmpty

end PFunctorTest.QuotientRel

end
