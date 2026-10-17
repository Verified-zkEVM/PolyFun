/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Basic
public import PolyFun.ITree.Basic
public import PolyFun.PFunctor.Bound
public import PolyFun.PFunctor.Dynamical.Responder.Reindex
public import PolyFun.PFunctor.Free.Support
public import PolyFun.PFunctor.Resumption

/-!
# Lift equations over concrete polynomial abbreviations

`Query := Bool y^ Nat` unfolds at reducible transparency, so simp rewrites the
direction type `Query.B query` to `Nat` before it consults its index. The generic
lift equations below carry `P.B a` as an implicit type argument of their left-hand
side and mark it `no_index`. Each example applies the equation to a concrete
interface and fails if that argument is indexed again. Results in `Type 1` keep
`FreeM.bind` from being rewritten to `>>=`, so the `bind` and `>>=` forms of an
equation are each exercised.
-/

public section

open PFunctor

namespace PolyFunTest.PFunctor.ConcreteSimp

abbrev Query : PFunctor.{0, 0} := Bool y^ Nat

/-! ## Support and bounds of free programs -/

example (query : Query.A) : MonadAttach.support (FreeM.lift query) = Set.univ := by
  simp

example {α : Type 1} (query : Query.A) (next : Nat → FreeM Query α) :
    MonadAttach.support ((FreeM.lift query).bind next) =
      ⋃ answer, MonadAttach.support (next answer) := by
  simp

example {α : Type 1} (query : Query.A) (next : Nat → FreeM Query α) (budget : Nat)
    (canRoll : Query.A → Nat → Prop) (cost : Query.A → Nat → Nat) :
    ((FreeM.lift query).bind next).IsRollBound budget canRoll cost ↔
      canRoll query budget ∧
        ∀ answer, (next answer).IsRollBound (cost query budget) canRoll cost := by
  simp

example (query : Query.A) (next : Nat → FreeM Query Nat) (budget : Nat)
    (canRoll : Query.A → Nat → Prop) (cost : Query.A → Nat → Nat) :
    (FreeM.lift query >>= next).IsRollBound budget canRoll cost ↔
      canRoll query budget ∧
        ∀ answer, (next answer).IsRollBound (cost query budget) canRoll cost := by
  simp

example {α : Type 1} (query : Query.A) (next : Nat → FreeM Query α) (budget : Nat) :
    ((FreeM.lift query).bind next).IsTotalRollBound budget ↔
      0 < budget ∧ ∀ answer, (next answer).IsTotalRollBound (budget - 1) := by
  simp

example (query : Query.A) (next : Nat → FreeM Query Nat) (budget : Nat) :
    (FreeM.lift query >>= next).IsTotalRollBound budget ↔
      0 < budget ∧ ∀ answer, (next answer).IsTotalRollBound (budget - 1) := by
  simp

example {α : Type 1} (query : Query.A) (next : Nat → FreeM Query α) :
    ((FreeM.lift query).bind next).ProgramProgress ↔
      Nonempty Nat ∧ ∀ answer, (next answer).ProgramProgress := by
  simp

/-! ## Responders, resumptions and interaction trees -/

example {State : Type} (responder : Responder State Query) (query : Query.A)
    (state : State) :
    responder.runFree (FreeM.lift query) state =
      (responder.answer state query, responder.next state query) := by
  simp

example (query : Query.A) :
    Resumption.dest (Resumption.lift (p := Query) query) =
      Sum.inr (.mk query Resumption.pure) := by
  simp

example (query : Query.A) : ITree.shape (ITree.lift (F := Query) query) = .query query := by
  simp

/-! ## Indexed free programs

The identity indexed polynomial `IPFunctor.X` is also an abbreviation, with directions
`PUnit`. Plain `simp` also reaches this goal through `bind_liftBind`, because the indexed
`FreeM.lift` is reducible, so the example names `bind_lift` alone. -/

example {I β : Type} (state : I)
    (next : (state' : I) → PUnit → IPFunctor.FreeM (IPFunctor.X.{0, 0, 0} (I := I)) state' β) :
    (IPFunctor.FreeM.lift state PUnit.unit).bind next =
      IPFunctor.FreeM.liftBind state PUnit.unit (fun answer => next state answer) := by
  simp only [IPFunctor.FreeM.bind_lift]

end PolyFunTest.PFunctor.ConcreteSimp
