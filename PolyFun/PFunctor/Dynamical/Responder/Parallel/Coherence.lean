/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Free.Parallel
public import PolyFun.PFunctor.Dynamical.Responder.Lens
public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Behavior

/-!
# Structural coherence of state-free parallel responder behavior

The structural parallel-sum lenses witness symmetry, both units, and
associativity of ordinary lockstep state-free behavior. The proofs factor
through explicit responder state maps so their scheduling content is visible
rather than hidden behind raw coinductive equality.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uB uC₁ uD₁ uC₂ uD₂ uC₃ uD₃

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}

/-- The empty state-free responder behavior. -/
def zeroBehavior :
    PFunctor.M ((0 : PFunctor.{uA₁, uB}) ⊸ X.{uA₁, uB}) :=
  (Responder.zero : Responder PUnit.{1} (0 : PFunctor.{uA₁, uB})).behavior
    PUnit.unit

/-- Parallel behavior is symmetric after reindexing by the interface
braiding. -/
theorem mapBehavior_parallel_comm
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) :
    mapBehavior (PFunctor.Lens.parallelSumComm P Q)
        (parallelBehavior right left) =
      parallelBehavior left right := by
  let swapped := Responder.parallel (Responder.terminal (P := Q))
    (Responder.terminal (P := P))
  let normal := Responder.parallel (Responder.terminal (P := P))
    (Responder.terminal (P := Q))
  let mapped := Responder.reindex
    (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q)) swapped
  have hBehavior : mapped.behavior (right, left) =
      normal.behavior (left, right) := by
    apply behavior_eq_of_responderMap mapped normal Prod.swap _ _ (left, right)
    · intro state operation
      rw [Responder.answer_reindex, runFree_ofLens]
      cases operation <;> rfl
    · intro state operation
      rw [Responder.next_reindex, runFree_ofLens]
      exact parallel_next_comm (Responder.terminal (P := P))
        (Responder.terminal (P := Q)) state operation
  calc
    mapBehavior (PFunctor.Lens.parallelSumComm P Q)
        (parallelBehavior right left) = mapped.behavior (right, left) :=
      reindexBehavior_behavior
        (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q))
        swapped (right, left)
    _ = normal.behavior (left, right) := hBehavior
    _ = parallelBehavior left right := rfl

/-- The right zero interface is a unit for state-free parallel behavior after
reindexing by the structural unitor. -/
theorem mapBehavior_parallel_zero_right
    (left : PFunctor.M (P ⊸ X.{uA₁, uB})) :
    mapBehavior
        (PFunctor.Lens.parallelSumZero P :
          PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P)
        left =
      parallelBehavior left
        (zeroBehavior : PFunctor.M
          ((0 : PFunctor.{uA₂, uB}) ⊸ X.{uA₂, uB})) := by
  let base := Responder.terminal (P := P)
  let empty := (Responder.zero :
    Responder PUnit.{1} (0 : PFunctor.{uA₂, uB}))
  let parallel := Responder.parallel base empty
  let mapped := Responder.reindex
    (PFunctor.Handler.ofLens
      (PFunctor.Lens.parallelSumZero P :
        PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P)) base
  have hBehavior : mapped.behavior left =
      parallel.behavior
        (left, PUnit.unit) := by
    apply behavior_eq_of_responderMap mapped parallel Prod.fst _ _
      (left, PUnit.unit)
    · intro state operation
      rw [Responder.answer_reindex, runFree_ofLens]
      cases operation with
      | left operation => rfl
      | right impossible => exact PEmpty.elim impossible
      | both operation impossible => exact PEmpty.elim impossible
    · intro state operation
      rw [Responder.next_reindex, runFree_ofLens]
      cases operation with
      | left operation => rfl
      | right impossible => exact PEmpty.elim impossible
      | both operation impossible => exact PEmpty.elim impossible
  let terminalParallel := Responder.parallel base
    (Responder.terminal (P := (0 : PFunctor.{uA₂, uB})))
  have hPresentation : parallel.behavior (left, PUnit.unit) =
      terminalParallel.behavior (left, empty.behavior PUnit.unit) := by
    apply behavior_eq_of_responderMap parallel terminalParallel
      (fun state => (state.1, PUnit.unit)) _ _
      (left, empty.behavior PUnit.unit)
    · intro state operation
      cases operation with
      | left operation => rfl
      | right impossible => exact PEmpty.elim impossible
      | both operation impossible => exact PEmpty.elim impossible
    · intro state operation
      cases operation with
      | left operation => rfl
      | right impossible => exact PEmpty.elim impossible
      | both operation impossible => exact PEmpty.elim impossible
  calc
    mapBehavior
        (PFunctor.Lens.parallelSumZero P :
          PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P) left =
      mapBehavior
        (PFunctor.Lens.parallelSumZero P :
          PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P)
        (base.behavior left) := by rw [terminal_behavior]
    _ = mapped.behavior left :=
        reindexBehavior_behavior
          (PFunctor.Handler.ofLens
            (PFunctor.Lens.parallelSumZero P :
              PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
          base left
    _ = parallel.behavior
        (left, PUnit.unit) := hBehavior
    _ = terminalParallel.behavior (left, empty.behavior PUnit.unit) :=
      hPresentation
    _ = parallelBehavior left
        (zeroBehavior : PFunctor.M
          ((0 : PFunctor.{uA₂, uB}) ⊸ X.{uA₂, uB})) := rfl

/-- The left zero interface is a unit for state-free parallel behavior after
reindexing by the structural unitor. -/
theorem mapBehavior_parallel_zero_left
    (right : PFunctor.M (P ⊸ X.{uA₁, uB})) :
    mapBehavior
        (PFunctor.Lens.zeroParallelSum P :
          PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P)
        right =
      parallelBehavior
        (zeroBehavior : PFunctor.M
          ((0 : PFunctor.{uA₂, uB}) ⊸ X.{uA₂, uB})) right := by
  let base := Responder.terminal (P := P)
  let empty := (Responder.zero :
    Responder PUnit.{1} (0 : PFunctor.{uA₂, uB}))
  let parallel := Responder.parallel empty base
  let mapped := Responder.reindex
    (PFunctor.Handler.ofLens
      (PFunctor.Lens.zeroParallelSum P :
        PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P)) base
  have hBehavior : mapped.behavior right =
      parallel.behavior (PUnit.unit, right) := by
    apply behavior_eq_of_responderMap mapped parallel Prod.snd _ _
      (PUnit.unit, right)
    · intro state operation
      rw [Responder.answer_reindex, runFree_ofLens]
      cases operation with
      | left impossible => exact PEmpty.elim impossible
      | right operation => rfl
      | both impossible operation => exact PEmpty.elim impossible
    · intro state operation
      rw [Responder.next_reindex, runFree_ofLens]
      cases operation with
      | left impossible => exact PEmpty.elim impossible
      | right operation => rfl
      | both impossible operation => exact PEmpty.elim impossible
  let terminalParallel := Responder.parallel
    (Responder.terminal (P := (0 : PFunctor.{uA₂, uB}))) base
  have hPresentation : parallel.behavior (PUnit.unit, right) =
      terminalParallel.behavior (empty.behavior PUnit.unit, right) := by
    apply behavior_eq_of_responderMap parallel terminalParallel
      (fun state => (PUnit.unit, state.2)) _ _
      (empty.behavior PUnit.unit, right)
    · intro state operation
      cases operation with
      | left impossible => exact PEmpty.elim impossible
      | right operation => rfl
      | both impossible operation => exact PEmpty.elim impossible
    · intro state operation
      cases operation with
      | left impossible => exact PEmpty.elim impossible
      | right operation => rfl
      | both impossible operation => exact PEmpty.elim impossible
  calc
    mapBehavior
        (PFunctor.Lens.zeroParallelSum P :
          PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P) right =
      mapBehavior
        (PFunctor.Lens.zeroParallelSum P :
          PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P)
        (base.behavior right) := by rw [terminal_behavior]
    _ = mapped.behavior right :=
      reindexBehavior_behavior
        (PFunctor.Handler.ofLens
          (PFunctor.Lens.zeroParallelSum P :
            PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
        base right
    _ = parallel.behavior (PUnit.unit, right) := hBehavior
    _ = terminalParallel.behavior (empty.behavior PUnit.unit, right) :=
      hPresentation
    _ = parallelBehavior
        (zeroBehavior : PFunctor.M
          ((0 : PFunctor.{uA₂, uB}) ⊸ X.{uA₂, uB})) right := rfl

/-- Parallel state-free behavior associates after reindexing by the interface
associator. -/
theorem mapBehavior_parallel_assoc
    {R : PFunctor.{uA₃, uB}}
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (middle : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (right : PFunctor.M (R ⊸ X.{uA₃, uB})) :
    mapBehavior (PFunctor.Lens.parallelSumAssoc P Q R)
        (parallelBehavior left (parallelBehavior middle right)) =
      parallelBehavior (parallelBehavior left middle) right := by
  let pResponder := Responder.terminal (P := P)
  let qResponder := Responder.terminal (P := Q)
  let rResponder := Responder.terminal (P := R)
  let rightAssociated := Responder.parallel pResponder
    (Responder.parallel qResponder rResponder)
  let leftAssociated := Responder.parallel
    (Responder.parallel pResponder qResponder) rResponder
  let mapped := Responder.reindex
    (PFunctor.Handler.ofLens
      (PFunctor.Lens.parallelSumAssoc P Q R)) rightAssociated
  let reassocState :
      ((PFunctor.M (P ⊸ X.{uA₁, uB}) ×
          PFunctor.M (Q ⊸ X.{uA₂, uB})) ×
        PFunctor.M (R ⊸ X.{uA₃, uB})) →
      (PFunctor.M (P ⊸ X.{uA₁, uB}) ×
        (PFunctor.M (Q ⊸ X.{uA₂, uB}) ×
          PFunctor.M (R ⊸ X.{uA₃, uB}))) :=
    fun state => (state.1.1, (state.1.2, state.2))
  have hBehavior :
      mapped.behavior (reassocState ((left, middle), right)) =
        leftAssociated.behavior ((left, middle), right) := by
    apply behavior_eq_of_responderMap mapped leftAssociated reassocState _ _
      ((left, middle), right)
    · intro state operation
      rw [Responder.answer_reindex, runFree_ofLens]
      cases operation with
      | left operation => cases operation <;> rfl
      | right operation => rfl
      | both operation rightOperation => cases operation <;> rfl
    · intro state operation
      rw [Responder.next_reindex, runFree_ofLens]
      cases operation with
      | left operation => cases operation <;> rfl
      | right operation => rfl
      | both operation rightOperation => cases operation <;> rfl
  let rightPresentation := Responder.parallel pResponder
    (Responder.terminal (P := Q ∥ R))
  have hRightPresentation :
      rightPresentation.behavior
          (left, parallelBehavior middle right) =
        rightAssociated.behavior (left, (middle, right)) := by
    apply behavior_eq_of_responderMap rightPresentation rightAssociated
      (fun state => (state.1, parallelBehavior state.2.1 state.2.2)) _ _
      (left, (middle, right))
    · intro state operation
      dsimp [rightPresentation, rightAssociated, pResponder,
        qResponder, rResponder]
      cases operation <;> simp [parallelBehavior]
    · intro state operation
      dsimp [rightPresentation, rightAssociated, pResponder,
        qResponder, rResponder]
      cases operation <;> simp [parallelBehavior]
  let leftPresentation := Responder.parallel
    (Responder.terminal (P := P ∥ Q)) rResponder
  have hLeftPresentation :
      leftPresentation.behavior
          (parallelBehavior left middle, right) =
        leftAssociated.behavior ((left, middle), right) := by
    apply behavior_eq_of_responderMap leftPresentation leftAssociated
      (fun state => (parallelBehavior state.1.1 state.1.2, state.2)) _ _
      ((left, middle), right)
    · intro state operation
      dsimp [leftPresentation, leftAssociated, pResponder,
        qResponder, rResponder]
      cases operation <;> simp [parallelBehavior]
    · intro state operation
      dsimp [leftPresentation, leftAssociated, pResponder,
        qResponder, rResponder]
      cases operation <;> simp [parallelBehavior]
  calc
    mapBehavior (PFunctor.Lens.parallelSumAssoc P Q R)
        (parallelBehavior left (parallelBehavior middle right)) =
      mapBehavior (PFunctor.Lens.parallelSumAssoc P Q R)
        (rightAssociated.behavior (left, (middle, right))) := by
          exact congrArg (mapBehavior
            (PFunctor.Lens.parallelSumAssoc P Q R)) hRightPresentation
    _ =
      mapped.behavior (reassocState ((left, middle), right)) :=
        reindexBehavior_behavior
          (PFunctor.Handler.ofLens
            (PFunctor.Lens.parallelSumAssoc P Q R))
          rightAssociated (reassocState ((left, middle), right))
    _ = leftAssociated.behavior ((left, middle), right) := hBehavior
    _ = leftPresentation.behavior
        (parallelBehavior left middle, right) := hLeftPresentation.symm
    _ = parallelBehavior (parallelBehavior left middle) right := rfl

end Responder
end PFunctor
