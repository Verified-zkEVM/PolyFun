/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.PatternRunsOnMatter.Operational

/-! # Operational regression tests for patterns running on matter -/

@[expose] public section

universe pA pB u v

namespace PFunctor.PatternRunsOperationalTest

/-- Handler execution keeps the pattern position/direction universes
independent of the square matter universe. -/
example {P : PFunctor.{pA, pB}} {Q : PFunctor.{u, u}}
    {m : Type (max pB u) → Type v} [Monad m]
    (handler : Handler m (P ⊗ Q)) (pattern : (FreeP P).A)
    (matter : (CofreeP Q).A) :
    m (FreeM.Path pattern × M.Vertex matter) :=
  FreeP.runWithHandler handler pattern matter

abbrev PatternP : PFunctor := ⟨Bool, fun _ => Bool⟩
abbrev MatterP : PFunctor := ⟨Nat, fun _ => Fin 3⟩

def pattern : (FreeP PatternP).A :=
  .liftBind false fun first =>
    .liftBind first fun _ => .pure PUnit.unit

def matter : (CofreeP MatterP).A :=
  M.corec (fun history : List (Fin 3) =>
    ⟨history.length, fun direction => direction :: history⟩) []

def deterministicHandler : Handler Id (PatternP ⊗ MatterP) :=
  fun _ => (true, 2)

/-- A concrete handler run pins the paired direction order and both levels of
the dependent pattern-path/matter-vertex result. -/
example : FreeP.runWithHandler deterministicHandler pattern matter =
    (⟨true, ⟨true, ⟨⟩⟩⟩,
      .child 2 (.child 2 (.root _))) := by
  rfl

def leafLabels : FreeM (PatternP ⊗ MatterP)
    (FreeM.Path pattern × M.Vertex matter) →
    List (List Bool × List (Fin 3))
  | .pure pulled => [(patternDirections pulled.1, matterDirections pulled.2)]
  | .liftBind _ next =>
      (List.finRange 3).flatMap fun qDirection =>
        [false, true].flatMap fun pDirection =>
          leafLabels (next (pDirection, qDirection))
where
  patternDirections : {tree : (FreeP PatternP).A} →
      FreeM.Path tree → List Bool
    | .pure _, _ => []
    | .liftBind _ _, ⟨direction, next⟩ =>
        direction :: patternDirections next
  matterDirections : {tree : (CofreeP MatterP).A} →
      M.Vertex tree → List (Fin 3)
    | _, .root _ => []
    | _, .child direction next => direction :: matterDirections next

/-- Decoded execution enumerates all `2² × 3²` synchronized paths. -/
example : (leafLabels (FreeP.runTree pattern matter)).length = 36 := by
  decide

/-- Grafting compatibility is exercised at a nontrivial depth-two outer tree
and a nonempty continuation. -/
example :
    FreeP.runTree
        (FreeM.append pattern (fun _ =>
          (.liftBind true fun _ => .pure PUnit.unit))) matter =
      FreeM.bind (FreeP.runTree pattern matter) (fun pulled =>
        FreeM.map
          (fun inner =>
            (FreeM.Path.append pattern
                (fun _ => (.liftBind true fun _ => .pure PUnit.unit))
                pulled.1 inner.1,
              M.Vertex.append pulled.2 inner.2))
          (FreeP.runTree
            (.liftBind true fun _ => .pure PUnit.unit)
            (M.Vertex.subtree pulled.2))) :=
  FreeP.runTree_append pattern _ matter

end PFunctor.PatternRunsOperationalTest
