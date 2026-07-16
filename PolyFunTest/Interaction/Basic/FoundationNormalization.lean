/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Chain
import PolyFun.Interaction.Basic.Telescope

/-!
# Polynomial normalization regression tests

Checks that interaction type trees, finite chains, and stopping trees expose the
canonical polynomial structures used by their implementations.
-/

namespace Interaction
namespace TypeTree

/-! ## Type trees are the free substitution monoid -/

example : TypeTree.stepPoly = PFunctor.FreeP TypeTree.basePFunctor := rfl

example : TypeTree.substMonoid.carrier = TypeTree.stepPoly := rfl

example (spec : TypeTree) (next : Path spec → TypeTree) :
    TypeTree.substMonoid.mult.toFunA ⟨spec, next⟩ = spec.append next :=
  rfl

example (spec : TypeTree) (next : Path spec → TypeTree)
    (tr : Path (spec.append next)) :
    TypeTree.substMonoid.mult.toFunB ⟨spec, next⟩ tr =
      PFunctor.FreeM.Path.split spec next tr :=
  rfl

/-! ## Chains are finite final-sequence approximants -/

example (n : Nat) : Chain (Nat.succ n) ≃ TypeTree.stepPoly.Obj (Chain n) :=
  Chain.succEquiv n

private abbrev Stage (i : Nat) := Fin (i + 1)

private def stageSpec (i : Nat) (_ : Stage i) : TypeTree :=
  .node (Fin (i + 1)) fun _ => .done

private def advance (i : Nat) (s : Stage i) (_ : Path (stageSpec i s)) :
    Stage (i + 1) :=
  s.castSucc

example (n i : Nat) (s : Stage i) :
    Chain.toTypeTree n (Chain.ofStateChain Stage stageSpec advance n i s) =
      TypeTree.stateChain Stage stageSpec advance n i s :=
  Chain.toTypeTree_ofStateChain Stage stageSpec advance n i s

/-! ## Telescopes have the indexed initial-algebra fold -/

private def stoppedRound (_ : PUnit) : TypeTree := .done

private def stoppedStep (s : PUnit) (_ : Path (stoppedRound s)) : PUnit :=
  PUnit.unit

private def twoLayers : Telescope stoppedRound stoppedStep PUnit.unit :=
  Telescope.extend PUnit.unit fun _ =>
    Telescope.extend PUnit.unit fun _ => Telescope.done PUnit.unit

private def heightAlg :
    PFunctor.FreeM.StoppingTree.Algebra
      (Obs := fun s => Path (stoppedRound s)) (step := stoppedStep)
      (fun _ => Nat) where
  done _ := 0
  extend _ cont := cont PUnit.unit + 1

private def height : {s : PUnit} → Telescope stoppedRound stoppedStep s → Nat :=
  PFunctor.FreeM.StoppingTree.fold heightAlg

example : height twoLayers = 2 := rfl

private def manualHeight :
    {s : PUnit} → Telescope stoppedRound stoppedStep s → Nat
  | _, .done _ => 0
  | _, .extend _ cont => manualHeight (cont PUnit.unit) + 1

example {s : PUnit} (tree : Telescope stoppedRound stoppedStep s) :
    manualHeight tree = height tree :=
  PFunctor.FreeM.StoppingTree.eq_fold heightAlg manualHeight
    (fun _ => rfl) (fun _ _ => rfl) tree

end TypeTree
end Interaction
