/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Chain
import PolyFun.Interaction.Basic.Telescope

/-!
# Polynomial normalization regression tests

Checks that interaction specs, finite chains, and stopping trees expose the
canonical polynomial structures used by their implementations.
-/

namespace Interaction
namespace Spec

/-! ## Specs are the free substitution monoid -/

example : Spec.stepPoly = PFunctor.FreeP Spec.basePFunctor := rfl

example : Spec.substMonoid.carrier = Spec.stepPoly := rfl

example (spec : Spec) (next : Transcript spec → Spec) :
    Spec.substMonoid.mult.toFunA ⟨spec, next⟩ = spec.append next :=
  rfl

example (spec : Spec) (next : Transcript spec → Spec)
    (tr : Transcript (spec.append next)) :
    Spec.substMonoid.mult.toFunB ⟨spec, next⟩ tr =
      PFunctor.FreeM.Path.split spec next tr :=
  rfl

/-! ## Chains are finite final-sequence approximants -/

example (n : Nat) : Chain (Nat.succ n) ≃ Spec.stepPoly.Obj (Chain n) :=
  Chain.succEquiv n

private abbrev Stage (i : Nat) := Fin (i + 1)

private def stageSpec (i : Nat) (_ : Stage i) : Spec :=
  .node (Fin (i + 1)) fun _ => .done

private def advance (i : Nat) (s : Stage i) (_ : Transcript (stageSpec i s)) :
    Stage (i + 1) :=
  s.castSucc

example (n i : Nat) (s : Stage i) :
    Chain.toSpec n (Chain.ofStateChain Stage stageSpec advance n i s) =
      Spec.stateChain Stage stageSpec advance n i s :=
  Chain.toSpec_ofStateChain Stage stageSpec advance n i s

/-! ## Telescopes have the indexed initial-algebra fold -/

private def stoppedRound (_ : PUnit) : Spec := .done

private def stoppedStep (s : PUnit) (_ : Transcript (stoppedRound s)) : PUnit :=
  PUnit.unit

private def twoLayers : Telescope stoppedRound stoppedStep PUnit.unit :=
  Telescope.extend PUnit.unit fun _ =>
    Telescope.extend PUnit.unit fun _ => Telescope.done PUnit.unit

private def heightAlg :
    PFunctor.FreeM.StoppingTree.Algebra
      (Obs := fun s => Transcript (stoppedRound s)) (step := stoppedStep)
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

end Spec
end Interaction
