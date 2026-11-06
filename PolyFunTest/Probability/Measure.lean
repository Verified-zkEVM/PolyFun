/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunProbability.PFunctor.Free.Measure
public import PolyFunProbability.PFunctor.Free.Kernel
public import PolyFunProbability.PFunctor.Free.Path.Measure
public import PolyFunProbability.PFunctor.Free.Support

/-!
# Measure and kernel semantics of free programs

Regression tests for the measure fold, the kernel extension of a stateful kernel handler, and the
path measure, over a fair coin.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.FreeM

namespace PolyFunTest.Probability.FreeMeasure

/-- One operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A fair coin: uniform answers on the two-point type. -/
noncomputable instance : Coin.AnswerMeasure := AnswerMeasure.uniformOfFiniteNonempty Coin

/-- Two independent flips. -/
@[expose] def twoFlips : FreeM Coin (Bool × Bool) := do
  let x ← FreeM.lift (P := Coin) ()
  let y ← FreeM.lift (P := Coin) ()
  pure (x, y)

/-- A single flip denotes the uniform measure on its answers. -/
example : denote (FreeM.lift (P := Coin) ()) = uniformOn Set.univ := denote_lift (P := Coin) ()

/-- Every program over discrete answers is lossless. -/
example : IsProbabilityMeasure (denote twoFlips) := inferInstance

/-- Two independent flips denote the product of the two flip measures. -/
example :
    denote (FreeM.bind (FreeM.lift (P := Coin) ()) fun x =>
      FreeM.bind (FreeM.lift (P := Coin) ()) fun y => pure (x, y)) =
      (uniformOn Set.univ : Measure Bool).prod (uniformOn Set.univ) := by
  rw [denote_bind_bind_prod_mk_eq_prod (P := Coin), denote_lift (P := Coin)]
  rfl

/-- Mapping an output pushes the measure forward. -/
example : denote (FreeM.map Prod.fst twoFlips) = (denote twoFlips).map Prod.fst :=
  denote_map_of_discrete twoFlips Prod.fst

/-- A kernel handler that answers with a fair coin and counts the calls in its state. -/
noncomputable def countingCoin : KernelHandler Coin ℕ := fun _ =>
  Kernel.ofFunOfCountable fun n => (uniformOn Set.univ : Measure Bool).map fun b => (b, n + 1)

/-- The kernel extension runs a single call as that call's kernel. -/
example (n : ℕ) : runKernel countingCoin (FreeM.lift ()) n = countingCoin () n :=
  runKernel_lift countingCoin () n

/-- Each call of the counting handler is lossless, so the whole run is a subprobability kernel. -/
example (program : FreeM Coin Bool) [∀ a, IsSubprobabilityKernel (countingCoin a)] :
    IsSubprobabilityKernel (runKernel countingCoin program) := inferInstance

/-- A coin that never answers `false`: a Dirac answer measure. -/
noncomputable def biased : (a : Coin.A) → Measure (Coin.B a) := fun _ => Measure.dirac true

/-- Substitution is pullback: simulating each flip by two flips and keeping the second folds to
the source program under the two-flip measure. -/
example (program : FreeM Coin Bool) :
    measureFold (fun _ => (uniformOn Set.univ : Measure Bool))
        (program.liftM fun _ => FreeM.bind (FreeM.lift (P := Coin) ()) fun _ =>
          FreeM.lift (P := Coin) ()) =
      measureFold (fun _ => measureFold (fun _ => (uniformOn Set.univ : Measure Bool))
        (FreeM.bind (FreeM.lift (P := Coin) ()) fun _ => FreeM.lift (P := Coin) ())) program :=
  measureFold_liftM _ _ program

/-- Every result of positive mass is a possible output, even when the answer measure has gaps. -/
example (program : FreeM Coin Bool) (v : Bool) (h : measureFold biased program {v} ≠ 0) :
    v ∈ MonadAttach.support program :=
  mem_support_of_measureFold_singleton_ne_zero biased h

end PolyFunTest.Probability.FreeMeasure
