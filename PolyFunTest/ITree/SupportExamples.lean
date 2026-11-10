/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.WP.Support

/-! # Possible outputs of interaction trees

Each example pins one behaviour of `ITree.CanReturn` and its readings:
* a coin flip can return either of its values and nothing else;
* demonic partial correctness of the flip is the always judgment over both values;
* silent divergence returns nothing, so it satisfies every always judgment and no sometimes
  judgment. It is partially but not totally correct, so the always judgment matches partial
  correctness only;
* total angelic correctness needs a returning run;
* the generic support lemmas over `ExactMonadAttach` apply to interaction trees.
-/

@[expose] public section

namespace PolyFunTest.ITreeSupportExamples

open PFunctor MonadAttach

/-- One operation, a coin flip answered by a Boolean. -/
@[reducible] def CoinE : PFunctor.{0, 0} where
  A := PUnit
  B _ := Bool

/-- Flip a coin and return `1` on heads and `0` on tails. -/
def flipNat : ITree CoinE Nat :=
  ITree.query PUnit.unit fun b => ITree.pure (if b then 1 else 0)

example : ITree.CanReturn flipNat 0 :=
  ITree.CanReturn.of_query false (by simp)

example : ITree.CanReturn flipNat 1 :=
  ITree.CanReturn.of_query true (by simp)

/-- The flip returns nothing else. Admitting every value as an output breaks this. -/
example : ¬ ITree.CanReturn flipNat 2 := by
  simp [flipNat]

/-- Demonic partial correctness of the flip is the always judgment over both values. -/
example : ITree.wpPartial (OpSpec.demonic CoinE) flipNat (· ≤ 1) := by
  refine ITree.wpPartial_demonic_iff_allOutputs.mpr fun r hr => ?_
  obtain ⟨b, hb⟩ := ITree.canReturn_query_iff.mp hr
  rw [ITree.canReturn_pure_iff] at hb
  subst hb
  cases b <;> decide

/-- Silent divergence returns nothing, so it satisfies every always judgment. -/
example : AllOutputs (fun _ => False) (ITree.diverge : ITree CoinE Nat) :=
  fun r hr => ITree.not_canReturn_diverge r hr

/-- Silent divergence satisfies no sometimes judgment. -/
example : ¬ SomeOutput (fun _ => True) (ITree.diverge : ITree CoinE Nat) :=
  fun ⟨r, hr, _⟩ => ITree.not_canReturn_diverge r hr

/-- Silent divergence is partially correct for every postcondition, matching the always
judgment. -/
example : ITree.wpPartial (OpSpec.demonic CoinE) (ITree.diverge : ITree CoinE Nat)
    (fun _ => False) :=
  ITree.wpPartial_demonic_iff_allOutputs.mpr fun r hr => ITree.not_canReturn_diverge r hr

/-- Silent divergence is not totally correct, although it satisfies the always judgment. -/
example : ¬ ITree.wpTotal (OpSpec.demonic CoinE) (ITree.diverge : ITree CoinE Nat)
    (fun _ => False) := by
  simp

/-- Total angelic correctness needs a returning run: the flip has one that returns `1`. -/
example : ITree.wpTotal (OpSpec.angelic CoinE) flipNat (· = 1) :=
  ITree.wpTotal_angelic_iff_someOutput.mpr ⟨1, ITree.CanReturn.of_query true (by simp), rfl⟩

/-- Silent divergence has no returning run, so it is not totally angelically correct. -/
example : ¬ ITree.wpTotal (OpSpec.angelic CoinE) (ITree.diverge : ITree CoinE Nat)
    (fun _ => True) := by
  simp

/-- The generic support lemmas over `ExactMonadAttach` apply to interaction trees. -/
example (p : Nat → Prop) (r : Nat) : SomeOutput p (Pure.pure r : ITree CoinE Nat) ↔ p r :=
  someOutput_pure p r

example (p : Nat → Prop) (x : ITree CoinE Nat) (f : Nat → ITree CoinE Nat) :
    AllOutputs p (x >>= f) ↔ ∀ a ∈ support x, AllOutputs p (f a) :=
  allOutputs_bind p x f

end PolyFunTest.ITreeSupportExamples
