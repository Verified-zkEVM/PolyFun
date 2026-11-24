/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.StatefulExpectedCharge

/-!
# Stateful expected charge boundaries

A setup service spends one token on its first call. A poisonous state costs five at each call,
so its amortized certificate depends on preservation of the invariant. Two linked counters
exercise the order of the outer and inner private state.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.FreeM
open scoped ENNReal

namespace PolyFunTest.Probability.StatefulExpectedCharge

abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

private abbrev start : Fin 3 := 0
private abbrev ready : Fin 3 := 1
private abbrev poison : Fin 3 := 2

private def setupPrice (_ : Tick.A) (s : Fin 3) : ℝ≥0∞ :=
  if s = start then 1 else if s = ready then 0 else 5

private def credit (s : Fin 3) : ℝ≥0∞ := if s = start then 1 else 0

private noncomputable def setup : KernelHandler Tick (Fin 3) :=
  KernelHandler.ofFun (fun _ _ => ((), ready)) (fun _ => measurable_const)

/-- The excluded state violates the numerical premise. -/
example : ¬ setupPrice () poison ≤ credit poison := by
  norm_num [setupPrice, credit, poison, ready, start]

/-- The setup charge and retained credit are bounded for arbitrarily long finite clients. -/
example (x : FreeM Tick Unit) :
    wpFold (OpSpec.statefulExpectedCharge setup setupPrice) x (fun _ s => credit s) start ≤
      wpFold (OpSpec.statefulExpectedCharge setup (fun _ _ => 0)) x (fun _ _ => 0) start + 1 := by
  suffices hp : wpFold (OpSpec.statefulExpectedCharge setup setupPrice) x
      (fun _ s => 0 + credit s) start ≤
      wpFold (OpSpec.statefulExpectedCharge setup (fun _ _ => 0)) x (fun _ _ => 0) start +
        credit start by simpa [credit] using hp
  refine wpFold_statefulExpectedCharge_le_of_potential setup (fun _ _ => 0) setupPrice
    (fun s => s ≠ poison) credit Measurable.of_discrete ?_ ?_ x (fun _ _ => 0)
    (s := start) (by decide)
  · intro a s _
    simp [setup, KernelHandler.ofFun, Kernel.deterministic_apply, ready, poison]
  · intro a s hs
    fin_cases s <;> norm_num [start, ready, poison, setupPrice, credit, setup,
      KernelHandler.ofFun, Kernel.deterministic_apply] at *

/-- Charging a call with no answer keeps the charge and yields zero terminal mass. -/
private abbrev Stop : PFunctor.{0, 0} := ⟨Unit, fun _ => Empty⟩

example (q : Empty → Unit → ℝ≥0∞) :
    wpFold (OpSpec.statefulExpectedCharge (P := Stop) (S := Unit)
      (fun _ => 0) (fun _ _ => 3)) (FreeM.lift ()) q () = 3 := by
  simp

private def tick : FreeM Tick Unit := FreeM.lift ()

private def twice : Handler.Stateful (FreeM Tick) Nat Tick := fun _ => StateT.mk fun n => do
  let _ ← tick
  let _ ← tick
  pure ((), n + 1)

private def inner : Handler.Stateful (FreeM Tick) Nat Tick := fun _ => StateT.mk fun n => do
  let _ ← tick
  pure ((), n + 1)

private noncomputable def spec := OpSpec.expectedCharge (P := Tick) (fun _ => Measure.dirac ())
  (fun _ => 1)

/-- One outer call consumes two inner calls, advances each state at its own rate, and pays
twice. The observation weights the resulting counters differently. -/
example : wpFold spec ((twice.link inner).run tick (0, 3))
    (fun z => (10 * z.2.1 + z.2.2 : ℕ)) = 17 := by
  rw [Handler.Stateful.run_link, wpFold_map]
  simp only [tick, Handler.Stateful.run_lift, twice, StateT.run_mk, Handler.Stateful.run_bind,
    Handler.Stateful.run_pure, inner, wpFold_bind, wpFold_pure, wpFold_lift,
    spec, OpSpec.expectedCharge_apply]
  norm_num

/-- Linking prices an arbitrary client before observing the two terminal counters. -/
example (x : FreeM Tick Unit) (outerState innerState : Nat) (post : Unit → Nat → Nat → ℝ≥0∞) :
    wpFold spec ((twice.link inner).run x (outerState, innerState))
        (fun z => post z.1 z.2.1 z.2.2) =
      wpFold (OpSpec.statefulExpectedCharge
        (inner.toKernelHandler (fun _ => Measure.dirac ()) (fun _ => Measurable.of_discrete))
        (inner.expectedCharge (fun _ => Measure.dirac ()) (fun _ => 1)))
        (twice.run x outerState) (fun z => post z.1 z.2) innerState :=
  wpFold_expectedCharge_run_link (Q := Tick) (fun _ => Measure.dirac ()) (fun _ => 1) inner twice
    (fun _ => Measurable.of_discrete) (fun _ => Measurable.of_discrete) x post
    (fun _ _ => Measurable.of_discrete) outerState innerState

private abbrev Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

private noncomputable def fixedCoin (b : Bool) : KernelHandler Coin Unit :=
  KernelHandler.ofFun (fun _ _ => (b, ())) (fun _ => measurable_const)

/-- Infinite incurred cost gives both implementations the same scalar pre-expectation for every
postcost, although their terminal kernels disagree on the event of returning heads. -/
example :
    (∀ k : Bool → Unit → ℝ≥0∞,
      wpFold (OpSpec.statefulExpectedCharge (fixedCoin true) (fun _ _ => ⊤)) (FreeM.lift ()) k () =
        wpFold (OpSpec.statefulExpectedCharge (fixedCoin false) (fun _ _ => ⊤))
          (FreeM.lift ()) k ()) ∧
    runKernel (fixedCoin true) (FreeM.lift ()) () {(true, ())} ≠
      runKernel (fixedCoin false) (FreeM.lift ()) () {(true, ())} := by
  constructor
  · intro k
    simp
  · rw [runKernel_lift (fixedCoin true) () (), runKernel_lift (fixedCoin false) () ()]
    simp [fixedCoin, KernelHandler.ofFun, Kernel.deterministic_apply]

end PolyFunTest.Probability.StatefulExpectedCharge
