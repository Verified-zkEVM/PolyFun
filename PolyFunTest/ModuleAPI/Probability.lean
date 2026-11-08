/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Deterministic
public import PolyFun.Control.Monad.Measure.SemanticsVia
public import PolyFun.PFunctor.Free.Measure.EvalDist
public import PolyFun.PFunctor.Free.Measure.Kernel
public import PolyFun.PFunctor.Free.Measure

/-!
# Ordinary-import canaries for measure semantics

VCVio's downstream proofs unfold the measure fold by definitional equality, and use the kernel
extension through its step equations. These examples check, through ordinary imports, that
`PFunctor.FreeM.denote` of a returned value holds by `rfl`, and that the step equation of
`PFunctor.FreeM.runKernel`, whose body is private, is available as a lemma. They also check that
`evalDist` unfolds to the denotation of the deterministic and free-program instances by `rfl`,
and that `prFail` unfolds to the defect of the output measure. The `OptionT` and `ExceptT`
semantics unfold to pullbacks of the run measure, and the bundled semantics of an instance unfolds
to its `evalDist`.
-/

@[expose] public section

universe u uA uS uR

namespace PolyFunTest.ModuleAPI.Probability

open _root_.PFunctor MeasureTheory ProbabilityTheory

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] {α : Type uR} [MeasurableSpace α]

example [P.AnswerMeasure] (x : α) : FreeM.denote (pure x : FreeM P α) = Measure.dirac x := rfl

example [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)] {S : Type uS}
    [MeasurableSpace S] (impl : KernelHandler P S) (a : P.A)
    (next : P.B a → FreeM P α) (state : S) :
    FreeM.runKernel impl (.liftBind a next) state =
      (impl a state).bind (fun out => FreeM.runKernel impl (next out.1) out.2) :=
  FreeM.runKernel_liftBind impl a next state

example (x : α) : evalDist (pure x : Id α) = Measure.dirac x := rfl

example (x : α) : evalDist (some x) = Measure.dirac x := rfl

example (mx : Option α) : prFail mx = (evalDist ((fun _ ↦ PUnit.unit) <$> mx)).defect := rfl

example [P.AnswerMeasure] (program : FreeM P α) : evalDist program = FreeM.denote program := rfl

example (mx : OptionT Option α) : evalDist mx = (evalDist mx.run).comap some := rfl

example {ε : Type uR} [MeasurableSpace ε] (mx : ExceptT ε Option α) :
    evalDist mx = (evalDist mx.run).comap Except.ok := rfl

example (mx : Option α) : (SemanticsVia.ofEvalDistSemantics Option).evalDist mx = evalDist mx :=
  rfl

end PolyFunTest.ModuleAPI.Probability
