# Probability

`PolyFunProbability` is an optional library of measure-theoretic interpretations of PolyFun
programs. It sits outside the generic `PolyFun` umbrella, so `import PolyFun` loads no measure
theory. It contains no cryptographic security notions; those belong in
[VCVio](polyfun-and-vcvio.md).

## Scope

The library holds statements about measures that need no security notion: subprobability
measures and kernels, and the measures and kernels that free programs, kernel handlers and their
paths denote. Security experiments, distinguishing advantage, adversary classes, negligibility,
hardness assumptions, named reductions and schemes stay downstream.

The core PolyFun libraries stay free of measure theory. A generic construction there takes a
monad, a semantic carrier or an observation as a parameter, and this library supplies
measure-valued instances of those parameters.

## Conventions

- **Measures, not mass functions.** The library uses Mathlib's `Measure` and `Kernel` and the
  Giry operations (`Measure.bind`, `Measure.dirac`, `Kernel.comp`). It does not use `PMF`: the
  lawful monad instance on `PMF` lives in a module whose import closure brings in most of
  Mathlib's analysis.
- **Subprobability for failure.** A computation that may fail to return denotes a measure of total
  mass at most one (`MeasureTheory.IsSubprobabilityMeasure`). The missing mass is the probability
  of failure, so failure needs no `Option` wrapper. Mathlib's `IsZeroOrProbabilityMeasure` is a
  different condition: it allows only total mass `0` or `1`.
- **Explicit measurable spaces.** Theorems state the measurability hypotheses they use. Mathlib's
  `Measure.map` and `Measure.bind` return a junk value for a non-measurable function, so lemmas
  about them carry measurability or almost-everywhere measurability side conditions.
- **Staged Mathlib lemmas.** Lemmas that belong in Mathlib live under
  `PolyFunProbability/ToMathlib/`, in paths that mirror Mathlib's, until they are upstreamed.

## The quarantine

`scripts/check-modules.sh` enforces the
[probability quarantine](../../AGENTS.md#probability-quarantine):

- only `PolyFunProbability/` and `PolyFunTest/Probability/` import `Mathlib.MeasureTheory`,
  `Mathlib.Probability` or `Mathlib.InformationTheory`;
- no module imports `Mathlib.Probability.ProbabilityMassFunction`;
- `PolyFun`, `ToCslib`, `ComplexityBackends` and `PolyFunIO` do not import
  `PolyFunProbability`;
- `PolyFunProbability` opens no `PolyFun` or `ToCslib` bodies.

## Contents

- **Subprobability measures**
  ([`Subprobability`](../../PolyFunProbability/ToMathlib/MeasureTheory/Measure/Subprobability.lean)).
  `IsSubprobabilityMeasure μ` states `μ Set.univ ≤ 1`. It has instances for `dirac`, products
  and pushforwards, and `isSubprobabilityMeasure_bind` keeps the bound through a bind with an
  almost-everywhere measurable subprobability family. `Measure.defect` is the missing mass.
- **Subprobability kernels**
  ([`Subprobability`](../../PolyFunProbability/ToMathlib/Probability/Kernel/Subprobability.lean)).
  `IsSubprobabilityKernel κ` bounds every fibre. Constant, restricted, pushed-forward,
  pulled-back, composed and product kernels keep the bound, and every Markov kernel is a
  subprobability kernel.
- **The measure fold**
  ([`AnswerMeasure`](../../PolyFunProbability/PFunctor/AnswerMeasure.lean),
  [`Free/Measure`](../../PolyFunProbability/PFunctor/Free/Measure.lean)).
  `PFunctor.FreeM.measureFold μ` folds a free program into a measure on its results with
  `Measure.bind`, under arbitrary per-operation answer measures `μ`: probability measures,
  subprobability measures for operations that can fail, or other weightings. An unmeasurable
  continuation folds to zero. Subprobability answers give a subprobability result, and over
  discrete answers probability answers give a probability result. Substitution is pullback:
  folding a program simulated by a free handler is folding the source program under the
  measures its implementations fold to (`measureFold_liftM`), the measure counterpart of
  `wpFold_liftM`. `PFunctor.AnswerMeasure` assigns a probability measure to each operation, and
  `PFunctor.FreeM.denote` is the fold under it. Over discrete answers the fold preserves bind
  and map (`denote_bind_of_discrete`, `denote_map_of_discrete`), and two independent runs denote
  the product measure (`denote_bind_bind_prod_mk_eq_prod`).
- **The expectation algebra**
  ([`Free/Expectation`](../../PolyFunProbability/PFunctor/Free/Expectation.lean)).
  `expectationAlgebra ν` collapses a program with values in `ℝ≥0∞` to the integral of those values
  under its measure fold. It is an ordered monad algebra, so PolyFun's program-logic bridges make
  it an exact weakest-precondition interpretation in which `wp x post` is the expected value of
  `post` (`expectationAlgebra_μ_bind_pure`). Under subprobability answers it restricts to the
  probability carrier `Set.Iic (1 : ℝ≥0∞)` (`probabilityAlgebra`). `open scoped
  PFunctor.FreeM.Expectation` installs the algebra of `PFunctor.AnswerMeasure`.
- **Kernel handlers**
  ([`Free/Kernel`](../../PolyFunProbability/PFunctor/Free/Kernel.lean),
  [`Free/Kernel/Transport`](../../PolyFunProbability/PFunctor/Free/Kernel/Transport.lean),
  [`Wiring/Kernel`](../../PolyFunProbability/PFunctor/Wiring/Kernel.lean)).
  A `KernelHandler P S` samples each operation's answer together with a successor state.
  `PFunctor.FreeM.runKernel` extends it to a kernel from initial states to results and final
  states, and it agrees with first interpreting a free handler's implementations
  (`runKernel_liftM`). Almost-everywhere state invariants and state projections transport from
  single steps to whole programs. `Wiring.runKernel` interprets recursive polynomial wiring.
- **Possible outputs and positive mass**
  ([`Free/Support`](../../PolyFunProbability/PFunctor/Free/Support.lean)).
  Over discrete answers, every result of positive mass is in PolyFun's `MonadAttach` support of
  the program, and under answer measures of full support the two sets agree
  (`support_eq_setOf_measureFold_ne_zero`). Without full support, reachability and positive
  probability differ.
- **Path measures**
  ([`Free/Path/Measure`](../../PolyFunProbability/PFunctor/Free/Path/Measure.lean)).
  `pathMeasure` is the measure on completed paths, and `expectedQueryCount` is the expected path
  length, bounded by a total roll bound (`expectedQueryCount_le_of_isTotalRollBound`).

The library keeps the names and namespaces of the declarations it took over from VCVio, so
VCVio can import them without renaming.

## Relation to VCVio and to interaction cost

VCVio specializes these interpretations to oracle computations. Its `OracleComp` programs are
PolyFun free programs, and its `evalDist`, `Pr{…}[…]` notation and `EvalDistSemantics` class
read the measures defined here.

The interaction-cost API in the core library is probability-free. An expected cost is a
measure-valued reading of the same programs, so it belongs in this library.
