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
- the import closure of those four roots, through Mathlib and the other packages, reaches
  none of these modules either, so an indirect import cannot bring measure theory into the
  core;
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

## Relation to VCVio and to interaction cost

VCVio specializes these interpretations to oracle computations. Its `OracleComp` programs are
PolyFun free programs, and its `evalDist`, `Pr{…}[…]` notation and `EvalDistSemantics` class
read the measures defined here.

The interaction-cost API in the core library is probability-free. An expected cost is a
measure-valued reading of the same programs, so it belongs in this library.
