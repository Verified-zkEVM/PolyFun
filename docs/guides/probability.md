# Probability

PolyFun's measure-theoretic interpretations are Giry interpretations with Mathlib's `Measure` and
`Kernel`. Their modules belong beside the constructions they interpret. They contain no
cryptographic security notions; those belong in [VCVio](polyfun-and-vcvio.md). The first measure
modules are staged Mathlib lemmas on subprobability measures and kernels.

## Scope

The measure modules hold statements about measures that need no security notion: subprobability
measures and kernels. Security experiments, distinguishing advantage, adversary classes, negligibility,
hardness assumptions, named reductions and schemes stay downstream.

A generic construction takes a monad, a semantic carrier or an observation as a parameter, and
the measure modules supply measure-valued instances of those parameters.

## Conventions

- **Measures, not mass functions.** The measure modules use Mathlib's `Measure` and `Kernel` and
  the Giry operations (`Measure.bind`, `Measure.dirac`, `Kernel.comp`). They do not use `PMF`: the
  lawful monad instance on `PMF` lives in
  `Mathlib.Probability.ProbabilityMassFunction.Constructions`, whose import closure brings in most
  of Mathlib's analysis.
- **Subprobability for failure.** A computation that may fail to return denotes a measure of total
  mass at most one (`MeasureTheory.IsSubprobabilityMeasure`). The missing mass is the probability
  of failure, so failure needs no `Option` wrapper. Mathlib's `IsZeroOrProbabilityMeasure` is a
  different condition: it allows only total mass `0` or `1`.
- **Explicit measurable spaces.** Theorems state the measurability hypotheses they use. Mathlib's
  `Measure.map` and `Measure.bind` return a junk value for a non-measurable function, so lemmas
  about them carry measurability or almost-everywhere measurability side conditions.
- **Staged Mathlib lemmas.** Lemmas that belong in Mathlib live under `ToCslib/MeasureTheory/` and
  `ToCslib/Probability/`, in paths that mirror Mathlib's, until they are upstreamed.

## Where the modules live

The measure interpretation of a construction lives in a `Measure` companion beside it, in the
measure home of its area. An area is a directory that holds one kind of construction, together with
its subdirectories. No area of `PolyFun/` has a measure module yet. A measure interpretation of a
kind of construction that has none starts a new area. Each area whose constructions get
a measure interpretation has one measure home: `<area>/Measure.lean` holds the area's main measure
module, and `<area>/Measure/` holds the others.

A subdirectory of an area uses the area's home, unless it is an area itself. Free programs
therefore have one home: a measure reading of their paths, weakest preconditions or costs
(`Free/Path`, `Free/WP`, `Free/Cost`) belongs in `PFunctor/Free/Measure/`, not in a companion under
`Free/Path/`, `Free/WP/` or `Free/Cost/`. Polynomial wiring is an area of its own, although it
sits inside `PFunctor/`, so its measure module belongs at `PFunctor/Wiring/Measure.lean`.

The staged lemmas are about Mathlib's and core's types, not about PolyFun constructions, so they
live in `ToCslib/MeasureTheory/` and `ToCslib/Probability/`, in paths that mirror Mathlib's. Like
the rest of `ToCslib`, they import no PolyFun module.

## Contents

- **Subprobability measures**
  ([`Subprobability`](../../ToCslib/MeasureTheory/Measure/Subprobability.lean)).
  `IsSubprobabilityMeasure μ` states `μ Set.univ ≤ 1`. It has instances for `dirac`, products
  and pushforwards, and `isSubprobabilityMeasure_bind` keeps the bound through a bind with an
  almost-everywhere measurable subprobability family. `Measure.defect` is the missing mass.
- **Subprobability kernels**
  ([`Subprobability`](../../ToCslib/Probability/Kernel/Subprobability.lean)).
  `IsSubprobabilityKernel κ` bounds every fibre. Constant, restricted, pushed-forward,
  pulled-back, composed and product kernels keep the bound, and every Markov kernel is a
  subprobability kernel.

## Relation to VCVio and to interaction cost

VCVio interprets oracle computations measure-theoretically. Its `OracleComp` programs are
PolyFun free programs, and its `evalDist`, `Pr{…}[…]` notation and `EvalDistSemantics` class read
their measures.

The interaction-cost modules are probability-free. An expected cost is a measure-valued reading
of the same programs, so it belongs in a measure companion.
