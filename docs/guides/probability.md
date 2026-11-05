# Probability

PolyFun interprets its programs measure-theoretically, as Giry interpretations with Mathlib's
`Measure` and `Kernel`. The measure modules live beside the constructions they interpret, and
`import PolyFun` loads them. They contain no cryptographic security notions; those belong in
[VCVio](polyfun-and-vcvio.md).

## Scope

The measure modules hold statements about measures that need no security notion: subprobability
measures and kernels, and the measures and kernels that free programs, kernel handlers and their
paths denote. Security experiments, distinguishing advantage, adversary classes, negligibility,
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
its subdirectories. In `PolyFun/`, the areas with measure modules are `PFunctor/` (polynomial
interfaces), `PFunctor/Free/` (free programs) and `PFunctor/Wiring/` (polynomial wiring). A measure
interpretation of another kind of construction starts a new area. Each area whose constructions get
a measure interpretation has one measure home: `<area>/Measure.lean` holds the area's main measure
module, and `<area>/Measure/` holds the others.

A subdirectory of an area uses the area's home, unless it is an area itself. Free programs
therefore have one home: a measure reading of their paths, weakest preconditions or costs
(`Free/Path`, `Free/WP`, `Free/Cost`) belongs in `PFunctor/Free/Measure/`, not in a companion under
`Free/Path/`, `Free/WP/` or `Free/Cost/`. Polynomial wiring is an area of its own, although it
sits inside `PFunctor/`, so its measure module is `PFunctor/Wiring/Measure.lean`.

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
- **The measure fold**
  ([`PFunctor/Measure`](../../PolyFun/PFunctor/Measure.lean),
  [`Free/Measure`](../../PolyFun/PFunctor/Free/Measure.lean)).
  `PFunctor.FreeM.measureFold μ` folds a free program into a measure on its results with
  `Measure.bind`, under arbitrary per-operation answer measures `μ`: probability measures,
  subprobability measures for operations that can fail, or other weightings. An unmeasurable
  continuation folds to zero. Subprobability answers give a subprobability result, and over
  discrete answers probability answers give a probability result. Substitution is pullback:
  folding a program simulated by a free handler is folding the source program under the
  measures its implementations fold to (`measureFold_liftM`), the measure counterpart of
  `wpFold_liftM`. `PFunctor.AnswerMeasure` assigns a probability measure to each operation, and
  `PFunctor.FreeM.denote` is the fold under it. Over discrete answers, `denote` preserves bind and
  map out of a discrete result type (`denote_bind_of_discrete`, `denote_map_of_discrete`), and two
  independent runs, the first with a discrete result type, denote the product measure
  (`denote_bind_bind_prod_mk_eq_prod`).
- **The expectation algebra**
  ([`Free/Measure/Expectation`](../../PolyFun/PFunctor/Free/Measure/Expectation.lean)).
  `expectationAlgebra ν` collapses a program with values in `ℝ≥0∞` to the integral of those values
  under its measure fold. It is an ordered monad algebra, so PolyFun's program-logic bridges make
  it an exact weakest-precondition interpretation in which `wp x post` is the expected value of
  `post` (`expectationAlgebra_μ_bind_pure`). Under subprobability answers it restricts to the
  probability carrier `Set.Iic (1 : ℝ≥0∞)` (`probabilityAlgebra`). `open scoped
  PFunctor.FreeM.Expectation` installs the algebra of `PFunctor.AnswerMeasure`.
- **Kernel handlers**
  ([`Free/Measure/Kernel`](../../PolyFun/PFunctor/Free/Measure/Kernel.lean),
  [`Free/Measure/Kernel/Transport`](../../PolyFun/PFunctor/Free/Measure/Kernel/Transport.lean),
  [`Wiring/Measure`](../../PolyFun/PFunctor/Wiring/Measure.lean)).
  A `KernelHandler P S` samples each operation's answer together with a successor state.
  `PFunctor.FreeM.runKernel` extends it to a kernel from initial states to results and final
  states, and it agrees with first interpreting a free handler's implementations
  (`runKernel_liftM`). Almost-everywhere state invariants and state projections transport from
  single steps to whole programs. `Wiring.runKernel` interprets recursive polynomial wiring.
  [`Free/Measure/Kernel/Handler`](../../PolyFun/PFunctor/Free/Measure/Kernel/Handler.lean) gives
  the constructions: pullback along a free handler (`KernelHandler.comap`, with `comap_comap`), the
  Dirac handler of a deterministic step (`KernelHandler.ofFun`, run by `runKernel_ofFun`), Markov
  program kernels from Markov operation kernels, and the stateless kernel of answer measures
  (`KernelHandler.ofMeasure`), whose run is the measure fold (`runKernel_ofMeasure`).
- **Possible outputs and positive mass**
  ([`Free/Measure/Support`](../../PolyFun/PFunctor/Free/Measure/Support.lean)).
  Over discrete answers, every result of positive mass is in PolyFun's `MonadAttach` support of
  the program, and under answer measures of full support the two sets agree
  (`support_eq_setOf_measureFold_ne_zero`). Without full support, reachability and positive
  probability differ.
- **Path measures**
  ([`Free/Measure/Path`](../../PolyFun/PFunctor/Free/Measure/Path.lean)).
  `pathMeasure` is the measure on completed paths, and `expectedQueryCount` is the expected path
  length, bounded by a total roll bound (`expectedQueryCount_le_of_isTotalRollBound`).

The measure modules keep the names and namespaces of the declarations they took over from VCVio,
so VCVio can import them without renaming.

## Relation to VCVio and to interaction cost

VCVio specializes these interpretations to oracle computations. Its `OracleComp` programs are
PolyFun free programs, and its `evalDist`, `Pr{…}[…]` notation and `EvalDistSemantics` class
read the measures defined here.

The interaction-cost modules are probability-free. An expected cost is a measure-valued reading
of the same programs, so it belongs in a measure companion.
