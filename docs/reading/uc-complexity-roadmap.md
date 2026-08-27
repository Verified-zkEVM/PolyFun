# UC and computational-complexity roadmap

This is the cross-repository milestone ledger for the computational UC stack.
It reconciles PolyFun's categorical roadmap, PolyFun's qualitative
realizability layer, VCVio's cost semantics, and cslib's developing machine
complexity theory. Lean source remains authoritative for declarations; the
three repositories keep their own implementation details.

## Architectural decision

The target proof chain is:

```text
cslib machine/function witness
  -> PolyFun structural process realization
  -> PolyFun composition-closed SubTheory
  -> VCVio probabilistic execution and resource accounting
  -> VCVio asymptotic contextual emulation
```

We use **selective upstreaming**, not either extreme:

- cslib owns domain-neutral admissible-function classes, encodings, LTS
  theory, and concrete machine time/space;
- PolyFun owns polynomial and dynamical realization, lifted step boundaries,
  open processes, and structural sub-theories;
- VCVio owns samplers, probability, resource profiles, negligible advantage,
  and cryptographic instantiations.

Moving all realizability into cslib would leak polynomial/open-process details
upstream. Keeping all complexity machinery in PolyFun would duplicate cslib's
machine models and make interoperability harder. VCVio's pathwise, output-wise,
and expected query costs are semantic crypto infrastructure and do not move.

## Critical path

### M0 — structural bridge (landed in PolyFun)

- `Realizability/DynSystem.lean` gives arbitrary polynomial dynamical systems a
  first-order realization boundary.
- `DynSystem.ulift` normalizes state, position, and direction universes before a
  `StepClass` is applied.
- `DynSystem.Realization.update?` is an admissible partial extension with an
  enabled-step correctness law. It does not require decidable equality on
  semantic positions such as decorated type trees.
- `Interaction/UC/Realizability.lean` defines
  `OpenProcess.StructuralBoundary`, direct structural realizability,
  `realizableSubTheory`, and `generatedRealizableSubTheory`.
- Direct membership is available after proving
  `OpenProcess.IsRealizabilityClosed`; generated membership is the honest
  fallback while composite-machine witnesses remain open.
- `DynSystem.Boundary.PolyTranslatable` makes direct realizability invariant
  under mutually admissible position and flattened-index encodings; the
  `OpenProcess.StructuralBoundary` abbreviation inherits this result.

Exit test: the unconstrained instance builds a direct plug-closed sub-theory,
and the generated sub-theory embeds into it.

### M1 — cslib admissibility substrate

1. Upstream `StepClass` under a neutral cslib namespace, including product,
   sum, option, distributivity, word-class, code-retraction, and representation
   translation APIs.
2. Keep `PFunctor.StepClass` compatibility aliases in PolyFun for one release.
3. Instantiate the abstraction using cslib's multi-tape time-and-space model.
   Land polynomial closure for composition, pairing, projections, tags,
   options, and codecs.
4. Represent randomness, nondeterministic paths, and oracle answers as explicit
   tapes. No distribution semantics enters cslib.

This is a bounded sub-milestone of cslib issue
[#611](https://github.com/leanprover/cslib/issues/611), not a reason to wait for
every proposed machine model. PFunctor PRs
[#803](https://github.com/leanprover/cslib/pull/803) and
[#731](https://github.com/leanprover/cslib/pull/731) remain useful but do not
gate this path.

### M2 — direct structural composition

1. **Landed:** `StepOver.mapContextLens`, `ProcessOver.mapContext_eq_wrap`, and
   `OpenProcess.structuralMapLens` factor boundary adaptation through an
   admissible lifted lens. `IsStructurallyRealizableBy.mapBoundary` performs the
   generic transport.
2. **Landed:** the product-state realization combinator
   (`Realization.choiceProd`, `IsRealizableBy.wrapChoiceProd`, and the
   universe-normalized `IsRealizableBy.ulift_wrapChoiceProd` in
   `Realizability/DynSystemClosure.lean`). Its certificate
   `Lens.IsChoiceAdmissible` exposes an admissible partial routing extension
   into `p.Idx ⊕ q.Idx` with enabled left/right routing laws and assumes no
   equality on type trees. New `StepClass` mixins: `HasOption.some_mem` (with
   the derived strength `omapCtx_mem`) and `HasULiftProd`.
3. **Landed (generic side):** `OpenProcess.IsRealizabilityClosed` is now four
   first-order lens certificates (`mapAdmissible`, `par/wire/plugAdmissible`),
   and `par_mem`/`wire_mem`/`plug_mem` are theorems derived through
   `ulift_wrapChoiceProd`; the contract mentions no processes or samplers.
   The cslib-class instantiation of the certificates remains open, and the raw
   structural boundary is never codable (`TypeTree` positions), so it will
   route through codable sub-interface boundaries plus `mapAdmissible`
   transport.
4. Reuse the landed representation-translation invariance for
   `DynSystem.Boundary` and `OpenProcess.StructuralBoundary` when selecting the
   concrete cslib encodings.

Exit test **(met for the generic pipeline)**: membership in
`realizableSubTheory` is a direct machine witness for every nested
`par`/`wire`/`plug` — the canary instance derives composite witnesses through
the combinator rather than assuming them, and
`generatedRealizableSubTheory_eq_realizableSubTheory` collapses the generated
view. The concrete-class exit test remains gated on M1.

### M3 — VCVio computational contexts

Landed downstream in `VCVio/Interaction/UC/ComputationalWithin.lean`:

- `ObservedCompEmulatesWithin`;
- `AsympObservedCompEmulatesWithin`;
- `ObservedCompUCSecureWithin`;
- top-subtheory reconciliation with the pre-existing unrestricted judgments;
- fixed-bound and asymptotic parallel, wired, and plug composition.

**Landed in PolyFun (the structural observation bridge):** the sampler-aware
coherence laws (`OpenProcessSamplerFactorization`, conditional on named
scheduler-transport hypotheses over an abstract `MonadRelFamily`) and
`Observation.respectsFactorization_of_samplerInvariant`
(`SamplerObservation`). A distributional VCVio observation now obtains
`RespectsFactorization` by supplying its relation family (equality of
measure-valued `evalDist` denotations), the three scheduler-transport facts,
and its sampler-equivalence invariance (adequacy) — see the gate map in
`docs/wiki/uc.md`.

The remaining concrete steps are `PPTProcessWitness` and `pptSubTheory`.

One `PPTProcessWitness` must uniformly handle the security parameter plus
encoded state/input. It combines a PolyFun structural realization with
canonical encoding retractions, sampler and scheduler machines, polynomial
time/state/activation bounds, and explicit random/path/oracle tapes. A named
adequacy theorem relates those tapes to `ProbComp`/`OracleComp` execution.

VCVio's `ResourceProfile`, `CostModel`, and `ReductionWithCost` remain intact.
The new bridge states that a polynomially bounded profile produces the machine
witness required by `pptSubTheory`, and that reduction transforms preserve it.

### M4 — vertical canaries

1. Parameterized one-time pad: pin `BitVec`/state encodings; certify real,
   ideal, simulator, scheduler, and a nontrivial closing context; prove
   zero-advantage asymptotic emulation within `pptSubTheory` without an opaque
   `isPPT` assumption.
2. ElGamal reduction cost: connect the existing exact resource profile to a
   concrete machine witness and show the reduction transform preserves PPT.

The OTP result is called observed computational emulation until the hypotheses
needed by the standard dummy-adversary theorem are proved.

## Non-blocking alignment lane

- Upstream delay bisimulation and generic `HasTau (Option α)` to cslib.
- Convert PolyFun's move-indexed LTS to cslib's relation-indexed LTS and migrate
  activation equivalence to the common theory.
- Make cslib/Lean/Mathlib pin upgrades isolated compatibility changes rather
  than mixing them with mathematical PRs.

## Deferred semantic and categorical work

After M4, build the cofree behavior carrier and its adequacy theorem into VCVio
execution, then dummy/multiplexer and global-subroutine composition. Resume
roadmap Phase D's bicomodule work against those named consumers. Until then,
Phase D is a research lane rather than the critical engineering path.

Corruption remains orthogonal to efficiency. Define its own sub-theory bridge
and combine it with `pptSubTheory` through `SubTheory.inf`.

## Acceptance and release discipline

- Every boundary encoding is a parameter or has a proved translation
  invariant; never existentially select public encodings.
- Charge initialization/exposure, enabled updates, reachable state growth,
  sampler work, scheduling, and activation count separately.
- Do not claim randomized PPT before the explicit-tape adequacy theorem.
- Each layer remains axiom-clean and passes its repository's build, lint, test,
  and axiom sweep.
- Land in dependency order: cslib substrate, PolyFun adoption/composition,
  VCVio computational relation, then examples.
