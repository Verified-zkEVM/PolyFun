# PolyFun documentation

PolyFun connects typed requests, programs, handlers, behavior trees, and
explicit-state machines. Start with the reading route that matches your goal.
The Lean source is authoritative for definitions and theorem assumptions.

## Start here

| Reader | Route |
|---|---|
| New to Lean | [Install and build](getting-started.md), then [write a first program](tutorials/first-program.md) |
| Familiar with Lean libraries | [Repository map](reference/repo-map.md), then [choose a computation model](guides/computation-models.md) |
| Modeling interaction | [Interfaces and protocol shapes](guides/interaction.md), [execution](guides/execution.md), [open composition](guides/open-systems.md) |
| Coming from VCVio | [Ownership and API correspondence](guides/polyfun-and-vcvio.md) |
| Contributing | [Contribution guide](../CONTRIBUTING.md), [validation](development/validation.md), [module APIs](development/module-api.md) |

## Tutorials and examples

- [First program](tutorials/first-program.md): two requests, two interpretations, checked results.
- [Indexed programs](tutorials/indexed-programs.md): a protocol whose type records its phases.
- [Runnable Lean examples](../Examples/README.md): program, machine, and indexed-program source.
- [Parliament](../Examples/Parliament/README.md): an executable application with certified history, interchangeable handlers, and explicit IO boundaries.

## Guides

- [Polynomial functors](guides/pfunctor.md): positions, directions, lenses, charts, free and cofree structures.
- [Indexed polynomial functors](guides/ipfunctor.md): state-dependent interfaces and their free programs.
- [Computation models](guides/computation-models.md): which model to use and what their connections preserve.
- [Interaction trees](guides/itree.md): silent steps, recursion, handlers, and observations.
- [Interaction](guides/interaction.md): type trees, decorations, strategies, and concurrency.
- [Execution](guides/execution.md): machine state, handler state, bounded runs, and networks.
- [Open systems](guides/open-systems.md): composition laws, contexts, observations, and instantiation obligations.
- [Program logic](guides/program-logic.md): support, ordered algebras, and weakest preconditions.
- [Realizability](guides/realizability.md): represented boundaries, admissible machines, and resource certificates.
- [Bisimulation](guides/bisimulation.md): strong, delay, and weak behavioral relations.
- [PolyFun and VCVio](guides/polyfun-and-vcvio.md): generic constructions and cryptographic interpretations.

## Reference

- [Repository map](reference/repo-map.md): library targets, imports, and dependency direction.
- [Notation](reference/notation.md): scoped mathematical and interaction notation.
- [Mathematical background](reference/mathematical-background.md): literature and formalized constructions.
- [Pattern runs on matter](reference/pattern-runs-on-matter.md): the free/cofree action and its scope.
- [Parallel composition](reference/parallel-composition.md): one-sided and joint interaction.
- [Bibliography](../REFERENCES.md) and [generated API documentation](https://verified-zkevm.github.io/PolyFun/docs/).

## Development

[Validation](development/validation.md), [module APIs](development/module-api.md),
[linting](development/linting.md), [generated files](development/generated-files.md),
[review practices](development/review-hardening.md),
[troubleshooting](development/troubleshooting.md), and
[upstream obligations](development/upstream.md) document contributor workflows.
[AGENTS.md](../AGENTS.md) is the canonical agent guide;
[CONTRIBUTING.md](../CONTRIBUTING.md) is the human contribution guide.

## Maintenance contract

Each topic has one owning guide. Change that guide in the same PR as a public
API, command, import boundary, or source-layout change. Source wins when prose
and declarations disagree. Keep executable teaching material in `Examples/`
and regressions in `PolyFunTest/`; keep links and README excerpts checked by
`scripts/check-docs-integrity.py`.

Document present behavior and explicit assumptions. Preserve useful design
rationale in its owning guide, and keep transient review evidence and migration
maps in PR descriptions. Historical progress logs remain available in Git
history. Cite public references rather than local manuscripts or personal paths.
