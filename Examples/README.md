# PolyFun examples

The tutorials and executable case study are intended to be read and edited. From the repository root:

```sh
lake build PolyFunExamples
lake env lean Examples/Tutorials/Requests.lean
```

| Module | What to explore |
|---|---|
| [Requests](Tutorials/Requests.lean) | The same dependent sequence of requests interpreted by two handlers |
| [Machines](Tutorials/Machines.lean) | A counter's state, outputs, trace, and composition of finite runs |
| [Indexed programs](Tutorials/IndexedPrograms.lean) | Two protocol phases, indexed sequencing, and forgetting indices |

Use ordinary imports such as `import Examples.Tutorials.Requests`.
The Lake target is `PolyFunExamples`, so it can coexist with downstream
projects' `Examples` targets. No generic `Examples` umbrella is provided.
Neither `lake build` nor `import PolyFun` includes this optional library.
Repository validation builds, lints, tests, and audits these examples explicitly.

Start with the [first-program walkthrough](../docs/tutorials/first-program.md)
or the [indexed-program walkthrough](../docs/tutorials/indexed-programs.md).

## Parliament application

[Parliament](Parliament/README.md) combines indexed meeting inputs, certified
histories, a returning machine, and interchangeable memory/IO handlers. It exports
replayable journals and unapproved draft minutes for an explicitly bounded rule set.
Use `import Examples.Parliament` for the case-study API.

```sh
lake build polyfun-parliament
lake exe polyfun-parliament --help
```

Read the [runtime contract](Parliament/Docs/runtime.md) alongside the source.
The [execution guide](../docs/guides/execution.md#resumable-execution) explains
the generic driver reused by this application.

The [Parliament walkthrough](Parliament/Docs/walkthrough.md) follows the same
application through certified prefixes, safety, resumptions, interaction trees,
and a writer handler whose erasure preserves execution.
