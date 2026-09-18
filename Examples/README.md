# PolyFun examples

These small programs are intended to be read and edited. From the repository root:

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
[Development notes](../docs/development/upstream.md#open-development) link
proposed larger applications while they are under review.
