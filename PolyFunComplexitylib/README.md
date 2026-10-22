# PolyFunComplexitylib

`PolyFunComplexitylib` is an optional, nested Lake package that imports
[complexitylib](https://github.com/cslib-community/complexitylib) directly and bridges its
complexity notions to PolyFun's polynomial-functor API. `import PolyFun` and PolyFun's downstream
consumers never resolve complexitylib; only this package does.

complexitylib's oracle programs are already PolyFun's substrate: `Cslib.OracleComp spec α` is
`PFunctor.FreeM ⟨ι, spec⟩ α` and `interpret` is `liftM`. The package therefore adds no
translation layer for programs. It proves that complexitylib's other free-monad-shaped structures
are PolyFun's, and supplies a quantitative realizability backend over complexitylib's machines.

| Module | Content |
|---|---|
| `Oracle.QueryBound` | complexitylib's semantic `HasQueryBounds` is PolyFun's structural `IsRollBound` when every query is answerable, and vacuous otherwise |
| `Query.DecisionTree` | `DecisionTree ι β ≃ FreeM ⟨ι, fun _ => Bool⟩ β`; query complexity over any polynomial interface, specializing to `DecisionTree.complexity` |
| `Query.Protocol` | two-party protocols are free programs over the message interface; `run` is the fold against the copaired sections |
| `Stateful.Responder` | `Stateful.Spec` is a `PFunctor.Responder`; client evaluation is `Responder.runFree`; modules compose as free handlers |
| `Backend.StepClass` | polynomial-time tidy computability as a `StepClass`, with products, sums, options and distributivity |
| `Backend.Quantitative` | realizers are concrete tidy machines; composition cost is exact; first-order polynomial certificates |
| `Backend.SingleTape` | certificates of the `ComplexityBackends.CslibSingleTape` backend transfer to multi-tape machines |
| `Adequacy.Iterate` | a closed machine iterated polynomially many times from PolyFun codes is strict oracle PPT |

Build from the repository root:

```bash
cd PolyFunComplexitylib
lake exe cache get
lake build --wfail
lake build PolyFunComplexitylibTest --wfail
lake lint
```

`PolyFunComplexitylibTest.Collision` imports all of complexitylib together with PolyFun and its
backends; building it checks that the two libraries declare no name twice.

See [PROVENANCE.md](PROVENANCE.md) for the pinned revisions.
