# PolyFunFrontier

PolyFunFrontier holds the parts of PolyFun that need
[cslib-frontier](https://github.com/cslib-community/cslib-frontier), the frontier library built on
[CSLib](https://github.com/leanprover/cslib). It is a separate Lake package inside the PolyFun
repository, so PolyFun itself keeps requiring only Mathlib and CSLib, and nothing that requires
PolyFun (VCVio, ArkLib, CatCrypt) ever resolves cslib-frontier.

```
   CSLib  ──────────▶  cslib-frontier
     │                     │
     ▼                     ▼
  PolyFun ──────────▶  PolyFunFrontier
```

cslib-frontier keeps each module at the path and namespace it would have in CSLib, so a module
moves upstream by changing its import prefix. PolyFunFrontier does the same one level up:

- A module sits at the path and namespace it would have in PolyFun.
  `PolyFunFrontier/PFunctor/Free/DecisionTree.lean` is the future
  `PolyFun/PFunctor/Free/DecisionTree.lean`.
- Each module records the cslib-frontier modules it waits on, in a comment after `module`:
  `-- frontier: CslibFrontier.Computability.DecisionTree.Parity`.
- When those modules reach CSLib, the module moves into `PolyFun/`: rename the file, replace
  `PolyFunFrontier.` by `PolyFun.` and `CslibFrontier.` by `Cslib.`, and leave a deprecated module
  in its place.
- Anything that needs no cslib-frontier module goes straight into PolyFun, not here.

## What is here

| Module | Content |
|---|---|
| `PFunctor/Free/DecisionTree` | Boolean decision trees are the free programs of `monomial ι Bool`; evaluation is the fold that answers queries from the input, and depth is the total roll bound |
| `PFunctor/Free/DecisionTree/LowerBound` | cslib-frontier's decision-tree lower bounds for free programs: a program computing the parity of `n` bits has no total roll bound below `n`, and the sensitivity and restricted-parity bounds |
| `Realizability/MultiTape` | The `StepClass.multiTapePolyTime` representations are injective binary encodings. Frontier's deterministic polynomial-time functions supply its admissible maps, including pairing and both projections. |
| `IPFunctor/Scoped/PolyTime` | Every fixed binary expression built from Boolean truth tables denotes a polynomial-time map on two encoded words. The one-time pad uses pointwise XOR and a nested expression that reuses the key. |
| `PFunctor/Free/Realization` | A certificate combines deterministic local maps, primitive probabilistic handlers, sequential composition, Boolean branches, and fair-bit sampling. `MachineRealization.ofPPTProgram` chooses one finite-control probabilistic machine whose output agrees with the handler fold and whose polynomial clock bounds every supported run on every input word. |

Installing a handler can change how the same source branches. In the regression below, the source
asks for a bit and asks again only on true. On the tape `[false, true, false, true]`, a handler
that reads one bit per request returns false with three bits left. Installing a handler that
reads two bits and returns the second makes the same source return true with an empty tape.
`PPTProgram.substitute` transfers the derivation over the composite handler to the installed
source. Under fair coins, `consecutive_pptProgram` certifies the complete branch, and
`consecutiveMachine_output` identifies the machine’s output law with the original program run
through the composite handler.
[Handler substitution regressions](PolyFunFrontierTest/Realization.lean)

## Building

The package uses cslib-frontier's Lean toolchain and its CSLib and Mathlib commits. The PolyFun
modules it imports compile on those pins. Warnings are errors in PolyFunFrontier's own modules.

```bash
cd PolyFunFrontier
lake exe cache get                          # Mathlib's cache; CSLib and cslib-frontier build from source
python3 scripts/check-pins.py               # toolchain, CSLib and Mathlib equal cslib-frontier's
lake build PolyFunFrontier PolyFunFrontierTest
lake exe polyfun-axiomsweep --root PolyFunFrontier \
  --baseline ../scripts/axiom_baseline.json --check   # PolyFun's zero-debt baseline
```

Work on this package in its own git worktree. Its path dependency on `..` builds PolyFun into the
repository's `.lake/build`, on cslib-frontier's toolchain. In one checkout, the root build and this
one would keep replacing each other's outputs. The dependency is inside
the repository, so a fresh clone still builds.

Do not use cslib-frontier's own `.olean` cache: Lean trusts downloaded `.olean` files without
re-checking them in the kernel.

## Moving the pins

cslib-frontier publishes no tags, so it is pinned by full commit, and the CSLib and Mathlib pins
must equal the ones that commit records. `scripts/bump.sh <commit>` moves all of them and the
toolchain together, updates only those packages, and runs `scripts/check-pins.py`.

If a bump or a PolyFun change breaks this package, first look for a change that compiles on both
toolchains. Otherwise keep the last commit that builds until PolyFun's next toolchain bump.
