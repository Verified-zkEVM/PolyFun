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

## Building

The package uses cslib-frontier's Lean toolchain and its CSLib and Mathlib commits, which are
newer than PolyFun's stable tags. PolyFun's own modules compile here on that toolchain; warnings
are errors only in this package's modules.

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
