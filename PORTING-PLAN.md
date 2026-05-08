# PolyFun Porting Plan

This document is the canonical, exhaustive plan for the wholesale port of the
generic polynomial-functor / interaction-tree / interaction-framework code
out of `VCV-io` (currently developed in worktree
`~/Documents/Lean/VCV-io-freeM-displayed`) into this repository.

The plan is written against the snapshot of `VCV-io-freeM-displayed`
on 2026-05-08. The numbers and inventories below are accurate as of that
snapshot; before each phase, sanity-check counts with `rg` / `wc -l` against
the live tree.

## 0. Goals and ground rules

1. **Wholesale copy first, edit second.** Port files verbatim, exactly
   preserving paths under a top-level `PolyFun/` source root, with no
   namespace edits in the first pass. Build is *not* expected to pass
   between phase 1 and phase 2.
2. **No backward compatibility shims** anywhere. Once `PolyFun` exists,
   all `VCVio.Interaction.*` and the moved `ToMathlib.{PFunctor,ITree,...}`
   namespaces are renamed to `PolyFun.*` in one mechanical pass and call
   sites in VCVio + ArkLib are updated. (Per the always-on
   `full-cutover-no-backward-compat` rule.)
3. **No cryptographic content lands here.** The library targets PL semantics,
   game theory, category theory, distributed/concurrent systems, and crypto
   protocols *as one of many* downstream consumers. Anything that mentions
   `ProbComp`, `EvalDist`, `Negligible`, `OracleComp`, `CryptoFoundations`
   in load-bearing code stays in VCVio.
4. **Single source of truth.** When this plan and the live VCVio worktree
   disagree, the live tree wins; update this doc.

## 1. Source-of-truth inventory

The source tree is rooted at `~/Documents/Lean/VCV-io-freeM-displayed/`.

### 1.1 Generic, no crypto deps — moves to `PolyFun/`

#### Layer A: Polynomial functor core

```
ToMathlib/PFunctor/Basic.lean                        481 lines
ToMathlib/PFunctor/Bound.lean                        210 lines
ToMathlib/PFunctor/Category.lean                      44 lines
ToMathlib/PFunctor/Cofree.lean                       179 lines
ToMathlib/PFunctor/MFacts.lean                       102 lines
ToMathlib/PFunctor/Trace.lean                        205 lines
ToMathlib/PFunctor/Chart/Basic.lean                  946 lines
ToMathlib/PFunctor/Equiv/Basic.lean                  692 lines
ToMathlib/PFunctor/Free/Basic.lean                   286 lines
ToMathlib/PFunctor/Free/Path.lean                    951 lines
ToMathlib/PFunctor/Free/Displayed.lean               576 lines
ToMathlib/PFunctor/Free/Displayed/Decoration.lean    373 lines
ToMathlib/PFunctor/Lens/Basic.lean                   863 lines
ToMathlib/PFunctor/Lens/Cartesian.lean               142 lines
ToMathlib/PFunctor/Lens/State.lean                   291 lines
                                              total 6 341 lines
```

Target: `PolyFun/PFunctor/...` (mirror; flatten the leading `ToMathlib/`).

#### Layer B: Interaction trees (coinductive)

```
ToMathlib/ITree/Basic.lean                           297 lines
ToMathlib/ITree/Construct.lean                       136 lines
ToMathlib/ITree/Handler.lean                          72 lines
ToMathlib/ITree/Rec.lean                             110 lines
ToMathlib/ITree/Bisim/Defs.lean                      253 lines
ToMathlib/ITree/Bisim/Bind.lean                      581 lines
ToMathlib/ITree/Bisim/Equiv.lean                     541 lines
ToMathlib/ITree/Sim/Defs.lean                         88 lines
ToMathlib/ITree/Sim/Facts.lean                       831 lines
ToMathlib/ITree/Events/Exception.lean                 48 lines
ToMathlib/ITree/Events/State.lean                     64 lines
                                              total 3 021 lines
```

Target: `PolyFun/ITree/...`.

#### Layer C: Generic interaction framework

```
VCVio/Interaction/Basic/{Spec,Decoration,Syntax,Shape,Interaction,Strategy,
                        Append,Replicate,StateChain,Chain,Node,Telescope,
                        Sampler,MonadDecoration,BundledMonad,Ownership,
                        SpecFintype}.lean
VCVio/Interaction/Concurrent/{Spec,Process,Machine,Tree,Trace,Frontier,
                              Bisimulation,Refinement,Fairness,Liveness,
                              Independence,Interleaving,Observation,Profile,
                              Policy,Run,Equivalence,Examples,Current,
                              Control,Execution}.lean
VCVio/Interaction/TwoParty/{Role,Syntax,Strategy,Decoration,Compose,Refine,
                            Swap,Examples}.lean
VCVio/Interaction/Multiparty/{Core,Broadcast,Directed,Profile,Observation,
                              ObservationProfile,Examples}.lean
VCVio/Interaction/UC/{Interface,OpenProcess,OpenProcessModel,OpenTheory,
                      OpenSyntax/Raw,OpenSyntax/Interp,OpenSyntax/Expr,
                      Notation,Emulates,MachineId,EnvOpenProcess,
                      CorruptionModel,MomentaryCorruption,Leakage}.lean
```

Verified by `rg "^import VCVio\." VCVio/Interaction/{Basic,Concurrent,TwoParty,
Multiparty}` — all hits are within `VCVio.Interaction.*`. The UC subset above
is verified by chasing the dependency graph against the four crypto-tinged
files listed in §1.2.

Target: `PolyFun/Interaction/...` (drop the `VCVio` prefix, keep the
sub-namespacing).

#### Layer D: Generic Control/Logic helpers transitively required

These ship with the library because PFunctor/ITree/Interaction depend on
them, *and* they are themselves crypto-free.

```
ToMathlib/Control/Coalgebra.lean                    used by Concurrent/{Machine,Process}
ToMathlib/Control/Comonad/Basic.lean                used by PFunctor/Cofree
ToMathlib/Control/Comonad/Cofree.lean               (companion; small)
ToMathlib/Control/Comonad/Instances.lean            (companion; small)
ToMathlib/Control/Lawful/Basic.lean                 used by TwoParty/Compose
ToMathlib/Control/Monad/Iter.lean                   used by ITree/Basic
ToMathlib/Control/Monad/Hom.lean                    used by PFunctor/Free/Basic
ToMathlib/Control/Monad/Algebra.lean                used by Control/Monad/Hom
ToMathlib/Logic/HEq.lean                            used by PFunctor/Free/Displayed/Decoration
```

Decision: also pull in `ToMathlib/Control/Monad/{Free,FreeCont,Equiv}.lean`
for completeness — they are PFunctor-tinged free-monad infrastructure with
no crypto content.

Target: `PolyFun/Control/...`, `PolyFun/Logic/...`.

**Watch out:** `ToMathlib/Control/Monad/Hom.lean` currently does
`import Mathlib.Probability.ProbabilityMassFunction.Monad`. Inspect: is the
PMF instance *actually* used anywhere downstream that we are moving? If only
in VCVio crypto code, drop the import in the move and the whole file becomes
genuinely generic. If used in say `Free.lean`, keep the dependency on
mathlib's PMF (which is fine — mathlib is our only require).

### 1.2 Crypto-tinged — STAYS in VCVio

```
VCVio/Interaction/UC/EnvAction.lean              imports OracleComp.ProbComp
VCVio/Interaction/UC/Computational.lean          imports CryptoFoundations + EvalDist
VCVio/Interaction/UC/Runtime.lean                imports SampleableType + Computational
VCVio/Interaction/UC/Standard.lean               depends on Computational
VCVio/Interaction/UC/AsyncRuntime.lean           depends on Runtime
VCVio/Interaction/UC/AsyncSecurity.lean          depends on AsyncRuntime + Computational
VCVio/Interaction/UC/StdDoBridge.lean            imports ProgramLogic.Unary.StdDoBridge
```

`EnvAction.lean` is *almost* portable: it uses `ProbComp` only as the codomain
of one `react` field on a structure. A trivial generalization to a `Monad m`
parameter would lift it into PolyFun, dragging `EnvOpenProcess`,
`CorruptionModel`, and `MomentaryCorruption` along with it.

**Decision (locked):** generalize `EnvAction` and pull it + its three
dependents into PolyFun. The genericization is a 5-minute change and removes
a real footgun (the rest of UC is already monad-generic).

Result after that decision:
- **Stays in VCVio**: `Computational.lean`, `Runtime.lean`, `Standard.lean`,
  `AsyncRuntime.lean`, `AsyncSecurity.lean`, `StdDoBridge.lean`.
- **Moves to PolyFun**: `EnvAction.lean` (post-generalization),
  `EnvOpenProcess.lean`, `CorruptionModel.lean`, `MomentaryCorruption.lean`.

## 2. Target file layout

```
PolyFun/                         # repo root
├── lakefile.toml                # already created
├── lean-toolchain               # already created — pinned to 4.29.0
├── lake-manifest.json           # filled by `lake update` in §3
├── README.md                    # bootstrapped
├── LICENSE                      # Apache 2.0, ships with the empty repo
├── AGENTS.md                    # adapted from VCVio AGENTS.md (see §13.3)
├── CLAUDE.md                    # symlink → AGENTS.md
├── CONTRIBUTING.md              # adapted from VCVio CONTRIBUTING.md
├── REFERENCES.md                # PolyFun-relevant subset of citations
├── PORTING-PLAN.md              # this document
├── PolyFun.lean                 # generated import aggregator
├── PolyFun/
│   ├── PFunctor/
│   │   ├── Basic.lean
│   │   ├── Bound.lean
│   │   ├── Category.lean
│   │   ├── Cofree.lean
│   │   ├── MFacts.lean
│   │   ├── Trace.lean
│   │   ├── Chart/Basic.lean
│   │   ├── Equiv/Basic.lean
│   │   ├── Lens/{Basic,Cartesian,State}.lean
│   │   └── Free/
│   │       ├── Basic.lean
│   │       ├── Path.lean
│   │       ├── Displayed.lean
│   │       └── Displayed/Decoration.lean
│   ├── ITree/
│   │   ├── Basic.lean
│   │   ├── Construct.lean
│   │   ├── Handler.lean
│   │   ├── Rec.lean
│   │   ├── Bisim/{Defs,Bind,Equiv}.lean
│   │   ├── Sim/{Defs,Facts}.lean
│   │   └── Events/{Exception,State}.lean
│   ├── Interaction/
│   │   ├── Basic/        # Spec, Decoration, ..., SpecFintype
│   │   ├── Concurrent/
│   │   ├── TwoParty/
│   │   ├── Multiparty/
│   │   └── UC/           # generic subset only — see §1.1 / §1.2
│   ├── Control/
│   │   ├── Coalgebra.lean
│   │   ├── Lawful/Basic.lean
│   │   ├── Comonad/{Basic,Cofree,Instances}.lean
│   │   └── Monad/{Algebra,Hom,Iter,Free,FreeCont,Equiv}.lean
│   └── Logic/
│       └── HEq.lean
├── scripts/                     # see §13.2
│   ├── lint-style.py            # mathlib-derived style linter
│   ├── lint-style.sh            # wrapper
│   ├── print-style-errors.sh
│   ├── style-exceptions.txt     # starts empty
│   ├── nolints-style.txt        # starts empty
│   ├── update-lib.sh            # regenerate `PolyFun.lean` aggregator
│   ├── check-imports.sh         # CI guard for the aggregator
│   ├── validate.sh              # one-shot local check wrapper
│   ├── requirements.txt         # Python deps for the linter
│   ├── port-from-vcvio.sh       # phase-1 wholesale-copy script (§3)
│   └── rename-namespaces.sh     # phase-2 textual-rename pass (§4)
├── .github/                     # see §13.1
│   ├── dependabot.yml
│   └── workflows/
│       ├── ci.yml
│       ├── linting.yml
│       ├── check-imports.yml
│       ├── release-tag.yml
│       ├── update.yml
│       ├── summary.yml
│       └── review.yml
└── docs/                        # blueprint / wiki — deferred (§10)
```

## 3. Phase 1 — wholesale copy (no edits)

A single shell script lifts the file set verbatim from
`~/Documents/Lean/VCV-io-freeM-displayed/` to `~/Documents/Lean/PolyFun/`,
flattening `ToMathlib/` and `VCVio/Interaction/` under `PolyFun/`.

```
PolyFun/{P,I,...}/X         ← ToMathlib/{PFunctor,ITree,...}/X
PolyFun/Control/X           ← ToMathlib/Control/X
PolyFun/Logic/X             ← ToMathlib/Logic/X
PolyFun/Interaction/X       ← VCVio/Interaction/X
```

Concrete `cp` lines live in `scripts/port-from-vcvio.sh` (to be authored at
the start of the phase). Use `cp -p` to preserve mtimes.

After this phase:
- `lake update` populates `lake-manifest.json` against `mathlib v4.29.0`.
- `lake build` will fail — namespaces still say `ToMathlib`, `VCVio.Interaction`,
  and `import` lines do not yet resolve.

That is intended. **Do not edit Lean files in this phase.** Commit the raw
copy as a single commit titled e.g. `port: wholesale copy from VCV-io @ <sha>`
so that the rename diff in phase 2 is mechanical and reviewable.

Concrete `cp` script skeleton:

```bash
SRC=~/Documents/Lean/VCV-io-freeM-displayed
DST=~/Documents/Lean/PolyFun

# Layer A: PFunctor
mkdir -p "$DST/PolyFun/PFunctor/Free/Displayed"
mkdir -p "$DST/PolyFun/PFunctor/Chart"
mkdir -p "$DST/PolyFun/PFunctor/Equiv"
mkdir -p "$DST/PolyFun/PFunctor/Lens"
cp -p "$SRC"/ToMathlib/PFunctor/{Basic,Bound,Category,Cofree,MFacts,Trace}.lean \
      "$DST/PolyFun/PFunctor/"
cp -p "$SRC"/ToMathlib/PFunctor/Free/{Basic,Path,Displayed}.lean \
      "$DST/PolyFun/PFunctor/Free/"
cp -p "$SRC"/ToMathlib/PFunctor/Free/Displayed/Decoration.lean \
      "$DST/PolyFun/PFunctor/Free/Displayed/"
cp -p "$SRC"/ToMathlib/PFunctor/Chart/Basic.lean       "$DST/PolyFun/PFunctor/Chart/"
cp -p "$SRC"/ToMathlib/PFunctor/Equiv/Basic.lean       "$DST/PolyFun/PFunctor/Equiv/"
cp -p "$SRC"/ToMathlib/PFunctor/Lens/{Basic,Cartesian,State}.lean \
      "$DST/PolyFun/PFunctor/Lens/"

# Layer B: ITree
mkdir -p "$DST/PolyFun/ITree"/{Bisim,Sim,Events}
cp -p "$SRC"/ToMathlib/ITree/{Basic,Construct,Handler,Rec}.lean "$DST/PolyFun/ITree/"
cp -p "$SRC"/ToMathlib/ITree/Bisim/{Defs,Bind,Equiv}.lean       "$DST/PolyFun/ITree/Bisim/"
cp -p "$SRC"/ToMathlib/ITree/Sim/{Defs,Facts}.lean              "$DST/PolyFun/ITree/Sim/"
cp -p "$SRC"/ToMathlib/ITree/Events/{Exception,State}.lean      "$DST/PolyFun/ITree/Events/"

# Layer C: Interaction
mkdir -p "$DST/PolyFun/Interaction"/{Basic,Concurrent,TwoParty,Multiparty,UC/OpenSyntax}
cp -p "$SRC"/VCVio/Interaction/Basic/*.lean       "$DST/PolyFun/Interaction/Basic/"
cp -p "$SRC"/VCVio/Interaction/Concurrent/*.lean  "$DST/PolyFun/Interaction/Concurrent/"
cp -p "$SRC"/VCVio/Interaction/TwoParty/*.lean    "$DST/PolyFun/Interaction/TwoParty/"
cp -p "$SRC"/VCVio/Interaction/Multiparty/*.lean  "$DST/PolyFun/Interaction/Multiparty/"
# UC: only the generic-friendly files. Excludes Computational, Runtime,
#   Standard, AsyncRuntime, AsyncSecurity, StdDoBridge.
cp -p "$SRC"/VCVio/Interaction/UC/{Interface,OpenProcess,OpenProcessModel,OpenTheory,Emulates,Notation,MachineId,Leakage,EnvAction,EnvOpenProcess,CorruptionModel,MomentaryCorruption}.lean \
      "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/OpenSyntax/{Raw,Interp,Expr}.lean \
      "$DST/PolyFun/Interaction/UC/OpenSyntax/"

# Layer D: Control / Logic helpers
mkdir -p "$DST/PolyFun/Control"/{Comonad,Lawful,Monad}
cp -p "$SRC"/ToMathlib/Control/{Coalgebra}.lean              "$DST/PolyFun/Control/"
cp -p "$SRC"/ToMathlib/Control/Comonad/{Basic,Cofree,Instances}.lean \
      "$DST/PolyFun/Control/Comonad/"
cp -p "$SRC"/ToMathlib/Control/Lawful/Basic.lean             "$DST/PolyFun/Control/Lawful/"
cp -p "$SRC"/ToMathlib/Control/Monad/{Algebra,Hom,Iter,Free,FreeCont,Equiv}.lean \
      "$DST/PolyFun/Control/Monad/"

mkdir -p "$DST/PolyFun/Logic"
cp -p "$SRC"/ToMathlib/Logic/HEq.lean   "$DST/PolyFun/Logic/"
```

Sanity check after copy: `find PolyFun -name '*.lean' | wc -l` should land
around 95 files, and `wc -l PolyFun/**/*.lean` total around 22-25 kloc.

## 4. Phase 2 — namespace rename

Mechanical pass. Purely textual; no semantic edits.

### 4.1 Module-path rewrites in `import` lines

```
ToMathlib.PFunctor              → PolyFun.PFunctor
ToMathlib.ITree                 → PolyFun.ITree
ToMathlib.Control.Coalgebra     → PolyFun.Control.Coalgebra
ToMathlib.Control.Comonad       → PolyFun.Control.Comonad
ToMathlib.Control.Lawful.Basic  → PolyFun.Control.Lawful.Basic
ToMathlib.Control.Monad.Algebra → PolyFun.Control.Monad.Algebra
ToMathlib.Control.Monad.Hom     → PolyFun.Control.Monad.Hom
ToMathlib.Control.Monad.Iter    → PolyFun.Control.Monad.Iter
ToMathlib.Control.Monad.Free    → PolyFun.Control.Monad.Free
ToMathlib.Control.Monad.FreeCont→ PolyFun.Control.Monad.FreeCont
ToMathlib.Control.Monad.Equiv   → PolyFun.Control.Monad.Equiv
ToMathlib.Logic.HEq             → PolyFun.Logic.HEq
VCVio.Interaction               → PolyFun.Interaction
```

Implement as a single `perl -pi` (or `sed -i`) sweep over every `.lean` file
under `PolyFun/` and every consumer in `VCVio/` and `ArkLib/`. Encapsulate
in `scripts/rename-namespaces.sh`.

### 4.2 In-file `namespace`/`open` rewrites

Same mapping above, applied to bare `namespace` / `end <namespace>` /
`open <namespace>` / `open ... in` lines. The `namespace VCVio` /
`namespace Interaction` blocks need particular care — VCVio currently
*sometimes* uses `namespace Interaction` directly under top-level, and
*sometimes* uses `namespace VCVio.Interaction`. Audit:

```
rg '^(namespace|end) (VCVio|Interaction|ToMathlib|PFunctor|ITree)' \
   ~/Documents/Lean/VCV-io-freeM-displayed/{ToMathlib,VCVio/Interaction}
```

before the rename so the script does the right thing in both cases.

### 4.3 Things NOT to rename

- `PFunctor` (mathlib namespace); only the *containing* namespace `ToMathlib`
  changes.
- `Mathlib.*`, `Std.*`, `Init.*`, `Batteries.*` — left alone.
- Module-internal namespaces under each file (`Spec.Decoration.*`,
  `PFunctor.FreeM.Displayed.*`, etc.) — those don't change because the
  qualified prefix sits one level higher.

### 4.4 Documentation strings

Run a docstring sweep:

```
rg -l 'ToMathlib|VCVio\.(Interaction|OracleComp|EvalDist|CryptoFoundations)' \
   PolyFun/PolyFun/
```

Update prose references to point to the new locations. In particular,
`Sampler.lean`'s docstrings mention `ProbComp` / `OracleComp` only as
examples; rephrase to "any monad `m` (e.g., your favorite probability
monad)" so the file is honestly monad-generic.

### 4.5 `EnvAction.lean` generalization

Currently:

```lean
import VCVio.OracleComp.ProbComp
...
structure EnvAction (Event : Type) (X : Type) where
  react : Event → X → ProbComp X := fun _ x => pure x
```

Generalized:

```lean
universe u v
structure EnvAction (m : Type u → Type v) (Event : Type u) (X : Type u) where
  react : Event → X → m X
```

The default `:= fun _ x => pure x` can stay, gated on `[Pure m]`. Update
`EnvOpenProcess.lean`, `CorruptionModel.lean`, `MomentaryCorruption.lean`
call sites (likely a `m := ProbComp` instantiation appears somewhere in
VCVio and not in PolyFun itself).

### 4.6 Generated import aggregator

Author `scripts/mk_all.py` to walk `PolyFun/PolyFun/` and emit `PolyFun.lean`
with one `import PolyFun.X.Y.Z` line per source. Mirrors mathlib's `Mathlib.lean`.

## 5. Phase 3 — first green build of PolyFun

- `lake exe cache get` (mathlib cache).
- `lake build` from a clean `.lake/`.
- Expected: zero errors, possibly a small handful of warnings around
  long files / unused simp args. Fix any `import VCVio.…` stragglers caught
  by the build.
- Fix the `Sampler.lean` docstring references in case the rename script
  missed them.
- CI smoke: a minimal `.github/workflows/ci.yml` that runs `lake exe cache
  get && lake build`. Optional in the first PR.
- First commit on PolyFun's `main`: `feat: initial wholesale port from
  VCV-io @ <vcvio-sha>` (this should be a separate commit from the
  namespace rename so reviewers can diff each phase independently).

## 6. Phase 4 — VCVio side: delete the moved code, depend on PolyFun

In the VCV-io worktree:

1. Add `polyfun` as a `require` in `lakefile.lean`:

   ```lean
   require polyfun from git
     "https://github.com/Verified-zkEVM/PolyFun" @ "<sha>"
   ```

   (Or eventually a `v0.1.0` tag once we tag.)

2. Delete the moved files:
   - `ToMathlib/PFunctor/`, `ToMathlib/ITree/`
   - `ToMathlib/Logic/HEq.lean`
   - The Layer-D Control files moved
   - `VCVio/Interaction/Basic/` *except* whatever genuinely needs to remain
     as a thin VCVio facade (likely none — the whole subtree moves)
   - `VCVio/Interaction/{Concurrent,TwoParty,Multiparty}/`
   - The portable `UC/` files

3. In the surviving 6 UC files (`Computational`, `Runtime`, `Standard`,
   `AsyncRuntime`, `AsyncSecurity`, `StdDoBridge`), rewrite their imports:

   ```
   VCVio.Interaction.UC.Emulates       → PolyFun.Interaction.UC.Emulates
   VCVio.Interaction.UC.OpenProcess    → PolyFun.Interaction.UC.OpenProcess
   VCVio.Interaction.UC.OpenProcessModel → PolyFun.Interaction.UC.OpenProcessModel
   ```

   plus the namespaces inside.

4. `lake build` VCVio. Fix anything that didn't translate cleanly.

5. Single VCVio PR titled `chore: depend on PolyFun for generic
   PFunctor/ITree/Interaction layer`.

## 7. Phase 5 — ArkLib side: re-target imports

ArkLib has a small surface (verified by `rg '^import VCVio\.'`):

```
ArkLib/Interaction/Reduction.lean        → uses VCVio.Interaction.Basic.Spec
                                            + VCVio.Interaction.TwoParty.Compose
ArkLib/Interaction/RoleChain.lean        → ditto
ArkLib/Interaction/FiatShamir/Basic.lean → VCVio.Interaction.TwoParty.Strategy
ArkLib/Interaction/Oracle/Spec.lean      → Basic.{Spec,Append} + TwoParty.Strategy
ArkLib/Interaction/Oracle/VerifierAccess.lean → Basic.BundledMonad + OracleComp
ArkLib/Interaction/Oracle/Core.lean      → TwoParty.Refine
ArkLib/Interaction/Oracle/Execution.lean → OracleComp.SimSemantics.SimulateQ
ArkLib/Interaction/Security/Basic.lean   → OracleComp.ProbComp
ArkLib/ProofSystem/Sumcheck/Interaction/Defs.lean → Basic.Replicate + TwoParty.Compose
ArkLib/OracleReduction/Prelude.lean      → OracleComp.Constructions.SampleableType
```

Rewrite:
- All `VCVio.Interaction.*` → `PolyFun.Interaction.*`.
- All `VCVio.OracleComp.*` *stay* as `VCVio.OracleComp.*`.

ArkLib also needs to add `polyfun` to its `lakefile.toml`:

```toml
[[require]]
name = "polyfun"
git = "https://github.com/Verified-zkEVM/PolyFun"
rev = "<sha>"
```

`VCVio` already transitively pulls PolyFun, so this require is technically
redundant in ArkLib *until* VCVio bumps; but adding it explicitly is the
safer pattern (per mathlib convention) and avoids a ghost transitive dep.

## 8. Risks and footguns

1. **Lake module-style imports.** Many `ToMathlib/PFunctor` files use `module`
   + `public import` (see `ToMathlib/PFunctor/Basic.lean`). Confirm Lean 4.29
   support for the module system is the same in PolyFun's standalone build
   environment (it should be — same toolchain — but verify on phase 3
   first build).

2. **`Mathlib.Probability.ProbabilityMassFunction.Monad` import in
   `Control/Monad/Hom.lean`.** Inspect whether the PMF instance is actually
   used by anything we move. If no, drop it; if yes, accept the dep
   (mathlib is our sole require, so PMF is in scope).

3. **`Control/Monad/Algebra.lean` imports `Mathlib.Order.CompleteLattice.Basic`.**
   Fine (mathlib is a require), but flag in case we later want a thinner
   `polyfun-core` slice without mathlib's order theory pulled in.

4. **Universe variable drift.** During the rename, `universe u v w` lines at
   file tops should not be touched. Spot-check a handful after the sweep.

5. **`@[match_pattern]` and `@[reducible]` attributes.** Critical for
   `Spec.done`, `Spec.node` to keep working as both terms and patterns.
   These are syntactic and should survive a textual rename, but verify
   with one `rg @\[match_pattern\]` after-the-fact.

6. **`Spec`-namespaced wrappers.** The active in-flight cutover plan in
   the VCV-io worktree (see `PFUNCTOR-FIRST-CUTOVER-NEVER-COMMIT.md`) is
   *deleting* `Spec.Decoration` / `Spec.replicate` / `Spec.stateChain`
   wrappers in favor of generic `PFunctor.FreeM.…` versions. **Finish that
   cutover before porting**, otherwise the porting diff will collide with
   the cutover diff in the same files.

7. **`Sampler.lean` and `SpecFintype.lean`.** Both move; both have
   `ProbComp`/`OracleComp` mentions only in docstrings. Scrub on the
   rename pass.

8. **Stale ToMathlib aggregator.** `VCV-io-freeM-displayed/ToMathlib.lean`
   currently imports a broad set of files. After phase 4's deletions, that
   aggregator must be regenerated to drop the moved imports. Keep an eye
   on CI.

9. **Doc-gen / blueprint.** PolyFun ships without blueprint or docs in v0.
   Hold off until we have actual user-facing API docs to host.

## 9. Acceptance criteria (per phase)

| Phase | Pass condition                                                                                       |
|-------|------------------------------------------------------------------------------------------------------|
| 1     | `find PolyFun/PolyFun -name '*.lean' \| wc -l` ≈ 100; no semantic edits.                             |
| 2     | `rg -l 'ToMathlib\.\|VCVio\.Interaction' PolyFun/PolyFun` returns nothing.                           |
| 3     | `lake build` clean from a fresh `.lake/`; smoke `#check PolyFun.Interaction.Spec` compiles; CI green.|
| 4     | VCVio `lake build` clean; deleted-file count ≈ 95; remaining UC files still build.                   |
| 5     | ArkLib `./scripts/validate.sh` clean.                                                                |

## 10. Deferred / out of scope

- **Strategy cluster slim-down** (`Spec.Strategy.{Plain,syntax,interaction,
  run,mapOutput,comp,compFlat,splitPrefix,iterate,stateChainComp,
  monadicSyntax,monadicInteraction}` plus `Spec.Chain`) — explicitly parked
  per user direction in `PFUNCTOR-FIRST-CUTOVER-NEVER-COMMIT.md` §10. Move
  as-is now; refactor later.
- **Blueprint / docs site.** Not in v0.
- **Bas-collaborated interaction work.** Coordinate after the wholesale port
  lands; do not pre-merge on speculation.
- **Removing the `EnvAction.lean` ProbComp leak.** *Will* happen at port
  time per §4.5; not deferred.

## 11. PR / commit shape

PolyFun side, three-PR cadence:
- **PR 1** (scaffolding): `lakefile.toml`, `lean-toolchain`,
  `lake-manifest.json`, `README.md`, `LICENSE`, this `PORTING-PLAN.md`,
  empty `PolyFun.lean`. **Already prepared on `main` worktree.**
- **PR 2** (repo hygiene): top-level docs, scripts, and CI workflows
  per §13. Sequenced *before* the wholesale port so that PR 3's diff
  shows up in CI from day one.
- **PR 3** (the actual port): wholesale copy + namespace rename, in two
  commits within one PR (phase 1 and phase 2 separately for review
  legibility).

VCVio side, one PR:
- `chore: depend on PolyFun; delete moved code` — phase 4 in a single
  reviewable diff.

ArkLib side, one PR (after VCVio merges):
- `chore: re-target VCVio.Interaction.* imports to PolyFun.*`.

That's five PRs total across three repos, executed in series.

## 12. Post-merge

- Tag `polyfun v0.1.0` once the three PRs land green and downstream is
  stable for ≥ 1 day.
- Ping Bas on Zulip with the link.
- Add a topic line to GitHub: `lean4 polynomial-functors interaction-trees
  mathlib4 process-calculus open-systems`.

## 13. Repo hygiene — CI, scripts, top-level docs

PolyFun should ship with the same operational rigor as VCVio and ArkLib
from day one. This section enumerates *exactly* which files in the
sibling repos to port, adapt, or skip, and the rationale for each.

Source trees inspected:
- `~/Documents/Lean/VCV-io-freeM-displayed/.github/`,
  `~/Documents/Lean/VCV-io-freeM-displayed/scripts/`
- `~/Documents/Lean/ArkLib-Refactor/.github/`,
  `~/Documents/Lean/ArkLib-Refactor/scripts/`

### 13.1 GitHub workflows (`.github/workflows/`)

| File                     | Source             | Action       | Notes                                                                                                                  |
|--------------------------|--------------------|--------------|------------------------------------------------------------------------------------------------------------------------|
| `ci.yml`                 | ArkLib (295 lines) | **adapt**    | Drop the timing-baseline machinery for v0; keep `lake exe cache get && lake build` plus a `validate.sh` invocation.   |
| `linting.yml`            | VCVio (47 lines)   | **port**     | Uses `leanprover-community/lint-style-action`. Update path globs to `PolyFun/**/*.lean`.                              |
| `check-imports.yml`      | ArkLib (21 lines)  | **port**     | Trivial — runs `./scripts/check-imports.sh`.                                                                          |
| `release-tag.yml`        | both (identical)   | **port**     | Auto-tags on `lean-toolchain` bumps via `leanprover-community/lean-release-tag@v4.18804.0`.                           |
| `update.yml`             | ArkLib (38 lines)  | **port**     | Weekly mathlib auto-update PR via `leanprover-community/mathlib-update-action`. Universal Lean repo pattern.          |
| `summary.yml`            | both (identical)   | **port**     | Gemini-backed PR summary. Requires `GEMINI_API_KEY` repo secret; coordinate with Verified-zkEVM org.                  |
| `review.yml`             | both (identical)   | **port**     | Auto-review on PR open; only fires for OWNER/MEMBER/COLLABORATOR.                                                     |
| `agent-docs.yml`         | VCVio (19 lines)   | **skip**     | Validates `docs/agents/` — none in PolyFun v0.                                                                        |
| `interop-isolation.yml`  | VCVio (30 lines)   | **skip**     | Specific to VCVio's Hax/Aeneas TCB isolation.                                                                         |
| `docs.yml`               | ArkLib (89 lines)  | **skip**     | Doc-gen / blueprint; deferred per §10.                                                                                |
| `docs-integrity.yml`     | ArkLib (22 lines)  | **skip**     | Same; the script it calls (`check-docs-integrity.py`) is also skipped.                                                |
| `build.yml`              | VCVio (315 lines)  | **skip**     | Superseded by ArkLib-style `ci.yml`.                                                                                  |

### 13.2 Scripts (`scripts/`)

| File                       | Source             | Action         | Notes                                                                                                          |
|----------------------------|--------------------|----------------|----------------------------------------------------------------------------------------------------------------|
| `lint-style.py`            | both (synced)      | **port**       | Mathlib-derived per-file style linter. Self-contained Python.                                                  |
| `lint-style.sh`            | both (synced)      | **port**       | Wrapper.                                                                                                       |
| `print-style-errors.sh`    | VCVio              | **port**       | Used by `linting.yml` and `lint-style.sh`.                                                                     |
| `style-exceptions.txt`     | both               | **start empty**| Per-file lint waivers; PolyFun starts clean.                                                                   |
| `nolints-style.txt`        | VCVio              | **start empty**| Companion ignore list.                                                                                         |
| `requirements.txt`         | VCVio              | **port**       | Python deps for the linter (`tomli`, `pyyaml`, etc.). Verify minimal set.                                      |
| `update-lib.sh`            | ArkLib             | **adapt**      | Regenerates `PolyFun.lean` from tracked `PolyFun/**/*.lean`. One-line path swap from ArkLib version.           |
| `check-imports.sh`         | ArkLib             | **adapt**      | Verifies the aggregator is in sync. Same one-line path swap.                                                   |
| `validate.sh`              | ArkLib             | **adapt**      | Convenience wrapper: `lake build` + warning check + `check-imports.sh` + style lint. Trim ArkLib-specific kb/docs hooks. |
| `mk_all.py` or equivalent  | new                | **author**     | If we choose Python for the aggregator (cleaner than `update-lib.sh`'s shell). Pick one and delete the other. |
| `port-from-vcvio.sh`       | new                | **author**     | One-shot phase-1 wholesale copy (skeleton in §3).                                                              |
| `rename-namespaces.sh`     | new                | **author**     | Phase-2 mechanical sed/perl pass.                                                                              |
| `build-project.sh`         | VCVio              | **skip**       | VCVio-specific (builds `Examples/`).                                                                           |
| `build_timing_report.sh`   | ArkLib             | **skip**       | Timing harness; unneeded in v0.                                                                                |
| `check-warning-log.py`     | both               | **defer**      | Useful but not v0-blocking. Re-evaluate after first port build.                                                |
| `check-agent-docs.py`      | VCVio              | **skip**       | No agent docs in v0.                                                                                           |
| `extract-doc-fragments.py` | VCVio              | **skip**       | Same.                                                                                                          |
| `pr-summary.py`            | VCVio              | **skip**       | Local helper; CI uses the action.                                                                              |
| `review.py`                | VCVio              | **skip**       | Same.                                                                                                          |
| `check-interop-isolation.sh` | VCVio            | **skip**       | VCVio-specific.                                                                                                |
| `check-docs-integrity.py`  | ArkLib             | **skip**       | Blueprint integrity; deferred.                                                                                 |
| `inject_nav.py`, `revert_nav.py`, `build-web.sh` | ArkLib | **skip** | Docs site; deferred.                                                                                          |
| `kb/`, `dependency_analysis/` | ArkLib          | **skip**       | ArkLib-specific knowledge base / dep graph utilities.                                                          |

### 13.3 Top-level markdown

| File              | Source action                                                                                                                                                                  |
|-------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `README.md`       | already drafted (matches the agreed description).                                                                                                                              |
| `LICENSE`         | already shipped (Apache-2.0).                                                                                                                                                  |
| `AGENTS.md`       | adapt VCVio's 194-line version. Trim crypto-specific sections (no `OracleComp`, `evalDist`, lattice crypto). Keep: header / docstring policy, lean module layering rules, naming conventions, the "Section Headers Within A File" guidance. Add: PolyFun-specific module DAG (§13.5). |
| `CLAUDE.md`       | symlink to `AGENTS.md` — `ln -s AGENTS.md CLAUDE.md`.                                                                                                                          |
| `CONTRIBUTING.md` | start from VCVio's leaner 106-line version. Update repo references (PolyFun, not VCV-io) and the build commands. Drop VCVio-specific items (`Examples/`, `LatticeCrypto/`, smoke tests). |
| `REFERENCES.md`   | author from scratch with the citations *actually* used in PolyFun: Hancock-Setzer 2000, Altenkirch-Ghani-Hancock-McBride-Morris 2015 ("Indexed Containers"), Spivak-Niu 2024 ("Polynomial Functors: A General Theory of Interaction"), Xia-Zakowski-He-Hur-Malecha-Pierce-Zdancewic 2020 ("Interaction Trees"), Escardó-Oliva 2023, McBride 2010 + Dagand-McBride 2014 (displayed algebras / ornaments). These appear in module docstrings already; centralize them. |
| `ROADMAP.md`      | optional; defer. No public roadmap commitments yet beyond §10.                                                                                                                 |
| `BACKGROUND.md`   | skip; ArkLib's 12-line stub is not worth porting.                                                                                                                              |
| `PORTING.md`      | not the same as our `PORTING-PLAN.md` (ArkLib's `PORTING.md` documents Mathlib porting workflow; ours documents this one-time PolyFun split). Skip.                            |

### 13.4 `.github/dependabot.yml`

Port verbatim from ArkLib. Configures monthly GitHub Actions version
bumps. Single-file change.

### 13.5 PolyFun-specific module-layering DAG (for `AGENTS.md`)

```
PFunctor/{Basic, Bound, MFacts, Equiv, Chart, Lens}
  → PFunctor/{Cofree, Trace}
  → PFunctor/Free/{Basic, Path}
  → PFunctor/Free/{Displayed, Displayed/Decoration}
  → ITree/{Basic, Construct, Handler, Rec, Events, Sim, Bisim}
  → Control/{Coalgebra, Comonad, Lawful, Monad}
  → Interaction/Basic/{Spec, Node, Decoration, Syntax, Shape, Interaction,
                       Strategy, Append, Replicate, StateChain, Chain,
                       Telescope, Sampler, MonadDecoration, BundledMonad,
                       Ownership, SpecFintype}
  → Interaction/{TwoParty, Multiparty, Concurrent}
  → Interaction/UC/{Interface, OpenProcess, OpenProcessModel, OpenTheory,
                    OpenSyntax, Notation, Emulates, MachineId, EnvAction,
                    EnvOpenProcess, CorruptionModel, MomentaryCorruption,
                    Leakage}
```

Document this in `AGENTS.md` as the canonical layering. Imports flow
strictly downward; cycles are a build error.

### 13.6 Phasing of repo-hygiene work

Per §11, repo hygiene lands in PR 2, *between* the scaffolding PR (PR 1)
and the wholesale port (PR 3). Reasons:

1. CI must be live before PR 3 hits, so reviewers see green on the
   ~25 kloc port at first push.
2. The lint-style infrastructure must be in place before any moved file
   triggers it.
3. The `update-lib.sh` / `check-imports.sh` pair must exist before the
   port, otherwise `PolyFun.lean`-aggregator drift can sneak in
   undetected.
4. The auto-update workflow (`update.yml`) is genuinely useful from
   commit one — it keeps the mathlib pin from rotting between PR 2 and
   PR 3.

PR 2 contents (concrete file list):
- `AGENTS.md`, `CLAUDE.md` (symlink), `CONTRIBUTING.md`, `REFERENCES.md`
- `.github/dependabot.yml`
- `.github/workflows/{ci,linting,check-imports,release-tag,update,summary,review}.yml`
- `scripts/{lint-style.py,lint-style.sh,print-style-errors.sh,style-exceptions.txt,nolints-style.txt,requirements.txt,update-lib.sh,check-imports.sh,validate.sh}`

PR 2 commit message: `chore: bootstrap CI, scripts, and repo docs`.
