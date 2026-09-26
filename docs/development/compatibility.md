# Compatibility and deprecation

PolyFun is consumed by pinned downstream projects (VCVio, ArkLib). A renamed module or declaration
therefore ships with a compatibility surface for a bounded period, so that a consumer can bump its pin
first and migrate names afterwards, one warning at a time.

## Policy

- **Modules.** When a module moves, the old path stays as a *shim*: a file whose only content is one
  `public import` of the replacement, a module docstring naming both paths, and a
  `deprecated_module "…" (since := "YYYY-MM-DD")` command. Lean warns at every import of the shim
  and names the replacement. Shims carry no declarations and are never imported inside PolyFun; the
  generated umbrella imports them with Lean's per-import `-- deprecated_module: ignore` suffix,
  which `./scripts/update-lib.sh` adds automatically and `./scripts/check-modules.sh` verifies.
- **Declarations.** A renamed declaration keeps a `@[deprecated newName (since := "YYYY-MM-DD")]
  alias`, placed next to the canonical declaration, and an aggregate module such as
  `PolyFun/PFunctor/Deprecated.lean` may collect a family of aliases. Namespaces are not aliased:
  a namespace rename is announced here and migrated by the consumer.
- **Lifetime.** A shim or alias lives for two Lean minor releases: introduced while PolyFun pins
  `v4.N`, it is removed in the PR that bumps PolyFun to `v4.(N+2)`. The removal PR checks the
  recorded downstream surface (`scripts/check-downstream-surface.py`, once it exists) and may retain
  an entry that a tracked consumer still uses, recording the new removal target below.
- **Every rename PR** adds the shims or aliases, adds a row to the tables below, and updates the
  owning guide. Regressions pin the compatibility surface:
  `PolyFunTest/ModuleAPI/DeprecatedModules.lean` (`#show_deprecated_modules`) and
  `PolyFunTest/PFunctor/{Lens,Equiv}/DeprecatedCompatibility.lean` (`#guard_msgs` on the alias
  warnings).
- Shim docstrings and this page are the one place where a removed or renamed name is written down;
  ordinary docstrings stay intrinsic, as [CONTRIBUTING.md](../../CONTRIBUTING.md) requires.
- Consumers should pin a PolyFun release tag (`v4.N.0`, cut by `.github/workflows/release-tag.yml`
  whenever `lean-toolchain` changes on `main`) or a commit, not `main`.

## Breaking changes by release

| Introduced at | Change | Compatibility surface |
|---|---|---|
| v4.34 (2026-09-17, #241) | `PolyFun/Interaction/UC/**` split into `Interaction/Execution/**`, `Interaction/Open/**` and `Interaction/Interface.lean`; namespace `Interaction.UC` became `Interaction.Open` and `Interaction.Execution.*` | module shims below; no namespace aliases |
| v4.34 (2026-09-19, #243) | library `PolyFunCslib` became `ComplexityBackends`; `ToCslib/Computability/**` moved to `ComplexityBackends/CslibSingleTape/**`; namespaces `ToCslib.Computability.*` and `PFunctor.CslibPPoly` became `ComplexityBackends.CslibSingleTape.*` | none (a shim would make `ToCslib` import a backend, which the layering forbids); migrate imports directly |
| v4.33 (2026-08-17) | polynomial algebra respelled from `X` to `y` (`PFunctor.X`, `X^`, `p ^ n`) | `@[deprecated]` aliases in `PolyFun/PFunctor/Deprecated.lean`, removable at v4.35 unless a tracked consumer still needs them |

## Module shims

| Deprecated module | Replacement | Since | Removable at |
|---|---|---|---|
| `PolyFun.Interaction.UC.ActivationObservation` | `PolyFun.Interaction.Open.ActivationObservation` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.CorruptionModel` | `PolyFun.Interaction.Open.CorruptionModel` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.Emulates` | `PolyFun.Interaction.Open.Emulates` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.EmulatesQuotient` | `PolyFun.Interaction.Open.EmulatesQuotient` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.EmulatesWithin` | `PolyFun.Interaction.Open.EmulatesWithin` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.EnvAction` | `PolyFun.Interaction.Open.EnvAction` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.EnvOpenProcess` | `PolyFun.Interaction.Open.EnvOpenProcess` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.GlobalSubroutine` | `PolyFun.Interaction.Open.GlobalSubroutine` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.Interface` | `PolyFun.Interaction.Interface` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.Leakage` | `PolyFun.Interaction.Open.Leakage` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.MomentaryCorruption` | `PolyFun.Interaction.Open.MomentaryCorruption` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.Notation` | `PolyFun.Interaction.Open.Notation` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenProcessCoherence` | `PolyFun.Interaction.Open.OpenProcessCoherence` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenProcessFactorization` | `PolyFun.Interaction.Open.OpenProcessFactorization` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenProcessInterleave` | `PolyFun.Interaction.Open.OpenProcessInterleave` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenProcess` | `PolyFun.Interaction.Open.OpenProcess` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenProcessModel` | `PolyFun.Interaction.Open.OpenProcessModel` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenProcessQuotient` | `PolyFun.Interaction.Open.OpenProcessQuotient` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenProcessSamplerCoherence` | `PolyFun.Interaction.Open.OpenProcessSamplerCoherence` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenProcessSamplerEquiv` | `PolyFun.Interaction.Open.OpenProcessSamplerEquiv` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenProcessSamplerFactorization` | `PolyFun.Interaction.Open.OpenProcessSamplerFactorization` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenSyntax.AtomSubTheory` | `PolyFun.Interaction.Open.OpenSyntax.AtomSubTheory` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenSyntax.Expr` | `PolyFun.Interaction.Open.OpenSyntax.Expr` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenSyntax.Interp` | `PolyFun.Interaction.Open.OpenSyntax.Interp` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenSyntax.Raw` | `PolyFun.Interaction.Open.OpenSyntax.Raw` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenTheory.Congruence` | `PolyFun.Interaction.Open.OpenTheory.Congruence` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenTheory.Family` | `PolyFun.Interaction.Open.OpenTheory.Family` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenTheory` | `PolyFun.Interaction.Open.OpenTheory` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenTheory.PlugFactorization` | `PolyFun.Interaction.Open.OpenTheory.PlugFactorization` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.OpenTheory.Quotient` | `PolyFun.Interaction.Open.OpenTheory.Quotient` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.Assembly` | `PolyFun.Interaction.Execution.ReactiveNetwork.Assembly` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.Behavior` | `PolyFun.Interaction.Execution.ReactiveNetwork.Behavior` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.Budget` | `PolyFun.Interaction.Execution.ReactiveNetwork.Budget` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.Diagram` | `PolyFun.Interaction.Execution.ReactiveNetwork.Diagram` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.Factorization` | `PolyFun.Interaction.Execution.ReactiveNetwork.Factorization` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.Factorization.Right` | `PolyFun.Interaction.Execution.ReactiveNetwork.Factorization.Right` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.HandledAssembly` | `PolyFun.Interaction.Execution.ReactiveNetwork.HandledAssembly` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.HandledDiagram` | `PolyFun.Interaction.Execution.ReactiveNetwork.HandledDiagram` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork` | `PolyFun.Interaction.Execution.ReactiveNetwork` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.Serial` | `PolyFun.Interaction.Execution.ReactiveNetwork.Serial` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveNetwork.Transport` | `PolyFun.Interaction.Execution.ReactiveNetwork.Transport` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ReactiveProcess` | `PolyFun.Interaction.Execution.ReactiveProcess` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.Realizability` | `PolyFun.Interaction.Open.Realizability` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.RequestNetwork` | `PolyFun.Interaction.Execution.RequestNetwork` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.RequestNetwork.Serial` | `PolyFun.Interaction.Execution.RequestNetwork.Serial` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.RequestNetwork.Transport` | `PolyFun.Interaction.Execution.RequestNetwork.Transport` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.SamplerObservation` | `PolyFun.Interaction.Open.SamplerObservation` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ScheduledOpenProcessModel` | `PolyFun.Interaction.Open.ScheduledOpenProcessModel` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.ScheduledSamplerFactorization` | `PolyFun.Interaction.Open.ScheduledSamplerFactorization` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.Scheduler` | `PolyFun.Interaction.Open.Scheduler` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.SecureEmulation` | `PolyFun.Interaction.Open.SecureEmulation` | 2026-09-26 | v4.36 |
| `PolyFun.Interaction.UC.SubTheory` | `PolyFun.Interaction.Open.SubTheory` | 2026-09-26 | v4.36 |
