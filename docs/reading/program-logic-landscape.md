# Program-Logic Landscape and PolyFun's Core

Status: design memo for the program-logic core (2026-08). Companion wiki page:
[`docs/wiki/program-logic.md`](../wiki/program-logic.md).

## The problem

VCVio carries a mature (18k-line, sorry-free) program logic over `OracleComp`
— unary and relational, with its own `vcgen`/`rvcgen` tactic family — but its
foundations are split across three competing assertion substrates, and PolyFun,
the layer everything sits on, historically contributed only
`Control/Monad/Algebra.lean`. This memo records the landscape, the architecture
decision, and the resulting PolyFun core.

## The three substrates

| Substrate | Assertions | Status | Consumers |
|---|---|---|---|
| Core `Std.Do` / `mvcgen` (Lean ≥ 4.22) | `SPred`/`PostShape` (Prop-based), `WP m ps`, `@[spec]`, `mvcgen`; `mvcgen'` (SymM) in development | Upstream, moving fast | VCVio via a narrow bridge (`StdDoBridge`, `HandlerSpecs`, `WriterTBridge`), almost-sure view only |
| Loom2 `Std.Do'` (fork of verse-lab/loom, POPL 2026, DOI 10.1145/3776719) | Lattice-generic `WP m Pred EPred`, any `CompleteLattice`, `EPost`, relational APIs, own `mvcgen'` | Fork pinned by SHA, VCVio-maintained | VCVio's main ProgramLogic: ℝ≥0∞ / Prop / Prob carriers, pRHL + eRHL |
| Iris/BI (Bluebell, POPL 2025, DOI 10.1145/3704894) | `HyperAssertion` over indexed probability-space × permission resources, `BIBase`, joint-conditioning modality | Branch-only in VCVio (`Ferinko/measureMySpace` line, Lean 4.24) and the org's iris-lean fork | Nethermind's Bluebell mechanization effort |

Downstream of VCVio, ArkLib is a *greenfield* consumer: it uses none of the
program logic today (its pin predates the layer), but its security definitions
are literally quantitative Hoare triples over `OptionT (OracleComp …)`, its
highest-leverage open gap is the additive-error sequencing rule for sequential
composition, and its completeness proofs want a grind-friendly support /
never-fails calculus.

## The unifying observation

`MAlgOrdered` — ordered monad algebras over a complete lattice — is the common
semantic kernel: core `Std.Do`'s `PredTrans` is the Prop/SPred special case,
Loom2's `Std.Do'.WP` is the lattice-generic version VCVio consumes (its
quantitative carrier bridges to `MAlgOrdered` by `rfl`), and Bluebell's `wp` is
a BI-valued sibling. PolyFun therefore owns the *handler/algebra-parameterized*
theory over the polynomial substrate, and each downstream picks its carrier.
PolyFun takes no Loom2 or Iris dependency and does not pick between the
substrates; core `Std.Do` is used only behind a two-file quarantine.

## The core (implemented)

- `Control/Monad/Algebra.lean` — the pre-existing kernel: `MAlgOrdered`,
  `wp`/`Triple`, transformer lifts, honest `wpExc`/`wpOpt`.
- `Control/Monad/Algebra/Relational.lean` — `MAlgRelOrdered` (relational
  `rwp`/`RelWP`/`Triple`, asynchronous bind rules, `StrictBind`, `Anchored`),
  upstreamed from VCVio's `ToMathlib/Control/Monad/RelationalAlgebra.lean`
  (near-verbatim; three unused `LawfulMonad` binders dropped).
- `Control/Monad/Support.lean` — `MonadSupport`: a monad with a canonical
  set-valued support, bundled as a monad morphism `supportHom : m →ᵐ SetM` into
  Mathlib's powerset monad (there is **no** upstream abstraction for this; the
  ad-hoc idiom is `[MonadLiftT m SetM]`, with documented diamond pitfalls).
  `supportM`, the `AllOutputs`/`SomeOutput`/`NoOutput` judgments with scoped
  `⊨ₐ`/`⊨ₛ`/`⊭` notation, the demonic `MAlgOrdered m Prop` instance, and
  failure-transformer instances. `StateT`/`ReaderT` deliberately have no
  instance (union over initial states is not a monad morphism).
- `PFunctor/Free/Support.lean` — the canonical `MonadSupport (FreeM P)`:
  fold every operation to `Set.univ`; coherence with `Free/Path.lean`
  (`supportM_eq_range_output`).
- `PFunctor/Free/WP.lean` — `OpSpec` per-operation predicate-transformer
  specs; the syntactic fold `FreeM.wpFold` with `demonic`/`angelic` `Prop`
  specs; `OpSpec.toMAlgOrdered`; the semantic `FreeM.wpVia` through a
  `Handler`; soundness `wpFold_le_wpVia` / `wpFold_eq_wpVia` (the generic
  engine behind VCVio's `HandlerSpecs` pattern); coherence of demonic/angelic
  folds with `AllOutputs`/`SomeOutput`.
- `Control/Do/Basic.lean` + `PFunctor/Free/Do.lean` — the core-`Std.Do`
  quarantine: `MonadHom.transportWP(Monad)`, `MonadSupport.toWP(Monad)`,
  scoped demonic `WP (FreeM P) .pure` instances, and the `Spec.lift` `@[spec]`
  lemma; `mvcgen` decomposes `do`-programs over `FreeM` with uninterpreted
  operations (`PolyFunTest/Do/FreeM.lean` proves this in CI). Only these two
  files (plus tests) may import `Std.Tactic.Do`.

## Deliberately not in PolyFun

Anything importing loom2/`Std.Do'`; all probability (`evalDist`/SPMF,
ℝ≥0∞/Prob carriers, couplings, pRHL/eRHL); concrete handler specs
(caching/logging/seeded oracles); the `vcgen`/`@[vcspec]` tactic family;
Bluebell/iris-lean/BI; global `WP` instances for `FreeM` (they would race
downstream registrations on reducible unfoldings such as `OracleComp`).

## Downstream migration sketch (VCVio, at its next PolyFun bump)

1. Replace `ToMathlib/Control/Monad/RelationalAlgebra.lean` with the PolyFun
   import.
2. Re-derive `support` from `MonadSupport` (its `instMonadLiftTSetM` becomes
   `MonadSupport.toMonadLiftT`; `allOutputsSatisfy`/`someOutputSatisfies`
   become deprecated aliases of `AllOutputs`/`SomeOutput` during migration),
   and `HoarePropTriple.instMAlgOrdered` from the generic demonic instance.
3. Re-derive `instWPOracleComp` from `MonadSupport.toWP` and
   `simulateQ_triple_preserves_invariant`-style facts from
   `wpFold_le_wpVia`; keep `wpProp_iff_forall_support` as the only
   probability-touching step, and `wp_eq_mAlgOrdered_wp` as the rfl regression
   test for the quantitative carrier.

Acceptance targets: VCVio's support instances become one-liners; ArkLib (once
its pin catches up) can delete `ToVCVio/DistEq.lean`, derive its Merkle
`NeverFail` calculus from `supportM_bind`-shaped rules, and state
`append_completeness` against a future generic approximate-triple algebra
(`pre ≤ wp x post + ε` over a lattice-with-addition carrier — sketched, not yet
implemented).

## Open follow-ups

- Relational free-monad layer: a two-tree `rwpFold` giving
  `MAlgRelOrdered (FreeM P) (FreeM Q) l` from a relational op-spec.
- `Display`/wp adequacy: `Display.ofPredicates` sections versus `wpFold` of
  the induced spec — the intrinsic/extrinsic bridge (roadmap track D5).
- ITree: no `WP` instance planned while `iter` is lawful only up to weak
  bisimulation; the honest deliverables are wp-congruence under `WeakBisim`
  and an invariant rule for the `ITree/Do.lean` `ForIn` loop.
- The ε-additive approximate-triple algebra (ArkLib's sequencing blocker).
- Optional `MonadFinSupport` (Finset-valued support, generalizing VCVio's
  `HasEvalFinset`).
