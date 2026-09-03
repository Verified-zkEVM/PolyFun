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
substrates; core's `Std.Internal.Do` stack is the canonical interface, imported only inside
the program-logic kernel (the two-tier quarantine).

## The core (implemented)

- `Control/Monad/Algebra.lean` — the pre-existing kernel: `MAlgOrdered`,
  `wp`/`Triple`, transformer lifts, honest `wpExc`/`wpOpt`.
- `Control/Monad/Algebra/Relational.lean` — `MAlgRelOrdered` (relational
  `rwp`/`RelWP`/`Triple`, asynchronous bind rules, `StrictBind`, `Anchored`, and
  named left/right/both `StateT` and `ReaderT` lifts preserving strict bind),
  upstreamed from VCVio's `ToMathlib/Control/Monad/RelationalAlgebra.lean`
  (near-verbatim; three unused `LawfulMonad` binders dropped).
- `Control/Monad/Algebra/Relational/Support.lean` — production demonic and
  angelic relations obtained from exact support. They quantify universally or
  existentially over the cross product of the two supports, respectively, and
  ship matching `StrictBind` and `Anchored` witnesses as opt-in definitions.
- `Control/Monad/Support.lean` — the support layer, built on Lean core's
  `MonadAttach` (shipped since v4.28; `CanReturn` *is* the support predicate).
  Core proves only the elimination half of the theory, and provably cannot prove
  the rest — a monad with `CanReturn := False` satisfies `LawfulMonadAttach` —
  so PolyFun contributes `ExactMonadAttach`, the two introduction rules, plus
  `MonadAttach.support` (the `Set`-valued view), the
  `AllOutputs`/`SomeOutput`/`NoOutput` judgments with scoped `⊨ₐ`/`⊨ₛ`/`⊭`
  notation, and the named demonic `MAlgOrdered m Prop` choice. Core supplies the
  `Id`/`Option`/`OptionT`/`ExceptT`/`StateT`/`ReaderT` instances; PolyFun adds
  `Except` and `SetM` (absent upstream) and a universe alias working around
  core's `max`-joined `ExceptT` declaration. `StateT`/`ReaderT` keep core's
  canonical support but are correctly not `ExactMonadAttach`.
- `PFunctor/Free/Support.lean` — `MonadAttach`/`ExactMonadAttach` for `FreeM P`
  with a computable, axiom-free `attach` (so `MonadAttach.pbind` is available for
  well-founded recursion); structural equations hold by `rfl`; coherence with
  `Free/Path.lean` (`support_eq_range_output`) and with the powerset fold
  (`support_eq_liftM_univ`).
- `PFunctor/Free/WP.lean` — `OpSpec` per-operation predicate-transformer
  specs; the syntactic fold `FreeM.wpFold` with `demonic`/`angelic` `Prop`
  specs; `OpSpec.toMAlgOrdered`; the semantic `FreeM.wpVia` through a
  `Handler`; soundness `wpFold_le_wpVia` / `wpFold_eq_wpVia` (the generic
  engine behind VCVio's `HandlerSpecs` pattern); coherence of demonic/angelic
  folds with `AllOutputs`/`SomeOutput`.
- `Control/Monad/Algebra/WP.lean`, `Control/Monad/Support/WP.lean`,
  `Control/Monad/Hom/WP.lean` — the bridges to core's lattice-generic stack
  (`Std.Internal.Do`, public as `Std.WP` from v4.35, driven by `vcgen`):
  `MAlgOrdered.toWPMonad` for Mathlib-lattice carriers, the demonic and angelic
  `WPMonad` interpretations of exact support, conjunctivity of the demonic one,
  a mirror of master's `LawfulWPMonadAttach` with `support_subset_of_wp` /
  `allOutputs_of_wp`, and transport along monad morphisms. These are the
  canonical interface; `PolyFunTest/Do/{Algebra,Support}.lean` run `vcgen`
  through them.
- `PFunctor/Free/WP/Upstream.lean` + `PFunctor/Free/Do.lean` — the free monad on the
  canonical stack: `OpSpec.toWPMonad`, `FreeM.wpMonadOfHandler`, scoped demonic and
  angelic instances with `@[spec]` rules for `lift` / `liftBind`, so `vcgen` decomposes
  free programs (`PolyFunTest/Do/{FreeM,Loops,Transport}.lean`).

## Deliberately not in PolyFun

Anything importing loom2/`Std.Do'`; all probability (`evalDist`/SPMF,
ℝ≥0∞/Prob carriers, couplings, pRHL/eRHL); concrete handler specs
(caching/logging/seeded oracles); the `vcgen`/`@[vcspec]` tactic family;
Bluebell/iris-lean/BI; global `WP` instances for `FreeM` (they would race
downstream registrations on reducible unfoldings such as `OracleComp`).

## Downstream migration sketch (VCVio, at its next PolyFun bump)

1. Replace `ToMathlib/Control/Monad/RelationalAlgebra.lean` with the PolyFun
   import.
2. Re-derive `support` as `export MonadAttach (support)` — that single line keeps
   all 1403 `support` occurrences and 212 `support_*` lemma names. `OracleComp`
   (= `OptionT (FreeM …)`) gets `MonadAttach`/`ExactMonadAttach` by pure instance
   composition, needing *no* VCVio-side instance; only `PMF` (via
   `PMF.bindOnSupport`, which is exactly `pbind`), `SPMF`, and `FinRatPMF.Raw`
   need real work, all probability-side. `allOutputsSatisfy`/`someOutputSatisfies`
   become deprecated aliases of `AllOutputs`/`SomeOutput` during migration, and
   `HoarePropTriple.instMAlgOrdered` can select the generic demonic definition
   explicitly.
   Guards: core's `StateT`/`ReaderT` instances make `support` typecheck on stacks
   where `CellRef.lean`/`WriterCost.lean` mean the per-run support, and
   `MonadAttach.trivial` must never be let in.
3. Re-derive `instWPOracleComp` from `MonadAttach.toWP` and
   `simulateQ_triple_preserves_invariant`-style facts from
   `wpFold_le_wpVia`; keep `wpProp_iff_forall_support` as the only
   probability-touching step, and `wp_eq_mAlgOrdered_wp` as the rfl regression
   test for the quantitative carrier.

Acceptance targets: VCVio's support instances become one-liners; ArkLib (once
its pin catches up) can delete `ToVCVio/DistEq.lean`, derive its Merkle
`NeverFail` calculus from `support_bind`-shaped rules, and state
`append_completeness` against a future generic approximate-triple algebra
(`pre ≤ wp x post + ε` over a lattice-with-addition carrier — sketched, not yet
implemented).

## Open follow-ups

- Relational loop rules: `MAlgRelOrdered` lockstep `forIn` / `forM` / `foldlM` rules under
  `StrictBind`, mirroring core's `Spec.forIn'_list` induction; not yet written.
- A `mapM` rule for the judgments (`Hom/Loops.lean` has the morphism form only).
- `try/catch` through core's `ExceptT.instWPMonad` over a PolyFun base: `vcgen` reports
  `No spec found for program tryCatch …` although `Spec.tryCatch_ExceptT` exists at the pin;
  the instance path needs diagnosing before the canary lands.

- Relational free-monad layer: a two-tree `rwpFold` giving
  `MAlgRelOrdered (FreeM P) (FreeM Q) l` from a relational op-spec.
- `Display`/wp adequacy: `Display.ofPredicates` sections versus `wpFold` of
  the induced spec — the intrinsic/extrinsic bridge (roadmap track D5).
- ITree: no `WP` instance planned while `iter` is lawful only up to weak
  bisimulation. The `ForIn` loop rule is now in place —
  `ITree.forInLoop_weakBisim_of_invariant`, a bisimulation congruence carrying the
  invariant inside the state relation, since `ITree` has no possible-output
  predicate for a postcondition to range over. wp-congruence under `WeakBisim`
  remains open.
- `vcgen` on dependent value types: core's `Sym` matcher compares the `Prog`/`Value` slots
  of a spec structurally, so `Spec.lift` misses an operation in tail position once the goal's
  value type is normalized (gotcha 11e). Worth raising upstream: matching those slots up to
  reducible defeq, or reducing structure projections in `unfoldReducible`, would make
  dependently typed operations first-class.
- The angelic WP bridge exists only on the lattice-generic stack
  (`MonadAttach.toWPMonadAngelic`, scoped as `PFunctor.FreeM.AngelicWP`); on the older
  `Std.Do` stack it is **blocked**, not merely unwritten.
  `Std.Do.PredTrans` carries conjunctivity as a structure field, stated as a
  bi-entailment; `AllOutputs` distributes over `∧` both ways but `SomeOutput` only
  left-to-right, so there is no angelic `Std.Do.WP`. The lattice-generic stack makes
  conjunctivity an opt-in `WPConjunctive`, which the angelic instance omits.
  `PolyFunTest/Control/MonadAttach.lean` pins both directions and the failure.
- The ε-additive approximate-triple algebra (ArkLib's sequencing blocker).
- Optional `MonadFinSupport` (Finset-valued support, generalizing VCVio's
  `HasEvalFinset`).

## The `SetM` migration contract

`MonadAttach` is the canonical interface for reachability; the `MonadLiftT m SetM`
spelling is a compatibility shim for a downstream still phrased that way. This section
records what such a downstream needs, so the migration does not have to be re-derived.

**What already exists here.** `MonadAttach.toMonadLiftT` / `toLawfulMonadLiftT`
(`Control/Monad/Support.lean`) are the shim itself — deliberately not instances.
`MonadAttach.SetM.support_eq_run` and `SetM.canReturn_iff` are the carrier bridges.
`support_liftM_subset` plus `allOutputs_liftM` / `someOutput_of_someOutput_liftM` /
`noOutput_liftM` are the generically-true half of lift transport.
`PFunctor.FreeM.support_eq_liftM_univ` is the worked *introduction* instance — the half
that is not generic, since nothing in `MonadLiftT`'s lawfulness says a lift preserves
reachability.

**Two real obstructions, both outside this repo.**

1. **`MonadAttach PMF` and `MonadAttach SPMF` do not exist anywhere** — not in the
   pinned Mathlib, not here, not downstream. Any bridge from a probability-flavoured
   support to the attach-based one goes through them, so they are the pivotal missing
   piece rather than a rename. `SPMF := OptionT PMF`, so a `MonadAttach PMF` yields
   `SPMF` for free through core's `OptionT` instance; the work is `attach`, for which
   `PMF.bindOnSupport` is the nearest primitive.
2. **A consumer pinning a PolyFun release predating `Control/Monad/Support.lean`
   cannot see any of this.** The whole layer landed after the `v4.33.2` tag. A tag bump
   is a hard prerequisite, not a detail.

**What will not migrate.** An answer-set-indexed support — the `supportWhen` shape,
where a per-oracle answer assignment is supplied — needs `SetM` as a genuine monad and
is a different notion from `MonadAttach.support`. Its home here is the specification
layer (`PFunctor/Free/WP.lean`), which indexes by a per-operation answer assignment.

**No boundary guard is proposed.** The probability layer's `PMF` guard justifies itself
from the pinned tree, where Mathlib is dismantling `PMF` construction by construction.
`SetM` is not being retired upstream at all, and PolyFun's own `SetM` surface is 17
occurrences across three files. The direction is set by documentation and by which API
new code is written against, not by CI.
