# Program-Logic Core

PolyFun's program-logic layer extends core's lattice-generic weakest-precondition framework
`Std.WP` and its tactic `vcgen`. It adds exactness of interpretations (`ExactWPMonad`), with the
equational `simp` set that exactness licenses on core's `wp`, ordered monad algebras as a
presentation of exact interpretations, exact support, and a relational layer, which core does not
have. The layer is parameterized by the effects and by an ordered algebra of results.

An *interpretation* of a monad is a core `WPMonad` structure on it, and a *reading* is a named
interpretation. The *demonic* reading (`MonadAttach.toWPMonadDemonic`) asks the postcondition of
every possible output, and the *angelic* reading (`MonadAttach.toWPMonadAngelic`) asks it of some
possible output. Together they are the *support readings*. The *dual* reading of an exact
interpretation (`ExactWPMonad.dual`) states upper bounds. An *expectation* reading takes
postconditions valued in `ℝ≥0∞` and gives their expected values. VCVio, which builds on PolyFun,
supplies the expectation reading of its oracle computations.
[Names in VCVio](#names-in-vcvio) lists VCVio's names for these readings.

## Layers

| Module | Content |
|---|---|
| `PolyFun/Control/Monad/Algebra.lean` | `MonadAlgebra`/`LawfulMonadAlgebra` (Eilenberg–Moore structure maps); `MAlgOrdered m l`: ordered monad algebras over a complete lattice, a structure map `μ` fixing `pure` and monotone under `bind` — the presentation of an exact interpretation that `MAlgOrdered.toWPMonad` installs |
| `PolyFun/Control/Monad/Algebra/Restrict.lean` | `MAlgOrdered.restrictIic`: an algebra that respects a bound `c` restricted to the lower set `Set.Iic c` (Mathlib's complete lattice on it), with `wp_restrictIic_val` and `restrictIic_triple_iff` on core's `wp`/`Triple` — the shape of a probabilistic carrier `[0, 1] ⊆ ℝ≥0∞` |
| `PolyFun/Control/Monad/Algebra/Relational.lean` | `MAlgRelOrdered m₁ m₂ l`: relational `rwp`/`RelWP`/`Triple`, asynchronous one-sided bind rules, structural pure rules, explicit named `StateT`/`ReaderT` side lifts, the honest `rwpExc`, and the `StrictBind` / `Anchored` subclasses (Maillard et al. POPL 2020 shapes; `Anchored` ties `rwp` to core's `wp` of each side at `pure`) |
| `PolyFun/Control/Monad/Algebra/Relational/Support.lean` | Named demonic and angelic exact-support relational algebras; support characterizations; matching `StrictBind` witnesses and `Anchored` witnesses over `toWPMonadDemonic`/`toWPMonadAngelic` |
| `PolyFun/Control/Monad/Support.lean` | `ExactMonadAttach m`: additional pure/bind composition laws for `MonadAttach.CanReturn`; `MonadAttach.support`; the `AllOutputs`/`SomeOutput`/`NoOutput` judgments and scoped `⊨ₐ`/`⊨ₛ`/`⊭` notation with their `pure`/`bind` laws |
| `PolyFun/Control/Monad/Support/Instances.lean` | The `MonadLiftT m SetM` shim, transport along lawful lifts, `MonadAttach` and its lawfulness instances for `SetM` and Mathlib's `WriterT`, a single-universe alias of core's `MonadAttach (ExceptT ε m)`, the exactness instances for `Id`, `Option`, `Except`, `SetM`, `OptionT`, `ExceptT`, and `WriterT`, and per-monad `CanReturn` unfoldings |
| `PolyFun/Control/Monad/Support/Indexed.lean` | Per-run support of `StateT`/`ReaderT` (`supportFrom`, `supportAt`) with exact laws and the indexed judgments `⊨ₐ[s]`/`⊨ₛ[s]`/`⊭[s]` |
| `PolyFun/Control/Monad/Support/Structural.lean` | The rest of the `do` fragment for `CanReturn` and the judgments: `<*`, `*>`, `if`, `if h :`, `Option.elim`, `Sum.elim`, `<$>`, `<*>` |
| `PolyFun/Control/Monad/Support/Loops.lean` | Invariant rules for `forIn'`/`forIn`/`foldlM`/`forM` over lists and `PureForIn` containers, for `AllOutputs` (from core's `Spec.*` under the demonic reading) and `SomeOutput` (angelic) |
| `PolyFun/PFunctor/Free/Support.lean` | `MonadAttach`/`ExactMonadAttach` for `FreeM P` with a computable, axiom-free `attach`; structural equations by `rfl`; coherence with `Free/Path.lean` (`support_eq_range_output`) and with the powerset fold (`support_eq_liftM_univ`) |
| `PolyFun/PFunctor/Free/WP.lean` | `OpSpec P l` per-operation specs; syntactic `FreeM.wpFold` (with `demonic`/`angelic`); `OpSpec.toMAlgOrdered` (`toMAlgOrdered_μ_bind_pure`); coherence of the demonic/angelic folds with the support judgments |
| `PolyFun/PFunctor/Free/WP/Upstream.lean` | `OpSpec.toWPMonad` (the syntactic fold as a core `WPMonad`), `FreeM.wpMonadOfHandler` (transport along `liftMHom`), both exact when their source is; `wpFold_le_wp_liftM`, soundness of op-specs against any core `WPMonad`, and `wpFold_eq_wp_liftM` over an exact one; `allOutputs_liftM_of_wpFold` / `allOutputs_liftM_of_allOutputs` for the support of the interpreted program |
| `PolyFun/ITree/Do.lean` | Productive `while` for interaction trees: `forInLoop`, the scoped `ForIn` instance, and `forInLoop_weakBisim_of_invariant` — an invariant-scoped `WeakBisim` congruence because `iter` is lawful only up to weak bisimulation |
| `PolyFun/PFunctor/Free/Do.lean` | Tactic tier for free programs: scoped demonic and angelic `WPMonad` instances (`open scoped PFunctor.FreeM.DemonicWP` / `AngelicWP`), soundness and conjunctivity instances, and the `@[spec]` lemmas `Spec.lift`, `Spec.liftBind`, `Spec.bind`, `Spec.lift_angelic`, `Spec.lift_ofHandler` that let `vcgen` decompose free programs with uninterpreted operations |
| `PolyFun/Control/Monad/ExactWP.lean` | `ExactWPMonad m Pred EPred`, the mixin that makes a core `WPMonad` exact, with its dual reading `ExactWPMonad.dual`, the equational `simp` set on core's `wp` (`wp_pure` to `wp_sum_elim`), and the exactness instances for core's interpretations and transformer lifts (see [Exact interpretations](#exact-interpretations)) |
| `PolyFun/Control/Monad/Algebra/WP.lean` | `MAlgOrdered.toWP` / `toWPMonad`: an ordered monad algebra as the core `Std.WP.WPMonad m l EStack⟨⟩` with `wp x post = μ (x >>= fun a => pure (post a))` (through the `ToCslib.Order.LeanOrder` bridge), exact (`instExactWPMonadToWPMonad`), its value by `rfl` (`toWPMonad_wp`, not `@[simp]`), `toWP_triple_iff`, `wpConjunctiveOf`, and the transfer lemmas `top_eq_top`, `meet_eq_inf`, `join_eq_sup`, `iInf_eq_iInf`, and `iSup_eq_iSup` between core's and Mathlib's lattice operations |
| `PolyFun/Control/Monad/Support/WP.lean` | `MonadAttach.toWPDemonic` / `toWPAngelic`: the always and sometimes judgments as core `WP` transformers from attachment alone; `toWPMonadDemonic` / `toWPMonadAngelic`: the demonic and angelic readings as `WPMonad m Prop EStack⟨⟩`; conjunctivity of the demonic reading; exactness of both readings over an `ExactMonadAttach`; soundness of the demonic reading in the sense of core's `Std.WP.LawfulWPMonadAttach` (`toWPMonadDemonic_lawfulWPMonadAttach`); `support_subset_of_wp` / `allOutputs_of_wp` |
| `PolyFun/Control/Monad/Hom/WP.lean` | `MonadHom.transportWPOf` / `transportWPMonadOf` (along cslib's `IsMonadHom`) and the bundled `transportWP` / `transportWPMonad`: pulling a core `WPMonad` back along a monad morphism, preserving exactness |
| `PolyFun/Control/Monad/WriterT/WP.lean` | `WriterT.wpMonadOf`, the interpretation of `WriterT` with explicit empty and append operations on the log-indexed carrier `ω → Pred`, and its multiplicative specialization, scoped under `WriterT.MonoidWP`; the equations `WriterT.wp_apply_eq`, `wp_mk_apply_eq`, and `wp_run_eq`; the `tell` and `monadLift` entailments behind the `@[spec]` rules; and exactness over an exact base (`exactWPMonad_wpMonadOf`, scoped `WriterT.MonoidWP.instExactWPMonad`) |
| `PolyFun/Control/Monad/Hom/Loops.lean` | A monad morphism between lawful monads commutes with `forIn'`/`forIn`/`forM`/`foldlM`/`mapM` and with `forIn` over `PureForIn` containers (`@[simp, grind =]`), through `MonadHom.isMonadHom` and cslib's `IsMonadHom.map_list*` |
| `PolyFun/Control/Do/Spec.lean` | Tactic tier: the `@[spec]` rules listed below, for list loops, `try … catch`, sequencing, `WriterT`, `OptionT`, and the transformers' constructors, lifts, and runners |

`PolyFun/Control/Do/Spec.lean` adds these rules to core's `@[spec]` catalogue, in core's
namespace `Std.WP`:

- `Spec.forM_list`, for the one list loop that core does not specify, and `Spec.mapM_list`,
  with an invariant over the elements consumed, the elements remaining, and the outputs so far.
- The registration of core's `Spec.tryCatch_MonadExcept`, the rule for
  `MonadExcept.tryCatch`, which `try … catch` elaborates to. Core states this rule but does not
  tag it.
- `Spec.seqLeft` and `Spec.seqRight`, for `<*` and `*>`.
- `Spec.tell_WriterT`, `Spec.monadLift_WriterT`, `Spec.mk_WriterT`, and `Spec.run_WriterT`, for
  Mathlib's `WriterT` with a multiplicative log.
- `Spec.failure_OptionT` and `Spec.lift_OptionT` for every assertion carrier, `Spec.guard_OptionT`
  for `Prop`-valued readings, and `Spec.guard_OptionT_iInf`, its counterpart for every assertion
  carrier.
- `Spec.mk_StateT`, `Spec.lift_StateT`, `Spec.run'_StateT`, `Spec.mk_OptionT`,
  `Spec.mk_ExceptT`, and `Spec.lift_ExceptT`, for the transformers' constructors, lifts, and
  runners that programs write. `Spec.run_OptionT'` and `Spec.run_ExceptT'` run an `OptionT` or
  `ExceptT` computation into any postcondition of the returned option or result, and they take
  precedence over core's `Spec.run_OptionT` and `Spec.run_ExceptT`.

Worked examples:

- `PolyFunTest/Control/MonadAttach.lean`: the judgments, their notation, and the `Iff.rfl`
  transfer contract.
- `PolyFunTest/Control/{SupportStructural,SupportLoops,MonadHomLoops}.lean`: the `do`-fragment
  rules and the loop rules, each applied by one tactic or one lemma, with no triple.
- Under `vcgen`: `PolyFunTest/Do/FreeM.lean` and `PolyFunTest/Do/Loops.lean` (free programs with
  uninterpreted operations, loops, branching, and `StateT`), `PolyFunTest/Do/Transport.lean` (a
  handler-relative interpretation), `PolyFunTest/Do/{Algebra,Support,Except}.lean` (a locally
  installed algebra, the demonic reading of `SetM` with `for` and `forM` loops, and
  `try … catch` on `ExceptT`), and `PolyFunTest/Do/{OptionT,Transformers}.lean` (the `OptionT`
  rules and the transformers' constructors, lifts, and runners).

## Relation to core `MonadAttach`

Continuation congruence needs only `WeaklyLawfulMonadAttach`: use
`MonadAttach.bind_congr_of_canReturn` or
`MonadAttach.bind_congr_of_forall_mem_support` to compare continuations on possible
returns. Both follow from core's `attach_bind_val`, without exact composition.

For polynomial free programs, `FreeM.support_map` permits independent result
universes and `support_liftObj` uses the public object projection. Nonempty answer
types give `support_nonempty`; finite answer types give `support_finite`, even when
some answer types are empty. Neither theorem requires an enumeration.

The support layer is a three-way split:

- **Core owns the data and canonicity.** `MonadAttach.CanReturn x a` is "`a` is a
  possible output of `x`", `attach` decorates results with proofs of it, and
  `LawfulMonadAttach` pins it down as the strongest postcondition.
- **PolyFun supplies optional exact composition laws.** `ExactMonadAttach` adds
  pure and bind introduction to core's elimination rules. It carries proofs over
  the existing attachment data. Lawful attachment already determines the return
  predicate; exactness adds equations needed for existential composition and
  support-based monad algebras. The constant monad `fun _ => PUnit` has lawful
  empty support because it forgets all results, so pure introduction does not
  hold for every lawful monad.
- **Soundness is the bridge.** For an interpretation that satisfies core's
  soundness class `Std.WP.LawfulWPMonadAttach`, `support_subset_of_wp` and
  `allOutputs_of_wp` turn a weakest-precondition proof into a support fact.

The demonic reading needs only `LawfulMonadAttach`, even when the monad is a
state or reader transformer. Its `pure` and `bind` laws are inequalities, and
core's elimination lemmas for return values prove them directly. The angelic
reading, and exactness of either reading, need exact composition. The weakly
lawful and lawful attachment instances of `WriterT` need the corresponding core
law on the base monad, and neither needs exactness.

`PolyFunTest/Do/Support.lean` checks that lawful `CanReturn` agrees with core's
`Std.Do.Internal.MayReturn`, that `AllOutputs` agrees with
`Std.Do.Internal.Ensures`, and that two lawful attachment instances have
equivalent return predicates. These internal predicates stay out of the public
API: core's public soundness class `Std.WP.LawfulWPMonadAttach` uses `CanReturn`
directly ([Lean #14801](https://github.com/leanprover/lean4/pull/14801)).

Core supplies the `MonadAttach` instances for `Id`, `Option`, `Except`,
`OptionT`, `ExceptT`, `StateT`, and `ReaderT`. PolyFun adds the instances for
`SetM`, Mathlib's `WriterT`, and `FreeM P`. It also adds a single-universe alias
for core's `ExceptT` instance, which core declares at `max`-joined universes and
which instance search therefore cannot find in a universe-polymorphic context.

## Operation-indexed reachability

`FreeM.reachableUnder allows program` restricts each operation's typed responses
using `allows : (a : P.A) → P.B a → Prop`. It is the angelic `wpFold`, and
`mem_reachableUnder_iff_exists_path` characterizes its outputs by a root-to-leaf
path satisfying `Path.AllowedUnder`. The pure and node equations for that path
predicate are public, so consumers do not need `import all` to reason about it.
Use the compositional bind and lift equations for ordinary programs and the
explicit constructor equation `Path.allowedUnder_liftBind` for node paths.
`wpFold_bind'` supports sequencing across independent result universes.
The bind and map laws support independent result universes; use
`reachableUnder_bind'` for the universe-polymorphic `FreeM.bind`.

`FreeM.reachable` admits every typed response and equals `MonadAttach.support`.
A response policy can exclude structurally possible leaves. An operation with
no admitted answers has no reachable output: its demonic `LeavesSatisfyUnder`
judgment is vacuous, while the angelic judgment is false. These are partial
correctness statements, with no termination or progress guarantee.

A free handler satisfying the source response policy cannot add reachable leaf
results (`reachableUnder_liftM_subset`). It can discard source responses, so the
law is an inclusion, not equality. `reachable_liftM_subset` specializes to the
all-response policy. This generic semantics assumes neither probabilities nor
`ExactMonadAttach`.

`PolyFunTest/ModuleAPI/Reachability.lean` checks this API through ordinary imports,
including dependent responses, empty response sets, independent result universes,
and a handler that strictly reduces the reachable results.

## Always / never judgments

For `[MonadAttach m]` and `x : m α` (`open scoped MonadAttach`):

- `x ⊨ₐ p` (`AllOutputs p x`): every possible output satisfies `p` —
  definitionally `∀ a, CanReturn x a → p a`, and equally
  `∀ a ∈ support x, p a`: the two spellings are interchangeable by `Iff.rfl`
  (`allOutputs_iff_forall_canReturn`, `allOutputs_iff_forall_support`).
- `x ⊨ₛ p` (`SomeOutput p x`): some possible output satisfies `p`.
- `x ⊭ p` (`NoOutput p x`): no possible output satisfies `p`.

These stay `Iff.rfl`-convertible both to their bounded-quantifier spellings and
to `CanReturn` — a contract pinned by tests — so downstream support-based
statements transfer without rewriting. `toWPMonadDemonic_triple_iff` identifies
`x ⊨ₐ p` with core's triple under the demonic reading, and on `FreeM` the
judgments recurse structurally (`allOutputs_liftBind` and friends) and agree with
the demonic/angelic `wpFold` (`wpFold_demonic_iff_allOutputs`).

`StateT` and `ReaderT` do carry core's canonical support — the union over initial
states — so the elimination theory applies to them, but they are deliberately
*not* `ExactMonadAttach`: possible outputs do not compose along `bind` when the
flattened premises choose unrelated initial indices. For `StateT`, the continuation
may observe a state the prefix never produced; for `ReaderT`, the two premises may use
different environments. The test suite pins both failures. Reason per run instead, via
`StateT.supportFrom` and `ReaderT.supportAt`. Oracle- and state-relative supports belong at the
specification layer (`PFunctor/Free/WP.lean`), which indexes the notion by a
per-operation answer assignment.

The unary support readings, the relational `Prop` algebras, and the relational transformer
lifts are explicit named definitions, not unrestricted global instances. This keeps
support partial correctness distinct from other interpretations of the same monad and prevents
inequivalent left/right transformer instance paths. The demonic relational algebra quantifies
over every pair in the two supports; the angelic algebra asks for one witnessing pair. Both
satisfy `StrictBind` and are `Anchored` to the corresponding unary support reading.
Install the intended definitions and witnesses locally at each verification boundary.

```lean
local instance : WPMonad m₁ Prop EStack⟨⟩ := MonadAttach.toWPMonadDemonic
local instance : WPMonad m₂ Prop EStack⟨⟩ := MonadAttach.toWPMonadDemonic
local instance : MAlgRelOrdered m₁ m₂ Prop :=
  MonadAttach.mAlgRelOrderedPropDemonic
local instance : StrictBind m₁ m₂ Prop := MonadAttach.strictBindPropDemonic
local instance : Anchored m₁ m₂ Prop := MonadAttach.anchoredPropDemonic
```

Use the `Angelic` definitions with the same pattern when existential support is
the intended observation. `ReaderT` itself is not `ExactMonadAttach`; its named
relational lifts instead reason at explicit left/right environments.

## Support: which interface is canonical

`MonadAttach` is the canonical interface for reachability: it is core's, it carries a
lawfulness hierarchy, and core supplies the transformer instances. The
`MonadLiftT m SetM` presentation (`MonadAttach.toMonadLiftT`, deliberately not an
instance) is a **compatibility shim for downstream code phrased as a lift into `SetM`**,
not the recommended API.

`SetM` is a good *carrier*: `support` takes values in `Set α`, and
`PFunctor.FreeM.support_eq_liftM_univ` is a genuine fold into `SetM` as a monad. Only the
lift as an interface is discouraged. This is a convention of this project, **not** an
upstream deprecation: Mathlib does not deprecate `SetM`, and no boundary check enforces
the convention.

## Coverage of the `do` fragment

The table lists what `do`-notation elaborates to and where each construct has a rule. An entry
"free" means that core's `Spec.*` lemma applies through the `WPMonad` instances of the bridges,
with no PolyFun proof.

| Construct | core `wp` / `Triple` (`vcgen`) | `AllOutputs` / `SomeOutput` / `support` | exact core `wp` (`simp`) | `MonadHom` | `wpFold` |
|---|---|---|---|---|---|
| `pure`, `>>=`, `<$>`, `<*>` | free | `Support.lean`, `Support/Structural.lean` | `ExactWP.lean` | `Hom.lean` | `Free/WP.lean` |
| `FreeM.lift a`, `FreeM.liftBind a r`, `(FreeM.lift a).bind r` | `Spec.lift`/`Spec.liftBind`/`Spec.bind` (`Free/Do.lean`); an operation in tail position is finished with `wp_apply_eq` ([troubleshooting](../development/troubleshooting.md#vcgen-matches-specs-structurally-so-dependent-value-types-need-care)) | `Free/Support.lean` (`allOutputs_lift`, `allOutputs_bind`, `allOutputs_liftBind`) | via `OpSpec.toWPMonad` | — | `wpFold_lift` / `wpFold_bind` / `wpFold_liftBind` |
| `<*`, `*>` | `Spec.seqLeft`/`Spec.seqRight` in `Do/Spec.lean` | `Support/Structural.lean` | `ExactWP.lean` (`wp_seqLeft`/`wp_seqRight`) | `Hom.lean` | `Free/WP.lean` |
| `if`, `if h :` | `vcgen` splits | `Support/Structural.lean` | `wp_ite`/`wp_dite` | `mmap_ite`/`mmap_dite` | `wpFold_ite`/`wpFold_dite` |
| `match` on `Option`/`Sum` | `vcgen` splits | `*_option_elim`/`*_sum_elim` | `wp_option_elim`/`wp_sum_elim` | `mmap_option_elim`/`mmap_sum_elim` | `wpFold_option_elim`/`wpFold_sum_elim` |
| `for` over `List`/`Array`/ranges/`Option`/`Vector` | free (`Spec.forIn'_list`, `forIn_pure` + `PureForIn`) | `Support/Loops.lean` | via the instance | `Hom/Loops.lean` | via `OpSpec.toWPMonad` (`Free/WP/Upstream.lean`) |
| `forM`, `foldlM` | `Spec.foldlM_list` free, `Spec.forM_list` in `Do/Spec.lean` | `Support/Loops.lean` | via the instance | `Hom/Loops.lean` | — |
| `mapM` | `Spec.mapM_list` in `Do/Spec.lean`, with an invariant over the elements consumed, the elements remaining and the outputs so far | — | — | `Hom/Loops.lean` | — |
| early `return`/`break`/`continue` | `Invariant.withEarlyReturnNewDo` (core) | via the instance | — | — | — |
| `throw`/`tryCatch` on `ExceptT`/`OptionT` | core's lifted instances (`Spec.throw_MonadExcept`, `Spec.tryCatch_ExceptT`), plus `Spec.tryCatch_MonadExcept` registered in `Do/Spec.lean` for the `try … catch` elaboration | via the instance | core's lifts, exact over an exact base | `ExceptT.mapHom`/`OptionT.mapHom` | — |
| `get`/`set`/`read` | core's lifted instances | `Support/Indexed.lean` (`supportFrom`, `supportAt`) | core's lifts, exact over an exact base | `StateT.mapHom`/`ReaderT.mapHom` | — |
| `tell`/`WriterT.run` | `WriterT.MonoidWP.instWPMonad` (`WriterT/WP.lean`) with `Spec.tell_WriterT` / `monadLift_WriterT` / `mk_WriterT` / `run_WriterT` in `Do/Spec.lean` | `mem_support_writerT_iff`, with exact support over an exact base (`Support/Instances.lean`) | `WriterT.MonoidWP.instExactWPMonad` | `WriterT.mapHom` | — |
| `while`/`repeat` | `ITree` only (`ITree/Do.lean`); no rule on finite `FreeM` | — | — | — | — |

The table has no relational column: loop rules for `MAlgRelOrdered` would need an invariant
relating two programs, and PolyFun states none. The `OptionT` rules and the rules for the
transformers' constructors, lifts, and runners are listed under [Layers](#layers).

`try … catch` elaborates to `MonadExcept.tryCatch`. Core states its lifting rule as
`Spec.tryCatch_MonadExcept` but, unlike its twin `Spec.throw_MonadExcept`, does not tag it.
`Do/Spec.lean` registers it, and `PolyFunTest/Do/Except.lean` runs `vcgen` through a
`try … catch` on `ExceptT String SetM`.

## The `Std.WP` quarantine

Core's weakest-precondition API is fenced in two tiers, and `scripts/check-modules.sh` enforces
both for every import modifier:

- **Definitions**: `Std.WP` (`WP`, `WPMonad`, `Triple`, the `@[spec]` lemmas) and core's
  `Std.Do` framework, which `mvcgen` uses, may be imported by the program-logic kernel
  (`PolyFun/Control/Monad/`, `PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/`, and
  `PolyFun/ITree/Do.lean`) and by `PolyFunTest/Do/`.
- **Tactics**: `Std.Tactic.Do` (`vcgen`, the deprecated `mvcgen`, and the `@[spec]` attribute
  syntax) stays in `PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/Do.lean`, and
  `PolyFunTest/Do/`.

`ToCslib/` imports neither tier directly. The quarantine confines the dependency on this
fast-moving core API. Every interpretation the fenced modules provide is a construction (`def`)
or a `scoped` instance, never a global instance, because a global `WP` instance on `FreeM` would
compete with downstream instances on its reducible unfoldings, such as VCVio's `OracleComp`. The
global instances they do declare are `Prop`-valued `ExactWPMonad` facts about those
interpretations. The free-monad readings are `scoped` under `PFunctor.FreeM.DemonicWP` and
`AngelicWP`. The bridges of `PolyFun/Control/Monad/{Algebra,Support,Hom}/WP.lean`,
`MAlgOrdered.restrictIic`, and `FreeM.wpMonadOfHandler` are installed `local` or `scoped` where
they are intended.

The writer interpretation also needs an explicit choice. Either `open scoped WriterT.MonoidWP`
for multiplicative logs, or install `WriterT.wpMonadOf` locally with the empty and append
operations and the lawfulness witness for the same `WriterT.monad`. The second choice supports
append-based logs without adding a `Monoid` instance or a competing writer monad.
`PolyFunTest/Do/WriterAppend.lean` checks ordered accumulation from a nonempty incoming log.

Core marks `vcgen` as experimental: each call prints a warning unless
`set_option experimental.vcgen true` acknowledges that status. No proof in the library calls
`vcgen`. The calls are in `PolyFunTest/Do/`, whose modules set the option, and
`PolyFunTest/Do/Algebra.lean` pins the warning itself with `#guard_msgs`.

## Core's two weakest-precondition frameworks

Core ships **two** complete weakest-precondition frameworks: the lattice-generic `Std.WP`, which
`vcgen` uses, and `Std.Do`, built on `SPred`, which `mvcgen` uses. PolyFun builds on `Std.WP`,
and nothing in PolyFun instantiates `Std.Do`.

| | `Std/WP/` (canonical here) | `Std/Do/` (not used) |
|---|---|---|
| Assertions | any `Lean.Order.CompleteLattice` (`Assertion`) | `SPred` / `PostShape` |
| `WPMonad` bind law | inequational (`bind_le_wp_bind`); equational under PolyFun's `ExactWPMonad` | equational (`wp_bind : … = …`) |
| Conjunctivity | opt-in, per program (`WPConjunctive x`) | a **field of `PredTrans`**, bi-entailment |
| Exceptions | `EPred` postconditions (`EStack⟨⟩`, `EStack⟨ε → Pred, …⟩`) | `ExceptConds` inside `PostCond` |
| Tactic | `vcgen` (experimental) | `mvcgen` (deprecated in favour of `vcgen`) |

The inequational laws let *both* support readings be interpretations in `Std.WP`:
`MonadAttach.toWPMonadDemonic` (`wp x post = AllOutputs post x`) and `toWPMonadAngelic`
(`wp x post = SomeOutput post x`). Only the demonic reading is conjunctive. The angelic reading
distributes over `∧` in one direction only, which is why it has no `Std.Do.WP` and no
`WPConjunctive` instance (`PolyFunTest/Control/MonadAttach.lean` proves the counterexample).
`MAlgOrdered.toWPMonad` gives every carrier with a Mathlib complete lattice the same treatment
through the `ToCslib.Order.LeanOrder` bridge, and `MonadHom.transportWPMonad` pulls any of these
interpretations back along a monad morphism. None of them is a global instance. Install each
`local` or `scoped` where it is intended, as `PolyFunTest/Do/{Algebra,Support,Angelic}.lean` do
before running `vcgen` through each.

### What the angelic reading does and does not say

`wp x post` under `toWPAngelic` is may/existential reachability: some output of `x` satisfies
`post`. It is the right reading for reachability, search, synthesis, and witness-producing
nondeterminism, and `PolyFunTest/Do/Angelic.lean` runs `vcgen` through it on a free program. Its
limits are deliberate, not gaps:

- No `WPConjunctive` instance, so core's `Triple.and`, `Triple.mp`, and `Triple.observe` do not
  apply: on the support `{0, 1}`, `wp x (· = 0)` and `wp x (· = 1)` both hold while
  `wp x (fun a => a = 0 ∧ a = 1)` fails.
- No `LawfulWPMonadAttach` instance: `wp x (· = 0)` holds on the same support although `1` is
  reachable, so an angelic `wp` proof never bounds every output; `support_subset_of_wp` needs the
  demonic reading.
- Empty support makes the angelic `wp` false where the demonic one is vacuously true.
- Existential reachability is not a probability bound and is never a security claim. Under
  scheduler nondeterminism it says that some favourable schedule exists, nothing about a fixed,
  fair, random, or adversarial scheduler, which needs its own bridge downstream.

## Exact interpretations

Soundness, the inequational `pure` and `bind` laws, is what `vcgen` needs: it decomposes a lower
bound `pre ⊑ wp prog post epost` into lower bounds on the pieces. These are the laws of a lax
monad morphism into core's `PredTrans`. Three other uses need the reverse, oplax, inequalities: an
upper bound `wp prog post epost ⊑ c` through a `bind`, an exact value, and a rewriting normal form
for `simp`. `ExactWPMonad m Pred EPred` is the `Prop` mixin on a `WPMonad` that supplies them.

The oplax laws are the soundness laws read in the order dual, so an exact interpretation is one
that is sound on both `Pred` and `Predᵒᵈ`. Its dual reading `ExactWPMonad.dual` is the same
interpretation as a core `WPMonad m Predᵒᵈ EPredᵒᵈ`. The triples of the dual reading state upper
bounds, and `vcgen` decomposes them like any other (`PolyFunTest/Do/Dual.lean`). Conversely,
`ExactWPMonad.of_dual` recovers exactness from a sound interpretation on the duals that agrees
with the original, and `exactWPMonad_iff_dual` states both directions. The lax and oplax laws
together make `wp_pure` and `wp_bind` equations. Equivalently, the interpretation is a monad
morphism into `PredTrans` (`ExactWPMonad.isMonadHom`, `ExactWPMonad.ofIsMonadHom`), and
`ExactWPMonad.of_eq` builds an instance from the two equations. `ToCslib.Order.LeanOrder` gives
`αᵒᵈ` the reverse of core's order on `α`. On a Mathlib lattice this order agrees, at instance
transparency, with the bridge of Mathlib's own dual order.

Every construction in this guide that can be exact is exact: `MAlgOrdered.toWPMonad`, both
support readings over an `ExactMonadAttach`, transport along a monad morphism,
`OpSpec.toWPMonad`, `FreeM.wpMonadOfHandler` into an exact target, core's `Id`, `Option`,
`Except`, and `EStateM` interpretations, and core's transformer lifts and the `WriterT`
interpretation over an exact base. Exactness is a mixin rather than a stronger class, so each of
these remains a plain core `WPMonad`, installed in the usual way, and a separation-logic or
inexact support interpretation keeps the same interface.

Under `ExactWPMonad`, core's `wp` is the normal form: its `@[simp]` set drives `wp` inward
through `pure`, `>>=`, `<$>`, `<*>`, `<*`, `*>`, `if`, `if h :`, `Option.elim`, and `Sum.elim`,
with each rewrite shrinking the program argument. The value of an algebra-built interpretation,
`toWPMonad_wp` (and `toWP_wp`), is therefore not `@[simp]`: `simp` keeps a goal stated against
core's `wp` on core's head rather than unfolding it to the algebra.
`PolyFunTest/Do/Exact.lean` checks the instances and that normalization stays on core's head.

Core's `Triple x pre post epost` is program-first; under an algebra-built interpretation
`toWP_triple_iff` unfolds it to Mathlib's order on the algebra (and `restrictIic_triple_iff`
relates a restricted carrier to its base).

Four practical rules for writing against `Std.WP`:

- Import the `Std.WP` **root** wherever a `vcgen` proof is expected: the `@[spec]`
  database (`Spec.bind`, `Spec.pure`, …) lives in `Std.WP.Triple.SpecLemmas`, and
  importing only `Std.WP.Basic` yields `No spec found for program …` on every `do` block.
  The bridge modules import the root for this reason.
- A structure with an instance-implicit parameter re-synthesizes that instance on projection
  and construction (`h.le_wp`, `⟨h⟩`, `refine ⟨…⟩` for `WPConjunctive`), so a proof about a
  non-instance interpretation binds it first: `let inst := MAlgOrdered.toWP α`.
- Naming a theorem `Lean.Order.foo` elaborates it inside that namespace, activating core's
  scoped `⊤` / `⊓` / `⊔` and shadowing Mathlib's `le_top` / `le_inf`; keep transfer lemmas in
  a PolyFun namespace and qualify core's names.
- `vcgen` matches `@[spec]` lemmas structurally on the program and its value type, so a spec
  at a dependent value type (`Spec.lift` at `P.B a`) applies under `bind` but not to an
  operation in tail position once the goal carries the normalized type. Finish such goals
  with `DemonicWP.wp_apply_eq` and `FreeM.allOutputs_lift`, as the
  [troubleshooting guide](../development/troubleshooting.md) explains under "`vcgen` matches
  specs structurally".

Core names in this guide are those of the pinned toolchain. Check them again whenever
`lean-toolchain` changes.

`MAlgOrdered` is a presentation, not a second program logic. It is how an exact interpretation
over a Mathlib lattice is written down, and everything proved about the interpretation is stated
on core's `wp`. VCVio presents its expectation reading this way, as an
`MAlgOrdered (OracleComp spec) ℝ≥0∞`.

## Support readings and expectation readings

On `FreeM`, attachment describes paths through the uninterpreted tree. The proof carried by an
attached value certifies that the value is a possible output. It records no runtime path and
fixes no probability distribution. One program can carry both support readings and an
expectation reading, each installed explicitly or locally. A `WPMonad` alone does not imply
`LawfulWPMonadAttach`: neither the angelic reading nor an expectation reading needs to
establish a property at every possible output.

A downstream handler can give probability zero to a branch of the free program. Possible
outputs, outputs of positive probability, and almost-sure properties are therefore related only
by explicit theorems, with the full-support, losslessness, and measurability hypotheses those
theorems need. An expectation reading does not change the attachment instance, and it satisfies
`LawfulWPMonadAttach` only where a theorem proves it.

## What stays downstream

Probability semantics stays downstream: output measures (`evalDist`), the expectation reading
over `ℝ≥0∞` and the `Prob` carrier, couplings and pRHL/eRHL, concrete handler specifications,
verification tactics specific to those readings, and any dependency on Loom2 or Iris/Bluebell.
PolyFun supplies the generic definitions, the rule lemmas, and the quarantined `vcgen` bridges
and specifications described above.

### Names in VCVio

VCVio, which builds on PolyFun, has its own names for the readings of its oracle computations
(`OracleComp`) and for their output measure:

| This guide | VCVio |
|---|---|
| the demonic reading (`MonadAttach.toWPMonadDemonic`) | the *necessary* reading (`OracleComp.Necessary`) |
| the angelic reading (`MonadAttach.toWPMonadAngelic`) | the *possible* reading (`OracleComp.Possible`) |
| the expectation reading, whose triples state lower bounds | the *lower* reading (`OracleComp.Lower`) |
| the dual reading (`ExactWPMonad.dual`) of the expectation reading, whose triples state upper bounds | the *upper* reading (`OracleComp.Upper`) |
| the output measure | the *successful-output measure* (`evalDist`) |
