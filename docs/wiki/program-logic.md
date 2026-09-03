# Program-Logic Core

PolyFun's program-logic layer is the probability-free kernel shared by the
downstream verification stacks (VCVio's Loom2-based logic, core's lattice-generic
`Std.Internal.Do` / `vcgen`, and the Bluebell/Iris line). Design rationale and the downstream
migration sketch live in
[`docs/reading/program-logic-landscape.md`](../reading/program-logic-landscape.md).

## Layers

| Module | Content |
|---|---|
| `PolyFun/Control/Monad/Algebra.lean` | `MAlgOrdered m l`: ordered monad algebras over a complete lattice, with `wp`, `Triple`, the structural rule set, `StateT`/`ReaderT`/`ExceptT`/`OptionT` lifts, and the honest two-postcondition `wpExc`/`wpOpt` |
| `PolyFun/Control/Monad/Algebra/Relational.lean` | `MAlgRelOrdered m₁ m₂ l`: relational `rwp`/`RelWP`/`Triple`, asynchronous one-sided bind rules, structural pure rules, explicit named `StateT`/`ReaderT` side lifts, and the `StrictBind` / `Anchored` subclasses (Maillard et al. POPL 2020 shapes) |
| `PolyFun/Control/Monad/Algebra/Relational/Support.lean` | Named demonic and angelic exact-support relational algebras; support characterizations; matching `StrictBind` and `Anchored` witnesses |
| `PolyFun/Control/Monad/Support.lean` | `ExactMonadAttach m`: additional pure/bind composition laws for `MonadAttach.CanReturn`; `MonadAttach.support`; the `AllOutputs`/`SomeOutput`/`NoOutput` judgments and scoped `⊨ₐ`/`⊨ₛ`/`⊭` notation with their `pure`/`bind` laws; the named demonic and angelic `MAlgOrdered m Prop` choices |
| `PolyFun/Control/Monad/Support/Instances.lean` | The `MonadLiftT m SetM` shim, transport along lawful lifts, the `MonadAttach` instances for `Except`, `SetM`, and Mathlib’s `WriterT`, exactness instances for `Id`/`Option`/`OptionT`/`ExceptT`, per-monad `CanReturn` unfoldings |
| `PolyFun/Control/Monad/Support/Indexed.lean` | Per-run support of `StateT`/`ReaderT` (`supportFrom`, `supportAt`) with exact laws and the indexed judgments `⊨ₐ[s]`/`⊨ₛ[s]`/`⊭[s]` |
| `PolyFun/Control/Monad/Support/Structural.lean` | The rest of the `do` fragment for `CanReturn` and the judgments: `<*`, `*>`, `if`, `if h :`, `Option.elim`, `Sum.elim`, `<$>`, `<*>` |
| `PolyFun/Control/Monad/Support/Loops.lean` | Invariant rules for `forIn'`/`forIn`/`foldlM`/`forM` over lists and `PureForIn` containers, for `AllOutputs` (from core's `Spec.*` under the demonic instance) and `SomeOutput` (angelic) |
| `PolyFun/PFunctor/Free/Support.lean` | `MonadAttach`/`ExactMonadAttach` for `FreeM P` with a computable, axiom-free `attach`; structural equations by `rfl`; coherence with `Free/Path.lean` (`support_eq_range_output`) and with the powerset fold (`support_eq_liftM_univ`) |
| `PolyFun/PFunctor/Free/WP.lean` | `OpSpec P l` per-operation specs; syntactic `FreeM.wpFold` (with `demonic`/`angelic`); `OpSpec.toMAlgOrdered`; semantic `FreeM.wpVia` through a `Handler`; soundness `wpFold_le_wpVia`/`wpFold_eq_wpVia` |
| `PolyFun/Control/Do/Spec.lean` | Tactic tier: `@[spec] Spec.forM_list` for `vcgen` |
| `PolyFun/PFunctor/Free/WP/Upstream.lean` | `OpSpec.toWPMonad` (the syntactic fold as a core `WPMonad`), `FreeM.wpMonadOfHandler` (transport along `liftMHom`), and `wpFold_le_wp_liftM`, soundness of op-specs against any core `WPMonad` |
| `PolyFun/ITree/Do.lean` | Productive `while` for interaction trees: `forInLoop`, the scoped `ForIn` instance, and `forInLoop_weakBisim_of_invariant` — an invariant-scoped `WeakBisim` congruence because `iter` is lawful only up to weak bisimulation |
| `PolyFun/PFunctor/Free/Do.lean` | Tactic tier for free programs: scoped demonic and angelic `WPMonad` instances (`open scoped PFunctor.FreeM.DemonicWP` / `AngelicWP`), soundness and conjunctivity instances, and the `@[spec]` lemmas `Spec.lift`, `Spec.liftBind`, `Spec.lift_bind`, `Spec.lift_angelic`, `Spec.lift_ofHandler` that let `vcgen` decompose free programs with uninterpreted operations |
| `PolyFun/Control/Monad/Algebra/WP.lean` | `MAlgOrdered.toWP` / `toWPMonad`: an ordered monad algebra as a core `Std.Internal.Do.WPMonad m l EPost.Nil` (through the `ToCslib.Order.LeanOrder` bridge), `wp` agreement by `rfl`, `toWP_triple_iff`, `wpConjunctiveOf`, and the transfer lemmas `top_eq_top` / `meet_eq_inf` / `join_eq_sup` between core's and Mathlib's lattice operations |
| `PolyFun/Control/Monad/Support/WP.lean` | `MonadAttach.toWPMonadDemonic` / `toWPMonadAngelic`: the always/some judgments as `WPMonad m Prop EPost.Nil`; conjunctivity of the demonic reading; `MonadAttach.LawfulWPMonadAttach` (soundness with respect to lawful attachment, the class core ships as `Std.WP.LawfulWPMonadAttach` from v4.35) with its demonic instance; `support_subset_of_wp` / `allOutputs_of_wp` |
| `PolyFun/Control/Monad/Hom/WP.lean` | `MonadHom.transportWPOf` / `transportWPMonadOf` (along cslib's `IsMonadHom`) and the bundled `transportWP` / `transportWPMonad`: pulling a core `WPMonad` back along a monad morphism |
| `PolyFun/Control/Monad/Hom/Loops.lean` | A monad morphism between lawful monads commutes with `forIn'`/`forIn`/`forM`/`foldlM`/`mapM` and with `forIn` over `PureForIn` containers (`@[simp, grind =]`), through `MonadHom.isMonadHom` and cslib's `IsMonadHom.map_list*` |
| `PolyFun/Control/Do/Spec.lean` | `@[spec] Spec.forM_list`, the list loop core does not specify, and the `@[spec]` registration of core's `Spec.tryCatch_MonadExcept`, the `try … catch` rule core states but does not tag (tactic tier) |

Worked examples: `PolyFunTest/Control/MonadAttach.lean` (judgments, notation,
`Iff.rfl` transfer contract), `PolyFunTest/Control/{SupportStructural,SupportLoops,MonadHomLoops}.lean`
(the `do`-fragment rules and loop rules by one tactic or one lemma, no triple), and, under
`vcgen`: `PolyFunTest/Do/FreeM.lean` and `PolyFunTest/Do/Loops.lean` (free programs with
uninterpreted operations, loops, branching, and `StateT`), `PolyFunTest/Do/Transport.lean`
(handler-relative interpretation), and `PolyFunTest/Do/{Algebra,Support,Except}.lean` (a
locally installed algebra, the demonic reading of `SetM` with `for` and `forM` loops, and
`try … catch` on `ExceptT`).

## Relation to core `MonadAttach`

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
- **Soundness is the bridge.** `MonadAttach.LawfulWPMonadAttach` with
  `support_subset_of_wp` / `allOutputs_of_wp` converts a weakest-precondition
  proof for an interpretation satisfying this law into a structural support fact.

The demonic core `WPMonad` needs only `LawfulMonadAttach`, including when the
monad is a state or reader transformer. Its pure/bind laws are inequalities,
proved directly from core's return-value elimination lemmas. The angelic
interpretation and the equality-based `MAlgOrdered` constructions require exact
composition. Writer attachment's weak and strong law instances require the
corresponding upstream law on the base, independently of exactness.

`PolyFunTest/Do/Support.lean` checks that lawful `CanReturn` agrees with upstream
`Std.Do.Internal.MayReturn`, that `AllOutputs` agrees with `Ensures`, and that
two lawful attachment instances have equivalent return predicates. These older
internal predicates stay out of the public API: the v4.35 public soundness class
uses `CanReturn` directly ([Lean #14801](https://github.com/leanprover/lean4/pull/14801)).

Core supplies the instances for `Id`, `Option`, `OptionT`, `ExceptT`, `StateT`,
and `ReaderT`; PolyFun adds `Except` and `SetM` (which core lacks), a
single-universe alias for core's `ExceptT` instance (which is declared at
`max`-joined universes and cannot otherwise be synthesized polymorphically), and
the `FreeM P` instance.

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
statements transfer without rewriting. `triple_top_iff_allOutputs` identifies
`x ⊨ₐ p` with the trivial-precondition `Prop`-carrier triple, and on `FreeM` the
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

The support-based unary and relational `Prop` algebras and the relational transformer lifts are
explicit named definitions, not unrestricted global instances. This keeps
support partial correctness distinct from the existing failure-as-`⊥`
`OptionT`/`ExceptT` algebras and prevents inequivalent left/right transformer
instance paths. The demonic relational algebra quantifies over every pair in the
two supports; the angelic algebra asks for one witnessing pair. Both satisfy
`StrictBind` and are `Anchored` to the corresponding unary support algebra.
Install the intended definitions and witnesses locally at each verification boundary.

```lean
local instance : MAlgOrdered m₁ Prop := MonadAttach.mAlgOrderedPropDemonic
local instance : MAlgOrdered m₂ Prop := MonadAttach.mAlgOrderedPropDemonic
local instance : MAlgRelOrdered m₁ m₂ Prop :=
  MonadAttach.mAlgRelOrderedPropDemonic
local instance : StrictBind m₁ m₂ Prop := MonadAttach.strictBindPropDemonic
local instance : Anchored m₁ m₂ Prop := MonadAttach.anchoredPropDemonic
```

Use the `Angelic` definitions with the same pattern when existential support is
the intended observation. `ReaderT` itself is not `ExactMonadAttach`; its named
relational lifts instead reason at explicit left/right environments.

## Support: which interface is canonical

`MonadAttach` is the canonical interface for reachability — it is core's, it carries a
lawfulness hierarchy, and core supplies the transformer instances. The
`MonadLiftT m SetM` presentation (`MonadAttach.toMonadLiftT`, deliberately not an
instance) is a **compatibility shim for a downstream still phrased that way**, not the
recommended API.

`SetM` is fine as a *carrier*: `support : Set α` is unchanged, and
`PFunctor.FreeM.support_eq_liftM_univ` — a genuine fold into `SetM`-as-monad — stays.
What is demoted is the lift as an interface. Note this is a project standardization,
**not** an upstream retirement: unlike `PMF` in the probability layer, `SetM` is not
being deprecated by Mathlib, so there is no boundary guard and none is proposed.

The migration contract for a downstream — what bridges exist, and the two real
obstructions — is in
[`docs/reading/program-logic-landscape.md`](../reading/program-logic-landscape.md).

## Coverage of the `do` fragment

What `do`-notation elaborates to, and where each construct has a rule. "free" means the rule is
core's `Spec.*` lemma applied through the `WPMonad` instances of the bridges, with no PolyFun
proof.

| Construct | core `wp` / `Triple` (`vcgen`) | `AllOutputs` / `SomeOutput` / `support` | `MAlgOrdered.wp` | `MonadHom` | `wpFold` |
|---|---|---|---|---|---|
| `pure`, `>>=`, `<$>`, `<*>` | free | `Support.lean`, `Support/Structural.lean` | `Algebra.lean` | `Hom.lean` | `Free/WP.lean` |
| `FreeM.lift a`, `FreeM.liftBind a r`, `(FreeM.lift a).bind r` | `Spec.lift`/`Spec.liftBind`/`Spec.lift_bind` (`Free/Do.lean`; tail position via `wp_apply_eq`, gotcha 12f) | `Free/Support.lean` (`allOutputs_lift`, `allOutputs_lift_bind`, `allOutputs_liftBind`) | via `OpSpec.toMAlgOrdered` | — | `wpFold_lift_bind` / `wpFold_liftBind` |
| `<*`, `*>` | free | `Support/Structural.lean` | `Algebra.lean` (`wp_seqLeft`/`wp_seqRight`) | `Hom.lean` | `Free/WP.lean` |
| `if`, `if h :` | `vcgen` splits | `Support/Structural.lean` | `wp_ite`/`wp_dite` | `mmap_ite`/`mmap_dite` | `wpFold_ite`/`wpFold_dite` |
| `match` on `Option`/`Sum` | `vcgen` splits | `*_option_elim`/`*_sum_elim` | `wp_option_elim`/`wp_sum_elim` | `mmap_option_elim`/`mmap_sum_elim` | `wpFold_option_elim`/`wpFold_sum_elim` |
| `for` over `List`/`Array`/ranges/`Option`/`Vector` | free (`Spec.forIn'_list`, `forIn_pure` + `PureForIn`) | `Support/Loops.lean` | via the instance | `Hom/Loops.lean` | via `OpSpec.toWPMonad` (`Free/WP/Upstream.lean`) |
| `forM`, `foldlM` | `Spec.foldlM_list` free, `Spec.forM_list` in `Do/Spec.lean` | `Support/Loops.lean` | via the instance | `Hom/Loops.lean` | — |
| `mapM` | — | — | — | `Hom/Loops.lean` | — |
| early `return`/`break`/`continue` | `Invariant.withEarlyReturnNewDo` (core) | via the instance | — | — | — |
| `throw`/`tryCatch` on `ExceptT`/`OptionT` | core's lifted instances (`Spec.throw_MonadExcept`, `Spec.tryCatch_ExceptT`), plus `Spec.tryCatch_MonadExcept` registered in `Do/Spec.lean` for the `try … catch` elaboration | via the instance | — | `ExceptT.mapHom`/`OptionT.mapHom` | — |
| `get`/`set`/`read` | core's lifted instances | `Support/Indexed.lean` (`supportFrom`, `supportAt`) | — | `StateT.mapHom`/`ReaderT.mapHom` | — |
| `while`/`repeat` | `ITree` only (`ITree/Do.lean`); no rule on finite `FreeM` | — | — | — | — |

Open in this table: the relational (`MAlgRelOrdered`) loop rules and a `mapM` judgment rule
(see the landscape memo's follow-ups). `try … catch` elaborates to `MonadExcept.tryCatch`, whose
lifting rule core states as `Spec.tryCatch_MonadExcept` but — unlike its twin
`Spec.throw_MonadExcept` — does not tag; `Do/Spec.lean` registers it, and
`PolyFunTest/Do/Except.lean` runs `vcgen` through a `try … catch` on `ExceptT String SetM`.

## The `Std.Do` quarantine

Core's weakest-precondition API is fenced in two tiers (`scripts/check-modules.sh` enforces
both, for every import modifier):

- **Definitions** — `Std.Do` and `Std.Internal.Do` (`WP`, `WPMonad`, `Triple`, the `@[spec]`
  lemmas) — may be imported by the program-logic kernel, `PolyFun/Control/Monad/`,
  `PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/`, `PolyFun/ITree/Do.lean`, and by
  `PolyFunTest/Do/`.
- **Tactics** — `Std.Tactic.Do` (`mvcgen`, `vcgen`, the `@[spec]` attribute syntax) — stay in
  `PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/Do.lean`, and `PolyFunTest/Do/`.

`ToCslib/` imports neither directly. The quarantine keeps the dependency on the fast-moving
upstream API confined, and everything the fenced modules provide is a construction (`def`) or a
`scoped` instance, not a global instance — global `WP` instances on `FreeM` would race
downstream registrations on reducible unfoldings such as VCVio's `OracleComp`. The free-monad
interpretations are `scoped` under `PFunctor.FreeM.DemonicWP` / `AngelicWP`; the bridges of
`PolyFun/Control/Monad/{Algebra,Support,Hom}/WP.lean` and `FreeM.wpMonadOfHandler` are
installed `local` or `scoped` at the carrier. `vcgen` itself is experimental at this pin (it warns on every call), so production
proofs do not call it; tactic calls live in `PolyFunTest/Do/`, where each asserts the warning
with `#guard_msgs`.

## The two upstream WP stacks

Core ships **two** complete weakest-precondition stacks at the v4.34.0 pin. PolyFun's
canonical interface is the lattice-generic one; nothing in PolyFun instantiates the older
SPred one.

| | `Std/Internal/Do/` (canonical here) | `Std/Do/` (not used) |
|---|---|---|
| Assertions | any `Lean.Order.CompleteLattice` (`Assertion`) | `SPred` / `PostShape` |
| `WPMonad` bind law | inequational (`bind_le_wp_bind`) | equational (`wp_bind : … = …`) |
| Conjunctivity | opt-in, per program (`WPConjunctive x`) | a **field of `PredTrans`**, bi-entailment |
| Exceptions | `EPred` postconditions (`EPost.Nil`, `EPost.Cons`) | `ExceptConds` inside `PostCond` |
| Tactic | `vcgen` | `mvcgen` (deprecated on master) |
| Upstream direction | public `Std.WP` in v4.35 | `mvcgen` deprecated in favor of `vcgen` |

The inequational law is what lets *both* support readings instantiate the canonical stack:
`MonadAttach.toWPMonadDemonic` (`wp x post = AllOutputs post x`) and `toWPMonadAngelic`
(`wp x post = SomeOutput post x`). Only the demonic reading is conjunctive; the angelic one
distributes over `∧` in one direction only, which is exactly why it has no `Std.Do.WP` and no
`WPConjunctive` instance (`PolyFunTest/Control/MonadAttach.lean` proves the counterexample).
`MAlgOrdered.toWPMonad` gives every Mathlib-lattice carrier the same treatment through the
`ToCslib.Order.LeanOrder` bridge, and `MonadHom.transportWPMonad` pulls any of these back along
a monad morphism. None of them is a global instance; install them `local` or `scoped` at the
carrier (`PolyFunTest/Do/{Algebra,Support}.lean` show `vcgen` running through each).

Four practical rules for writing against the canonical stack:

- Import the `Std.Internal.Do` **root** wherever a `vcgen` proof is expected: the `@[spec]`
  database (`Spec.bind`, `Spec.pure`, …) lives in `Std.Internal.Do.Triple.SpecLemmas`, and
  importing only `WP.Basic` yields `No spec found for program …` on every `do` block. The bridge
  modules import the root for this reason.
- A structure with an instance-implicit parameter re-synthesizes that instance on projection
  and construction (`h.le_wp`, `⟨h⟩`, `refine ⟨…⟩` for `WPConjunctive`), so a proof about a
  non-instance interpretation binds it first: `let inst := MAlgOrdered.toWP α`.
- Naming a theorem `Lean.Order.foo` elaborates it inside that namespace, activating core's
  scoped `⊤` / `⊓` / `⊔` and shadowing Mathlib's `le_top` / `le_inf`; keep transfer lemmas in
  a PolyFun namespace and qualify core's names.
- `vcgen` matches `@[spec]` lemmas structurally on the program and its value type, so a spec
  at a dependent value type (`Spec.lift` at `P.B a`) applies under `bind` but not to an
  operation in tail position once the goal carries the normalized type; finish such goals
  with `DemonicWP.wp_apply_eq` and `FreeM.allOutputs_lift` (gotcha 12f).

**Renames at the v4.35 bump** (recorded so the migration is mechanical; each affected
declaration carries an `-- upstream:` comment): `Std.Internal.Do` → `Std.WP`; `EPost.Nil` →
`EStack⟨⟩` and `EPost.Cons eh et` → `eh × et`; `Std.Internal.Do.Order.*` →
`Std.Internal.Order.*` (whose `Prop` instances become scoped); `MonadAttach.LawfulWPMonadAttach`
is deleted in favour of `Std.WP.LawfulWPMonadAttach` (same field); `ForIn.forInWithInvariant`
→ `forInPureWithInvariant`; `mvcgen` is deprecated and `vcgen` moves behind
`experimental.vcgen` (the `#guard_msgs` texts in `PolyFunTest/Do/` change accordingly); the
`⦃P⦄ x ⦃v, Q⦄` binder form of the triple notation is removed (PolyFun uses the lambda form).

`MAlgOrdered` stays: it is the Mathlib-lattice kernel VCVio's quantitative carrier bridges to
by `rfl`, and its `WriterT` lift has no core counterpart. The bridge, not a port, is what
connects it to core's order hierarchy.

## Qualitative and quantitative interpretations

Attachment on `FreeM` describes paths through the uninterpreted tree. Its
subtype proof certifies that a leaf value is reachable; it does not retain a
runtime path or choose a probability interpretation. The same program can have
qualitative and quantitative `WPMonad` interpretations, installed explicitly or
locally. `WPMonad` alone does not imply `LawfulWPMonadAttach`: existential or
expectation semantics need not establish a property at every structural output.

A downstream handler can assign zero mass to a structurally reachable branch.
Consequently structural reachability, positive mass, and almost-everywhere
properties must be related by explicit semantic theorems with their required
full-support, losslessness, and measurability hypotheses. No quantitative
interpretation changes the attachment instance or gains qualitative soundness
automatically.

## What stays downstream

Probability carriers (`evalDist`, SPMF, ℝ≥0∞/`Prob`), couplings and
pRHL/eRHL, concrete handler specifications, verification tactics
(`vcgen`/`mvcgen'` and attribute machinery), and any Loom2 or Iris/Bluebell
dependency. PolyFun ships definitions, rule lemmas, and simp sets only.
