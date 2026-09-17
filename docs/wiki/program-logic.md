# Program-Logic Core

PolyFun's program-logic layer is the probability-free kernel shared by the
downstream verification stacks (VCVio's Loom2-based logic, core `Std.Do` /
`mvcgen`, and the Bluebell/Iris line). Design rationale and the downstream
migration sketch live in
[`docs/reading/program-logic-landscape.md`](../reading/program-logic-landscape.md).

## Layers

| Module | Content |
|---|---|
| `PolyFun/Control/Monad/Algebra.lean` | `MAlgOrdered m l`: ordered monad algebras over a complete lattice, with `wp`, `Triple`, the structural rule set, `StateT`/`ReaderT`/`ExceptT`/`OptionT` lifts, and the honest two-postcondition `wpExc`/`wpOpt` |
| `PolyFun/Control/Monad/Algebra/Relational.lean` | `MAlgRelOrdered m₁ m₂ l`: relational `rwp`/`RelWP`/`Triple`, asynchronous one-sided bind rules, structural pure rules, explicit named `StateT`/`ReaderT` side lifts, and the `StrictBind` / `Anchored` subclasses (Maillard et al. POPL 2020 shapes) |
| `PolyFun/Control/Monad/Algebra/Relational/Support.lean` | Named demonic and angelic exact-support relational algebras; support characterizations; matching `StrictBind` and `Anchored` witnesses |
| `PolyFun/Control/Monad/Support.lean` | `ExactMonadAttach m`: additional pure/bind composition laws for `MonadAttach.CanReturn`; `MonadAttach.support`; the `AllOutputs`/`SomeOutput`/`NoOutput` judgments and scoped `⊨ₐ`/`⊨ₛ`/`⊭` notation; the named demonic `MAlgOrdered m Prop` choice; instances for `Except`/`SetM` (absent upstream) and the `ExceptT` universe alias |
| `PolyFun/PFunctor/Free/Support.lean` | `MonadAttach`/`ExactMonadAttach` for `FreeM P` with a computable, axiom-free `attach`; structural equations by `rfl`; coherence with `Free/Path.lean` (`support_eq_range_output`) and with the powerset fold (`support_eq_liftM_univ`) |
| `PolyFun/PFunctor/Free/WP.lean` | `OpSpec P l` per-operation specs; syntactic `FreeM.wpFold` (with `demonic`/`angelic`); `OpSpec.toMAlgOrdered`; semantic `FreeM.wpVia` through a `Handler`; soundness `wpFold_le_wpVia`/`wpFold_eq_wpVia` |
| `PolyFun/Control/Do/Basic.lean` | Legacy core-`Std.Do` transports: `MonadHom.transportSPredWP(Monad)` along a monad morphism, `MonadAttach.toWP(Monad)` demonically at `.pure`, `toWPSound` for core-sense soundness, and `support_subset_of_wpSPred`/`allOutputs_of_wpSPred` turning any `WPSound` triple into a support fact |
| `PolyFun/ITree/Do.lean` | Productive `while` for interaction trees: `forInLoop`, the scoped `ForIn` instance, and `forInLoop_weakBisim_of_invariant` — an invariant-scoped `WeakBisim` congruence because `iter` is lawful only up to weak bisimulation |
| `PolyFun/PFunctor/Free/Do.lean` | Scoped demonic `WP (FreeM P) .pure` instances (`open scoped PFunctor.FreeM.DemonicWP`), `wpMonadOfHandler`, and the `Spec.lift` `@[spec]` lemma enabling `mvcgen` on free programs with uninterpreted operations |
| `PolyFun/Control/Monad/Algebra/WP.lean` | `MAlgOrdered.toWP` / `toWPMonad`: an ordered monad algebra as a core `Std.Internal.Do.WPMonad m l EPost.Nil` (through the `ToCslib.Order.LeanOrder` bridge), `wp` agreement by `rfl`, `toWP_triple_iff`, `wpConjunctiveOf`, and the transfer lemmas `top_eq_top` / `meet_eq_inf` / `join_eq_sup` between core's and Mathlib's lattice operations |
| `PolyFun/Control/Monad/Support/WP.lean` | `MonadAttach.toWPMonadDemonic` / `toWPMonadAngelic`: the always/some judgments as `WPMonad m Prop EPost.Nil`; conjunctivity of the demonic reading; `MonadAttach.LawfulWPMonadAttach` (soundness with respect to lawful attachment, the class core ships as `Std.WP.LawfulWPMonadAttach` from v4.35) with its demonic instance; `support_subset_of_wp` / `allOutputs_of_wp` |
| `PolyFun/Control/Monad/Hom/WP.lean` | `MonadHom.transportWPOf` / `transportWPMonadOf` (along cslib's `IsMonadHom`) and the bundled `transportWP` / `transportWPMonad`: pulling a core `WPMonad` back along a monad morphism |

Worked examples: `PolyFunTest/Control/MonadAttach.lean` (judgments, notation,
`Iff.rfl` transfer contract), `PolyFunTest/Do/FreeM.lean` (`mvcgen` smoke
tests), and `PolyFunTest/Do/{Algebra,Support}.lean` (`vcgen` through a locally
installed algebra and through the demonic reading of `SetM`).

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
- **Soundness is the bridge.** On the canonical stack `LawfulWPMonadAttach` with
  `support_subset_of_wp` / `allOutputs_of_wp` convert any sound weakest-precondition
  proof — including a `vcgen`-discharged one — into a support fact; on the legacy
  stack `MonadAttach.toWPSound` and `support_subset_of_wpSPred` / `allOutputs_of_wpSPred`
  play the same role.

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
downstream registrations on reducible unfoldings such as VCVio's `OracleComp`. The demonic
instances are `scoped` under `PFunctor.FreeM.DemonicWP`; the bridges of
`PolyFun/Control/Monad/{Algebra,Support,Hom}/WP.lean` are installed `local` or `scoped` at the
carrier. `vcgen` itself is experimental at this pin (it warns on every call), so production
proofs do not call it; tactic calls live in `PolyFunTest/Do/`, where each asserts the warning
with `#guard_msgs`.

## The two upstream WP stacks

Core ships **two** complete weakest-precondition stacks at the v4.34.0 pin. PolyFun's
canonical interface is the lattice-generic one; the older SPred one is bridged only for the
existing `mvcgen` smoke tests until the free-monad layer moves over.

| | `Std/Internal/Do/` (canonical here) | `Std/Do/` (legacy bridge) |
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

Three practical rules for writing against the canonical stack:

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
