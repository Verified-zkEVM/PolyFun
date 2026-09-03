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
| `PolyFun/Control/Monad/Support.lean` | `ExactMonadAttach m`: the introduction rules core omits for `MonadAttach.CanReturn`; `MonadAttach.support`; the `AllOutputs`/`SomeOutput`/`NoOutput` judgments and scoped `⊨ₐ`/`⊨ₛ`/`⊭` notation with their `pure`/`bind` laws; the named demonic and angelic `MAlgOrdered m Prop` choices |
| `PolyFun/Control/Monad/Support/Instances.lean` | The `MonadLiftT m SetM` shim, transport along lawful lifts, the `MonadAttach` instances core lacks (`Except`, `SetM`) or leaves inexact (`WriterT`), exactness instances for `Id`/`Option`/`OptionT`/`ExceptT`, per-monad `CanReturn` unfoldings |
| `PolyFun/Control/Monad/Support/Indexed.lean` | Per-run support of `StateT`/`ReaderT` (`supportFrom`, `supportAt`) with exact laws and the indexed judgments `⊨ₐ[s]`/`⊨ₛ[s]`/`⊭[s]` |
| `PolyFun/Control/Monad/Support/Structural.lean` | The rest of the `do` fragment for `CanReturn` and the judgments: `<*`, `*>`, `if`, `if h :`, `Option.elim`, `Sum.elim`, `<$>`, `<*>` |
| `PolyFun/Control/Monad/Support/Loops.lean` | Invariant rules for `forIn'`/`forIn`/`foldlM`/`forM` over lists and `PureForIn` containers, for `AllOutputs` (from core's `Spec.*` under the demonic instance) and `SomeOutput` (angelic) |
| `PolyFun/PFunctor/Free/Support.lean` | `MonadAttach`/`ExactMonadAttach` for `FreeM P` with a computable, axiom-free `attach`; structural equations by `rfl`; coherence with `Free/Path.lean` (`support_eq_range_output`) and with the powerset fold (`support_eq_liftM_univ`) |
| `PolyFun/PFunctor/Free/WP.lean` | `OpSpec P l` per-operation specs; syntactic `FreeM.wpFold` (with `demonic`/`angelic`); `OpSpec.toMAlgOrdered`; semantic `FreeM.wpVia` through a `Handler`; soundness `wpFold_le_wpVia`/`wpFold_eq_wpVia` |
| `PolyFun/Control/Do/Spec.lean` | Tactic tier: `@[spec] Spec.forM_list` for `vcgen` |
| `PolyFun/PFunctor/Free/WP/Upstream.lean` | `OpSpec.toWPMonad` (the syntactic fold as a core `WPMonad`), `FreeM.wpMonadOfHandler` (transport along `liftMHom`), and `wpFold_le_wp_liftM`, soundness of op-specs against any core `WPMonad` |
| `PolyFun/ITree/Do.lean` | Productive `while` for interaction trees: `forInLoop`, the scoped `ForIn` instance, and `forInLoop_weakBisim_of_invariant` — an invariant-scoped `WeakBisim` congruence because `iter` is lawful only up to weak bisimulation |
| `PolyFun/PFunctor/Free/Do.lean` | Tactic tier for free programs: scoped demonic and angelic `WPMonad` instances (`open scoped PFunctor.FreeM.DemonicWP` / `AngelicWP`), soundness and conjunctivity instances, and the `@[spec]` lemmas `Spec.lift`, `Spec.liftBind`, `Spec.lift_angelic`, `Spec.lift_ofHandler` that let `vcgen` decompose free programs with uninterpreted operations |
| `PolyFun/Control/Monad/Algebra/WP.lean` | `MAlgOrdered.toWP` / `toWPMonad`: an ordered monad algebra as a core `Std.Internal.Do.WPMonad m l EPost.Nil` (through the `ToCslib.Order.LeanOrder` bridge), `wp` agreement by `rfl`, `toWP_triple_iff`, `wpConjunctiveOf`, and the transfer lemmas `top_eq_top` / `meet_eq_inf` / `join_eq_sup` between core's and Mathlib's lattice operations |
| `PolyFun/Control/Monad/Support/WP.lean` | `MonadAttach.toWPMonadDemonic` / `toWPMonadAngelic`: the always/some judgments as `WPMonad m Prop EPost.Nil`; conjunctivity of the demonic reading; the `LawfulWPMonadAttach` mirror of Lean master's soundness class with its demonic instance; `support_subset_of_wp` / `allOutputs_of_wp` |
| `PolyFun/Control/Monad/Hom/WP.lean` | `MonadHom.transportWP` / `transportWPMonad` / `transportWPMonadOf`: pulling a core `WPMonad` back along a (bundled or unbundled) monad morphism |
| `PolyFun/Control/Monad/Hom/Loops.lean` | A monad morphism commutes with `forIn'`/`forIn`/`forM`/`foldlM`/`mapM` and with `forIn` over `PureForIn` containers (`@[simp, grind =]`) |
| `PolyFun/Control/Do/Spec.lean` | `@[spec] Spec.forM_list`, the list loop core does not specify, for `vcgen` (tactic tier) |

Worked examples: `PolyFunTest/Control/MonadAttach.lean` (judgments, notation,
`Iff.rfl` transfer contract), `PolyFunTest/Do/FreeM.lean` and `PolyFunTest/Do/Loops.lean`
(`vcgen` over free programs, with loops, branching, and `StateT`), and
`PolyFunTest/Do/Transport.lean` (handler-relative interpretation).

## Relation to core `MonadAttach`

The support layer is a three-way split:

- **Core owns the data and canonicity.** `MonadAttach.CanReturn x a` is "`a` is a
  possible output of `x`", `attach` decorates results with proofs of it, and
  `LawfulMonadAttach` pins it down as the strongest postcondition.
- **PolyFun owns the introduction rules.** Core proves only elimination lemmas,
  which bound the support from above; they do not pin it down, since a monad with
  `CanReturn := fun _ _ => False` satisfies `LawfulMonadAttach` vacuously.
  `ExactMonadAttach` adds `canReturn_pure` and `canReturn_bind`, turning each of
  core's implications into the equivalence support reasoning rewrites with.
  Extending `LawfulMonadAttach` rather than the weak class simultaneously excludes
  `MonadAttach.trivial` (`CanReturn := True`, i.e. `support = univ`).
- **Soundness is the bridge.** On the canonical stack `LawfulWPMonadAttach` with
  `support_subset_of_wp` / `allOutputs_of_wp` convert any sound weakest-precondition
  proof — including a `vcgen`-discharged one — into a support fact; on the legacy
  stack `MonadAttach.toWPSound` and `support_subset_of_wpSPred` / `allOutputs_of_wpSPred`
  play the same role.

Core supplies the instances for `Id`, `Option`, `OptionT`, `ExceptT`, `StateT`,
and `ReaderT`; PolyFun adds `Except` and `SetM` (which core lacks), a
single-universe alias for core's `ExceptT` instance (which is declared at
`max`-joined universes and cannot otherwise be synthesized polymorphically), and
the `FreeM P` instance.

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
| `FreeM.lift a`, `FreeM.liftBind a r` | `Spec.lift`/`Spec.liftBind` (`Free/Do.lean`; tail position via `wp_apply_eq`, gotcha 11e) | `Free/Support.lean` (`allOutputs_lift`, `allOutputs_liftBind`) | via `OpSpec.toMAlgOrdered` | — | `wpFold_liftBind` |
| `<*`, `*>` | free | `Support/Structural.lean` | `Algebra.lean` (`wp_seqLeft`/`wp_seqRight`) | `Hom.lean` | `Free/WP.lean` |
| `if`, `if h :` | `vcgen` splits | `Support/Structural.lean` | `wp_ite`/`wp_dite` | `mmap_ite`/`mmap_dite` | `wpFold_ite`/`wpFold_dite` |
| `match` on `Option`/`Sum` | `vcgen` splits | `*_option_elim`/`*_sum_elim` | `wp_option_elim`/`wp_sum_elim` | `mmap_option_elim`/`mmap_sum_elim` | `wpFold_option_elim`/`wpFold_sum_elim` |
| `for` over `List`/`Array`/ranges/`Option`/`Vector` | free (`Spec.forIn'_list`, `forIn_pure` + `PureForIn`) | `Support/Loops.lean` | via the instance | `Hom/Loops.lean` | via `OpSpec.toWPMonad` (`Free/WP/Upstream.lean`) |
| `forM`, `foldlM` | `Spec.foldlM_list` free, `Spec.forM_list` in `Do/Spec.lean` | `Support/Loops.lean` | via the instance | `Hom/Loops.lean` | — |
| `mapM` | — | — | — | `Hom/Loops.lean` | — |
| early `return`/`break`/`continue` | `Invariant.withEarlyReturnNewDo` (core) | via the instance | — | — | — |
| `throw`/`tryCatch` on `ExceptT`/`OptionT` | core's lifted instances (`Spec.tryCatch_ExceptT`) | via the instance | — | `ExceptT.mapHom`/`OptionT.mapHom` | — |
| `get`/`set`/`read` | core's lifted instances | `Support/Indexed.lean` (`supportFrom`, `supportAt`) | — | `StateT.mapHom`/`ReaderT.mapHom` | — |
| `while`/`repeat` | `ITree` only (`ITree/Do.lean`); no rule on finite `FreeM` | — | — | — | — |

Open in this table: the relational (`MAlgRelOrdered`) loop rules, a `mapM` judgment rule, and
`try/catch` through the lifted `ExceptT` instance over a PolyFun base, where `vcgen` currently
reports no applicable spec (see the landscape memo's follow-ups).

## The `Std.Do` quarantine

The definitions (`Std.Do`, `Std.Internal.Do`) may be imported by the program-logic kernel —
`PolyFun/Control/Monad/`, `PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/`,
`PolyFun/ITree/Do.lean` — and by `PolyFunTest/Do/`; the tactics (`Std.Tactic.Do`) only by
`PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/Do.lean`, and `PolyFunTest/Do/`;
`scripts/check-modules.sh` enforces both tiers. The quarantine keeps the dependency on the
fast-moving upstream `vcgen` API confined, and
everything they provide is a construction (`def`), not a global instance —
global `WP` instances on `FreeM` would race downstream registrations on
reducible unfoldings such as VCVio's `OracleComp`. The demonic instances are
`scoped` under `PFunctor.FreeM.DemonicWP`.

## The two upstream WP stacks

Core ships **two** complete weakest-precondition stacks at the v4.34.0-rc2 pin. PolyFun's
canonical interface is the lattice-generic one; nothing in PolyFun instantiates the older
SPred one.

| | `Std/Internal/Do/` (canonical here) | `Std/Do/` (not used) |
|---|---|---|
| Assertions | any `Lean.Order.CompleteLattice` (`Assertion`) | `SPred` / `PostShape` |
| `WPMonad` bind law | inequational (`bind_le_wp_bind`) | equational (`wp_bind : … = …`) |
| Conjunctivity | opt-in, per program (`WPConjunctive x`) | a **field of `PredTrans`**, bi-entailment |
| Exceptions | `EPred` postconditions (`EPost.Nil`, `EPost.Cons`) | `ExceptConds` inside `PostCond` |
| Tactic | `vcgen` | `mvcgen` (deprecated on master) |
| Upstream fate | public `Std.WP` in v4.35 | retired |

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
  with `DemonicWP.wp_apply_eq` and `FreeM.allOutputs_lift` (gotcha 11e).

**Renames at the v4.35 bump** (recorded so the migration is mechanical):
`Std.Internal.Do` → `Std.WP`; `EPost.Nil` → `EStack⟨⟩` and `EPost.Cons eh et` → `eh × et`;
`Std.Internal.Do.Order.*` → `Std.Internal.Order.*`; the local `LawfulWPMonadAttach` is deleted
in favour of `Std.WP.LawfulWPMonadAttach` (same field); `ForIn.forInWithInvariant` →
`forInPureWithInvariant`; `mvcgen` is deprecated.

`MAlgOrdered` stays: it is the Mathlib-lattice kernel VCVio's quantitative carrier bridges to
by `rfl`, and its `WriterT` lift has no core counterpart. The bridge, not a port, is what
connects it to core's order hierarchy.

## What stays downstream

Probability carriers (`evalDist`, SPMF, ℝ≥0∞/`Prob`), couplings and
pRHL/eRHL, concrete handler specifications, verification tactics
(`vcgen`/`mvcgen'` and attribute machinery), and any Loom2 or Iris/Bluebell
dependency. PolyFun ships definitions, rule lemmas, and simp sets only.
