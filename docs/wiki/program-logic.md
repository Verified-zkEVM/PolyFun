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
| `PolyFun/Control/Monad/Support.lean` | `ExactMonadAttach m`: the introduction rules core omits for `MonadAttach.CanReturn`; `MonadAttach.support`; the `AllOutputs`/`SomeOutput`/`NoOutput` judgments and scoped `⊨ₐ`/`⊨ₛ`/`⊭` notation; the named demonic `MAlgOrdered m Prop` choice; instances for `Except`/`SetM` (absent upstream) and the `ExceptT` universe alias |
| `PolyFun/PFunctor/Free/Support.lean` | `MonadAttach`/`ExactMonadAttach` for `FreeM P` with a computable, axiom-free `attach`; structural equations by `rfl`; coherence with `Free/Path.lean` (`support_eq_range_output`) and with the powerset fold (`support_eq_liftM_univ`) |
| `PolyFun/PFunctor/Free/WP.lean` | `OpSpec P l` per-operation specs; syntactic `FreeM.wpFold` (with `demonic`/`angelic`); `OpSpec.toMAlgOrdered`; semantic `FreeM.wpVia` through a `Handler`; soundness `wpFold_le_wpVia`/`wpFold_eq_wpVia` |
| `PolyFun/Control/Do/Basic.lean` | Core-`Std.Do` transports: `MonadHom.transportWP(Monad)` along a monad morphism, `MonadAttach.toWP(Monad)` demonically at `.pure`, `toWPSound` for core-sense soundness, and `support_subset_of_wp`/`allOutputs_of_wp` turning any `WPSound` triple into a support fact |
| `PolyFun/ITree/Do.lean` | Productive `while` for interaction trees: `forInLoop`, the scoped `ForIn` instance, and `forInLoop_weakBisim_of_invariant` — an invariant-scoped `WeakBisim` congruence because `iter` is lawful only up to weak bisimulation |
| `PolyFun/PFunctor/Free/Do.lean` | Scoped demonic `WP (FreeM P) .pure` instances (`open scoped PFunctor.FreeM.DemonicWP`), `wpMonadOfHandler`, and the `Spec.lift` `@[spec]` lemma enabling `mvcgen` on free programs with uninterpreted operations |

Worked examples: `PolyFunTest/Control/MonadAttach.lean` (judgments, notation,
`Iff.rfl` transfer contract) and `PolyFunTest/Do/FreeM.lean` (`mvcgen` smoke
tests).

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
- **`WPSound` is the bridge.** `MonadAttach.toWPSound` proves PolyFun's demonic
  interpretation sound in core's sense, and `support_subset_of_wp` /
  `allOutputs_of_wp` convert any `WPSound` weakest-precondition proof — including
  an `mvcgen`-discharged one — into a support fact.

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

## The `Std.Do` quarantine

Only `PolyFun/Control/Do/Basic.lean` and `PolyFun/PFunctor/Free/Do.lean` (and
`PolyFunTest/Do/`) may import `Std.Do`, `Std.Internal.Do`, or `Std.Tactic.Do`;
`scripts/check-modules.sh` enforces all three spellings. The quarantine keeps the
dependency on the fast-moving upstream `mvcgen` / `vcgen` API confined to two files, and
everything they provide is a construction (`def`), not a global instance —
global `WP` instances on `FreeM` would race downstream registrations on
reducible unfoldings such as VCVio's `OracleComp`. The demonic instances are
`scoped` under `PFunctor.FreeM.DemonicWP`.

## The two upstream WP stacks

Core ships **two** complete weakest-precondition stacks at the v4.34.0-rc2 pin, and PolyFun
bridges the older one. Knowing which is which matters, because they differ on exactly the
property that decides what PolyFun can express.

| | `Std/Do/` (bridged here) | `Std/Internal/Do/` |
|---|---|---|
| Assertions | `SPred` / `PostShape` | any `Lean.Order.CompleteLattice` |
| `WPMonad` bind law | equational (`wp_bind : … = …`) | inequational (`bind_le_wp_bind`) |
| Conjunctivity | a **field of `PredTrans`**, bi-entailment | opt-in class `WPConjunctive`, one-directional |
| Soundness | `WPSound`, via `Internal.Ensures` | — |
| Also has | — | `WP.Frames`, `frameClosure`, `PreservesSup`, `RepeatInvariant` |
| Visibility | public | `Internal` |

**The conjunctivity field is why the WP bridge is demonic-only.** `Std.Do.PredTrans` requires
`t (Q₁ ∧ₚ Q₂) ⊣⊢ₛ t Q₁ ∧ t Q₂`. `AllOutputs` distributes over `∧` in both directions, so
`MonadAttach.toWP` discharges it. `SomeOutput` distributes only left-to-right — two different
outputs may witness the two conjuncts separately — so there is no angelic `Std.Do.WP` at all.
That is a structural obstruction, not an unwritten lemma;
`PolyFunTest/Control/MonadAttach.lean` proves both directions and the failure. The angelic
reading therefore lives at the `MAlgOrdered` level, whose `μ_bind_mono` asks only for
monotonicity.

**What changes upstream.** Beyond this pin, core promotes `Std.Internal.Do` verbatim to a
public `Std.WP`, replaces `WPSound` with `Std.WP.LawfulWPMonadAttach` — whose one field
concludes from a `MonadAttach.CanReturn` witness directly, dropping the `Ensures`
formulation — and deprecates `mvcgen` in favour of `vcgen`. All three ship in **v4.35**, not
v4.34. Two consequences for this layer: `support_subset_of_wp` / `allOutputs_of_wp` are
already stated against `CanReturn`, so they carry over as a rename; and `WPConjunctive`
being opt-in is what would unblock an angelic bridge. Its one law is exactly the reverse
conjunction direction refuted by the test, so that bridge would not provide the optional
class.

`MAlgOrdered` is recognisably `Std.Internal.Do.WPMonad` minus exception postconditions — but
over Mathlib's `CompleteLattice`, while every piece of core WP machinery is over
`Lean.Order.CompleteLattice`, and the pinned Mathlib contains no bridge between the two
hierarchies. Adopting core's stack means porting `MAlgOrdered` off Mathlib's order hierarchy.
That cost is recorded here deliberately; it is not this layer's current direction.

## What stays downstream

Probability carriers (`evalDist`, SPMF, ℝ≥0∞/`Prob`), couplings and
pRHL/eRHL, concrete handler specifications, verification tactics
(`vcgen`/`mvcgen'` and attribute machinery), and any Loom2 or Iris/Bluebell
dependency. PolyFun ships definitions, rule lemmas, and simp sets only.
