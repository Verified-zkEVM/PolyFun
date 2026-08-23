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
| `PolyFun/Control/Monad/Algebra/Relational.lean` | `MAlgRelOrdered m₁ m₂ l`: relational `rwp`/`RelWP`/`Triple`, asynchronous one-sided bind rules, structural pure rules, explicit named side lifts, and the `StrictBind` / `Anchored` subclasses (Maillard et al. POPL 2020 shapes) |
| `PolyFun/Control/Monad/Support.lean` | `ExactMonadAttach m`: the introduction rules core omits for `MonadAttach.CanReturn`; `MonadAttach.support`; the `AllOutputs`/`SomeOutput`/`NoOutput` judgments and scoped `⊨ₐ`/`⊨ₛ`/`⊭` notation; the named demonic `MAlgOrdered m Prop` choice; instances for `Except`/`SetM` (absent upstream) and the `ExceptT` universe alias |
| `PolyFun/PFunctor/Free/Support.lean` | `MonadAttach`/`ExactMonadAttach` for `FreeM P` with a computable, axiom-free `attach`; structural equations by `rfl`; coherence with `Free/Path.lean` (`support_eq_range_output`) and with the powerset fold (`support_eq_liftM_univ`) |
| `PolyFun/PFunctor/Free/WP.lean` | `OpSpec P l` per-operation specs; syntactic `FreeM.wpFold` (with `demonic`/`angelic`); `OpSpec.toMAlgOrdered`; semantic `FreeM.wpVia` through a `Handler`; soundness `wpFold_le_wpVia`/`wpFold_eq_wpVia` |
| `PolyFun/Control/Do/Basic.lean` | Core-`Std.Do` transports: `MonadHom.transportWP(Monad)` along a monad morphism, `MonadAttach.toWP(Monad)` demonically at `.pure`, `toWPSound` for core-sense soundness, and `support_subset_of_wp`/`allOutputs_of_wp` turning any `WPSound` triple into a support fact |
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
  definitionally `∀ a ∈ support x, p a`.
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
continuation may observe a state the prefix never produced. The test suite proves
both introduction rules fail there. Reason per run instead, via
`mem_support_stateT_iff`. Oracle- and state-relative supports belong at the
specification layer (`PFunctor/Free/WP.lean`), which indexes the notion by a
per-operation answer assignment.

The support-based `MAlgOrdered m Prop` and relational transformer lifts are
explicit named definitions, not unrestricted global instances. This keeps
support partial correctness distinct from the existing failure-as-`⊥`
`OptionT`/`ExceptT` algebras and prevents inequivalent left/right transformer
instance paths. Install the intended algebra locally at each verification
boundary.

## The `Std.Do` quarantine

Only `PolyFun/Control/Do/Basic.lean` and `PolyFun/PFunctor/Free/Do.lean` (and
`PolyFunTest/Do/`) may import `Std.Tactic.Do`. The quarantine keeps the
dependency on the fast-moving upstream `mvcgen` API confined to two files, and
everything they provide is a construction (`def`), not a global instance —
global `WP` instances on `FreeM` would race downstream registrations on
reducible unfoldings such as VCVio's `OracleComp`. The demonic instances are
`scoped` under `PFunctor.FreeM.DemonicWP`.

## What stays downstream

Probability carriers (`evalDist`, SPMF, ℝ≥0∞/`Prob`), couplings and
pRHL/eRHL, concrete handler specifications, verification tactics
(`vcgen`/`mvcgen'` and attribute machinery), and any Loom2 or Iris/Bluebell
dependency. PolyFun ships definitions, rule lemmas, and simp sets only.
