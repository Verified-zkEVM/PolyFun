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
| `PolyFun/Control/Monad/Algebra/Relational.lean` | `MAlgRelOrdered m₁ m₂ l`: relational `rwp`/`RelWP`/`Triple`, asynchronous one-sided bind rules, structural pure rules, side-lifts, and the `StrictBind` / `Anchored` subclasses (Maillard et al. POPL 2020 shapes) |
| `PolyFun/Control/Monad/Support.lean` | `MonadSupport m`: a canonical set-valued support as a monad morphism `supportHom : m →ᵐ SetM`; `supportM`; the `AllOutputs`/`SomeOutput`/`NoOutput` judgments and scoped `⊨ₐ`/`⊨ₛ`/`⊭` notation; the demonic `MAlgOrdered m Prop` instance |
| `PolyFun/PFunctor/Free/Support.lean` | The canonical `MonadSupport (FreeM P)` (every response possible) and its coherence with `Free/Path.lean` (`supportM_eq_range_output`) |
| `PolyFun/PFunctor/Free/WP.lean` | `OpSpec P l` per-operation specs; syntactic `FreeM.wpFold` (with `demonic`/`angelic`); `OpSpec.toMAlgOrdered`; semantic `FreeM.wpVia` through a `Handler`; soundness `wpFold_le_wpVia`/`wpFold_eq_wpVia` |
| `PolyFun/Control/Do/Basic.lean` | Core-`Std.Do` transports: `MonadHom.transportWP(Monad)` along a monad morphism, `MonadSupport.toWP(Monad)` demonically at `.pure` |
| `PolyFun/PFunctor/Free/Do.lean` | Scoped demonic `WP (FreeM P) .pure` instances (`open scoped PFunctor.FreeM.DemonicWP`), `wpMonadOfHandler`, and the `Spec.lift` `@[spec]` lemma enabling `mvcgen` on free programs with uninterpreted operations |

Worked examples: `PolyFunTest/Control/MonadSupport.lean` (judgments, notation,
`Iff.rfl` transfer contract) and `PolyFunTest/Do/FreeM.lean` (`mvcgen` smoke
tests).

## Always / never judgments

For `[MonadSupport m]` and `x : m α` (`open scoped MonadSupport`):

- `x ⊨ₐ p` (`AllOutputs p x`): every possible output satisfies `p` —
  definitionally `∀ a ∈ supportM x, p a`.
- `x ⊨ₛ p` (`SomeOutput p x`): some possible output satisfies `p`.
- `x ⊭ p` (`NoOutput p x`): no possible output satisfies `p`.

These stay `Iff.rfl`-convertible to their bounded-quantifier spellings — a
contract pinned by tests — so downstream support-based statements transfer
without rewriting. `triple_top_iff_allOutputs` identifies `x ⊨ₐ p` with the
trivial-precondition `Prop`-carrier triple, and on `FreeM` the judgments
recurse structurally (`allOutputs_liftBind` and friends) and agree with the
demonic/angelic `wpFold` (`wpFold_demonic_iff_allOutputs`).

`StateT` and `ReaderT` have no `MonadSupport` instance on purpose: the union
over initial states is not a monad morphism. State such facts per run,
`supportM (x.run s)`.

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
