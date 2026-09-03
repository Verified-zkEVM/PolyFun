# Upstream alignment survey

A ledger of PolyFun's general-purpose machinery against what Lean core, Batteries,
Mathlib, and cslib already provide, with a verdict for each entry: **adopt** what
upstream owns, **keep** what is genuinely PolyFun's, **upstream** what belongs
elsewhere, and **track** what is on its way to core.

Companion files: `program-logic-landscape.md` (the verification-tooling landscape),
`coalgebra-related-work.md` (coalgebras in other provers), `roadmap.md`.

## Why this file exists

PolyFun hand-rolled a `MonadSupport` class before discovering that Lean core had
shipped `MonadAttach` — the same abstraction, with a lawfulness hierarchy and a
`Std.Do` soundness bridge — five releases earlier. The cost was not the deleted code;
it was the design time spent rediscovering an interface, and the near-miss of
publishing a competing one.

That was drift, not bad luck. PolyFun's generic layers were written against an
ecosystem that has since moved: cslib grew a full labelled-transition-system library,
core grew a monad-lifting lawfulness family and a lattice-generic weakest-precondition
stack, and Batteries deprecated the `SatisfiesM` line in favour of core's. This file
is the periodic check against that drift.

The rule it encodes: **PolyFun should own the polynomial-functor and interaction
content, and as little else as it can get away with.**

## Method, and how to repeat it

Every claim below was checked against source on disk, not recalled.

| Tree | Revision surveyed | Compared against |
|---|---|---|
| Lean core | **v4.34.0-rc2** | `master`, via the GitHub API |
| Mathlib | v4.34.0-rc2 (`85e3a25e00`) | `origin/master` |
| cslib | v4.34.0-rc2 (`2255a5b5`) | `origin/main` |
| Batteries | `d54dddc58` | `origin/main` + live GitHub search |

Re-run at the v4.34.0-rc2 pin (2026-09). The previous baseline was v4.33.1, and this
time the pin move is *not* content-free: `diff -rq` over the v4.33.1 and v4.34.0-rc1
toolchains' `src/lean` trees touches 201 files, and rc1→rc2 additionally changes
`Init/Core`, `Init/Prelude`, `Init/Data/Bool`, `Init/Data/Int/Linear`, `Init/Grind/*`, and
`Lean/Elab/Tactic/Do/Contract.lean`; cslib moves 63 files over 16 commits. The one change
that reached PolyFun's build is the deprecation of `if_pos` / `if_neg` / `dif_pos` /
`dif_neg` in favour of `ite_eq_left` / `ite_eq_right` / `dite_eq_left` / `dite_eq_right`
(statement-identical aliases, `Init/Core.lean`), renamed at every call site. Rows below
that changed verdict at this re-run say so explicitly; the rest were re-checked against the
rc2 trees.

Availability is always reported **at the survey baseline**. Where something exists
only upstream, it is filed under *Track*, not *Adopt*.

Two traps worth recording for whoever repeats this:

- A toolchain directory named `nightly-<later date>` is not necessarily newer. Check
  `bin/lean --version`, not the directory name.
- **The "newest local `vX.Y.0-rc*` toolchain" proxy no longer works**, and following it
  silently surveys the pin against itself. At this re-run the newest toolchain on disk
  *was* the pin, and the `nightly-2026-01-22` directory the previous survey named does
  not exist any more. Use the GitHub API (`gh api repos/leanprover/lean4/contents/...`
  at an explicit `?ref=`) or a real clone. Pin comparisons must also name a *tag*:
  several findings below are on `master` but absent from `v4.34.0-rc2`, so they ship in
  v4.35 and a v4.34 bump would buy none of them.
- Absence is harder to establish than presence, and it is where the first guess is
  most often wrong. For *abstractions*, claims of "nothing upstream has this" below
  come from grepping the full pinned trees for the class/def keyword, not just the
  name PolyFun happens to use. For individual *lemmas*, they come from running
  `exact?` against full Mathlib on the exact statement — a lemma that "looks like it
  must exist" repeatedly turned out not to.

## Ledger

### Adopt — upstream owns it, PolyFun duplicates it

| PolyFun | Upstream | At the pin? | Status |
|---|---|---|---|
| `Control/Bisimulation.lean`, `Control/LTS/Trace.lean` | `Cslib.LTS` and its `Simulation` / `Bisimulation` / `HasTau` / `TraceEq` theory | yes | **partial** — the cslib bridge is in (`toLts`, `instHasTauOption`, the `↔`-correspondences), but the strong/weak spectrum is still redeveloped locally and `LTS/Trace.lean` still defines its own `WeakTrace` |
| `Interaction/Concurrent/Fairness.lean`, `Liveness.lean` — the `Always` / `Eventually` / `EventuallyAlways` / `InfinitelyOften` block | `Filter.atTop` | yes | **done** |
| `Control/Trace.lean` `mapHom` | `MonoidHom.compLeft`, `Mathlib/Algebra/Group/Pi/Lemmas.lean` | yes | **done** — `mapHom` is literally `φ.compLeft X` |
| `PFunctor/Supply.lean` `List.take_set_self` / `drop_set_self` | `List.take_set_of_le` (`Init/Data/List/Nat/TakeDrop.lean:119`), `List.drop_set_of_lt` (`:375`) | yes | **done** — previously mis-filed under *Upstream*; both were already in core |
| `Control/Monad/Hom.lean` | `LawfulMonadLift` / `LawfulMonadLiftT`, `Init/Control/Lawful/MonadLift/` | yes | **bridge, not adopt** — see below; core has no bundled monad hom, so `MonadHom` stays and `MonadHom.ofLift` connects it |

#### Transition systems

`Cslib/Foundations/Semantics/LTS/` is a substantially larger development than its
file names suggest, and cslib is already a pinned PolyFun dependency:

- `Basic.lean`: `LTS State Label` (a single field, `Tr : State → Label → State → Prop`),
  multi-step `MTr` with a `grind`-annotated API, `CanReach`, `generatedBy`,
  `Deterministic`, `image` / `setImage`, `FinitelyBranching`, `Bounded`, `Terminating`,
  `Acyclic`.
- `HasTau.lean`: `HasTau Label`, the silent closure `τSTr`, the saturated transition
  `STr`, `saturate`, `τClosure`, saturated multi-step `SMTr`.
- `Simulation.lean` / `Bisimulation.lean`: `IsSimulation`, `Similarity`,
  `SimulationEquiv`, `IsBisimulation`, `Bisimilarity`, `IsWeakBisimulation`,
  `WeakBisimilarity`, and `IsSWBisimulation` with the soundness/completeness bridge
  `isWeakBisimulation_iff_isSWBisimulation`. Plus `Bisimilarity.gfp`, a
  `SemilatticeSup` / `BoundedOrder` structure on the type of bisimulations, and
  bisimulation-up-to (`IsBisimulationUpTo`, `UpToHomBisimilarity`).
- `TraceEq.lean`: `traces`, `TraceEq`, `Bisimilarity.le_traceEq`,
  `Deterministic.bisim_tfae`.
- `Execution.lean`, `OmegaExecution.lean`, `Divergence.lean`, `Termination.lean`,
  `Total.lean`, `Union.lean`, `MapLabel.lean`, `Reverse.lean`, and `LTSCat/Basic.lean`
  — the latter making the category of LTSs an actual `CategoryTheory.Category`.

Scoped notation: `s ~[lts₁,lts₂] s'` (bisimilarity), `≈[·]` (weak), `≤[·]`
(similarity), `≤≥[·]` (simulation equivalence), `~tr[·]` (trace equivalence).

PolyFun's `Control.LTS` differs in one respect that is worth keeping: it is
*move-indexed* (`Move : State → Type`, `next`, `label`) rather than relation-indexed,
which is the polynomial-coalgebra presentation and the reason the dynamical layer can
adapt into it. That shape is PolyFun's; the theory over it is not. The bridge is one
definition and one instance:

```lean
instance : Cslib.HasTau (Option Obs) := ⟨none⟩
def Control.LTS.toLts (L : LTS Obs) : Cslib.LTS L.State (Option Obs) := ⟨L.Step⟩
```

with `SilentSteps` ⇝ `τSTr`, `WeakStep` ⇝ `STr`, and `WeakTrace` / `traces` ⇝ `SMTr` /
`traces`.

**The one genuine gap is delay bisimulation.** cslib has strong and weak/saturated
only. PolyFun's delay flavour is load-bearing — `Interaction/UC/OpenProcess.lean` uses
`DelayBisimulationEquivalent` for `OpenProcessActivationEquiv`, because the structural
`openTheory` laws prove the stronger delay notion, not merely weak bisimulation. Keep
it locally; it is the clearest upstream contribution candidate in this survey.
Branching bisimilarity and fairness over `OmegaExecution` are also absent from cslib.

#### Temporal operators

`Interaction/Concurrent/Fairness.lean` defines

```lean
def EventuallyAlways (P : Nat → Prop) : Prop := ∃ N, ∀ n, N ≤ n → P n
def InfinitelyOften  (P : Nat → Prop) : Prop := ∀ N, ∃ n, N ≤ n ∧ P n
```

and `Liveness.lean` repeats the pattern over run states. These are definitionally
Mathlib's filter operators at `atTop`:

```lean
theorem Filter.eventually_atTop  : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b, a ≤ b → p b
theorem Filter.frequently_atTop  : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b, a ≤ b ∧ p b
```

Adopting them replaces the hand-proved monotonicity lemmas with
`Filter.Eventually.mono` / `Filter.Frequently.mono` and connects the fairness
definitions to the rest of Mathlib's filter API. cslib's
`Foundations/Data/OmegaSequence/Temporal.lean` already uses `∀ᶠ` / `∃ᶠ` for exactly
this purpose, so it is also the idiom of the nearest neighbour.

#### Monad morphisms

Core ships, at the pin, an *unbundled* monad-morphism class with a full instance zoo
and a `liftM_*` simp set:

```lean
class LawfulMonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [Monad n] [inst : MonadLift m n] : Prop where
  monadLift_pure {α} (a : α) : inst.monadLift (pure a) = pure a
  monadLift_bind {α β} (ma : m α) (f : α → m β) :
    inst.monadLift (ma >>= f) = inst.monadLift ma >>= (fun x => inst.monadLift (f x))
```

with a transitive-closure variant `LawfulMonadLiftT`, instances for `StateT`,
`ReaderT`, `OptionT`, `ExceptT`, `StateRefT'`, `StateCpsT`, `ExceptCpsT`, and
reflexivity/transitivity instances. There is **no bundled** monad-hom structure in
core, so PolyFun's `MonadHom` / `→ᵐ` is not redundant — but it should interoperate
with this family rather than ignore it. This is the substance of issue #118, and is
what `MonadHom.ofLift` now does. The Adopt row above is therefore mislabelled in
spirit: the verdict is *keep and bridge*, not *adopt*.

Mathlib does, however, have `MonadHom`'s **structural twin**, which the previous survey
missed: `ApplicativeTransformation F G` (`Mathlib/Control/Traversable/Basic.lean:77`) is
a bundled `app : ∀ α, F α → G α` with two preservation laws, a `CoeFun`, `@[ext]`,
`idTransformation`, `comp`, `comp_assoc`, and a `@[functor_norm]` simp set — the same
API shape at the same universe level, preserving `pure`+`seq` where `MonadHom`
preserves `pure`+`bind`. It does not subsume `MonadHom`, but it is the naming and
simp-set template to follow, and `Hom.lean`'s "neighbouring upstream APIs" paragraph
should cite it alongside `LawfulMonadLift(T)` and Batteries' `LawfulAlternativeLift`.

### Keep — genuinely absent upstream

| PolyFun | Why |
|---|---|
| `Control/Comonad/Basic.lean` | There is no `Type`-level `Comonad` class in core, Batteries, Mathlib, or cslib. Mathlib has only the categorical `CategoryTheory.Comonad`. PolyFun's is the only one in the ecosystem. |
| `Control/Monad/Iter.lean` | Nothing upstream axiomatises Elgot/Conway iteration. The nearest concrete instance is `PFun.fix : (α →. β ⊕ α) → (α →. β)` — the same `β ⊕ α` shape — and core's `Lean.Order.MonadTail` unrolling lemmas, which are `Init/Internal/` with no stability promise. |
| `Control/Monad/Algebra.lean` `MonadAlgebra` | No non-categorical Eilenberg–Moore class upstream. |
| `Control/Coalgebra.lean` `Coalg` | Mathlib's `CategoryTheory.Endofunctor.Coalgebra` is bundled in an arbitrary category; the `Type`-level unbundled form is not upstream. Worth borrowing upstream *names* (`isoMk`, `forget`, `functorOfNatTrans`, and `Terminal.strInv` for Lambek's lemma). |
| The `Poly` categorical layer — lenses, charts, comonoids, `SubstMonoid`, `Display`, `Cofree`, `InternalHom`, wiring | Mathlib's `PFunctor` is a bare `⟨A, B⟩` used only as scaffolding for W-types, M-types, and QPF. It has no lenses, charts, category instance, or monoidal structure. This is PolyFun's actual contribution. |
| Delay bisimulation | See above. |

### Upstream — belongs elsewhere, PolyFun is the wrong home

cslib is already PolyFun's upstreaming channel: the `PFunctor` basic API is being moved
there, and cslib's `PFunctor.FreeM` is the free monad PolyFun builds on.

- **cslib**: delay bisimulation over `LTS` (see above). Also
  `Cslib.LTS.Bisimilarity.symm`, which is stated for a single state type while its
  weak counterpart `WeakBisimilarity.symm` is cross-type — PolyFun needs the
  cross-type, cross-universe form in both flavours, so that one does not transport.
  And `instance : HasTau (Option α) := ⟨.none⟩`, which cslib has but only inside
  `Computability/Automata/EpsilonNA/Basic.lean`; it belongs next to `HasTau` itself,
  so that reaching it does not mean importing the ε-NFA development.
- ~~**Batteries**: a bundled `MonadHom`, matching the in-flight draft.~~ **Withdrawn —
  no such draft could be found.** Four independent checks came back empty: `git grep`
  across all 3840 refs of a Batteries clone, a GitHub issue/PR search, a GitHub code
  search, and a scan of open PR titles. The only bundled `MonadHom` in the ecosystem is
  Mathlib's categorical one. Treat this row as unfounded unless a link is produced.
- **Lean core**: the `MonadAttach (ExceptT ε m)` universe bug, which forces a
  single-universe alias in the support layer and is **not** fixed on `master`.
  `MonadAttach (Except ε)` was also filed here; it has since landed upstream
  character-for-character (`Init/Control/Except.lean:333` on `master`, absent from
  `v4.34.0-rc2`, so shipping in **v4.35**). PolyFun's local instance is marked for
  deletion at that bump; the `ExactMonadAttach (Except ε)` half stays, since core does
  not ship the introduction rules.
- **Mathlib**: the small helpers below. Each was checked with `exact?` against full
  Mathlib and **none** is subsumed, so they are contributions rather than reuse — the
  opposite of the first guess, which is why the check matters:
  - `Logic/HEq.lean`'s `dependent_apply_heq` and `Prod.mk_heq`. Neighbours exist
    (`congr_arg_heq`, `eqRec_heq_iff`, `Subtype.heq_iff_coe_eq`) but neither lemma
    follows from them by `exact?`. The file's own docstring already says they "belong
    in Mathlib".
  - `heq_forall_iff` and `instIsEmptySigma`, currently parked in `section find_home`
    blocks in `PFunctor/Lens/Basic.lean` and `PFunctor/Equiv/Basic.lean`.

### Track — heading into core, not ready to adopt

#### Core is absorbing Loom's weakest-precondition design

**There are two complete WP stacks at the pin, and PolyFun bridges the other one.** The
tree described here is `Std/Internal/Do/`; the one `Control/Do/Basic.lean` and
`PFunctor/Free/Do.lean` target is the public `Std/Do/`, which is `SPred`/`PostShape`-indexed
and older. Confusing them is easy and consequential — they differ on conjunctivity, which
decides what PolyFun can express. The comparison table and that consequence are in
[`docs/wiki/program-logic.md`](../wiki/program-logic.md#the-two-upstream-wp-stacks); the
short version is that `Std.Do.PredTrans` makes conjunctivity a *structure field* stated as a
bi-entailment, which is why the demonic support reading has a `WP` instance and the angelic
one provably cannot.

At the pin, `Std/Internal/Do/` contains a lattice-generic weakest-precondition stack:

```lean
-- Std/Internal/Do/Assertion.lean
class abbrev Assertion (α : Type w) := CompleteLattice α        -- Lean.Order.CompleteLattice

-- Std/Internal/Do/WP/Basic.lean
class WP (Prog : Type u) (Value : outParam (Type v))
    (Pred : outParam (Type w)) (EPred : outParam (Type w')) where
  wpTrans : Prog → PredTrans Pred EPred Value
  wp_trans_monotone (x : Prog) : wpTrans x |>.monotone
```

together with `WP/Frame.lean`, `WP/Conjunctive.lean`, `Triple/`, and an `Order/`
subtree. Upstream of the pin this whole tree was renamed out of `Internal` into a
public `Std.WP` namespace (#14783) and gained `Std.WP.LawfulWPMonadAttach` (#14801),
whose single field concludes from a `MonadAttach.CanReturn` witness directly and which
**drops the `Std.Do.Internal.Ensures` formulation** that `MonadAttach.toWPSound` is built
on. Timing matters here: `src/Std/` at `v4.34.0-rc2` still has no `WP` directory, so all
of this lands in **v4.35**, and a v4.34 bump buys none of it.

This is structurally PolyFun's `MAlgOrdered` — a monotone predicate transformer into a
complete lattice — and core's frame and conjunctivity layers sit where a relational
extension of it would sit. Its author is the first author of the Loom paper that
`Control/Monad/Algebra.lean` credits. In other words, the lattice-generic program logic
PolyFun adapted from Loom, and that VCVio depends on a pinned Loom fork for, is being
upstreamed into Lean core.

**Verdict: track, do not adopt yet.** Three reasons:

1. It is `Std.Internal` at the pin and public only from v4.35.
2. It is churning: several breaking refactors landed in the week this survey was
   written, and more since.
3. It is built on `Lean.Order.CompleteLattice`, while `MAlgOrdered` uses Mathlib's.
   Reconciling those is real work, not a rename — and the gap is total: `Lean.Order`
   has **zero** occurrences anywhere in the pinned Mathlib. No instance, no coercion,
   no bridge lemma. Adopting core's stack means porting `MAlgOrdered` off Mathlib's
   order hierarchy. (`Lean.Order.PartialOrder` is on `Sort u` with `⊑` and no `LE`
   superclass; its `CompleteLattice.sup` takes a *predicate* where Mathlib's `sSup`
   takes a `Set`. Same data, no connective tissue. The `Std.Internal.Do` extension's
   `scoped notation` for `⊓`/`⊔`/`⊤`/`⨅` also collides with Mathlib's.)

Revisit after a toolchain bump. Recording the trajectory now is the point — this is
exactly the drift that produced the `MonadSupport` situation.

#### `mvcgen` is deprecated in favour of `vcgen`

Upstream marks `mvcgen` deprecated via `deprecated_syntax`, directing users to `vcgen`
(#14874, `since := "2026-08-21"`). That deprecation is on `master` only — not at the
`v4.34.0-rc2` pin — so it is a **v4.35** item. `vcgen` itself already exists at the pin
(`Std/Tactic/Do/Syntax.lean:464`), **but it is not a drop-in replacement for PolyFun's
`mvcgen` uses**: `vcgen` consumes `Std.Internal.Do.WPMonad` / `Std.Internal.Do.Triple`
(`Lean/Elab/Tactic/Do/Internal/VCGen/Frontend.lean`), not the `Std.Do.WP` structures
PolyFun's bridge provides. Retargeting therefore needs Internal-stack instances first, not a
toolchain bump; the previous claim that it "needs no toolchain bump and can be done whenever
convenient" was wrong on that point.

Relatedly, `Batteries.Classes.SatisfiesM` has been deprecated in favour of
`Std.Do.Triple`. The `SatisfiesM` / `MonadSatisfying` line — the other abstraction
PolyFun's support layer resembled — is superseded by core's `MonadAttach` plus
`Std.Do.Triple`.

#### Coinductive predicates in core

`ITree/Bisim/Defs.lean` builds weak bisimulation as an explicit Tarski greatest
fixpoint (`∃ R, R t s ∧ closure`), justified in its docstring by core's *syntactic*
monotonicity checker. Core has since shipped a `coinductive` command for coinductive
predicates, implemented via a reverse-implication order plus `partial_fixpoint`. Note
the command is **at the pin**, not only upstream — the previous "has since shipped"
phrasing read as upstream-only.

The two pieces of work-in-progress named previously have both **merged**: `monotonicity_by`
on `coinductive` / `inductive` predicate declarations (#14861), and strong (co)induction
principles for lattice-theoretic predicates — `strong_coinduct`, `strong_induct`,
`strong_mutual_induct`, all derived from a strengthened Park theorem (#14855). Both are
absent from `v4.34.0-rc2`, so again **v4.35**. Calibrate the payoff: `strong_coinduct` is
up-to-*reflexivity* (the candidate is joined by disjunction with the predicate itself), not
up-to-bisimilarity or a Pous-style companion — there is no compatibility class anywhere in
core, so ITree's up-to techniques stay hand-rolled either way.

At the pin there is also **no escape hatch for the `coinductive` command specifically**: the
parser has no slot for one, so a declaration whose functor `Lean.Order.monotonicity` cannot
handle must be written manually as `def … coinductive_fixpoint monotonicity …`. That is what
#14861 fixes.

Both address the objection `ITree/Bisim/Defs.lean`'s docstring raises. Worth re-evaluating at
v4.35; it touches the whole bisimulation development, so it is not a small change. Note the
alternative available *today*: Mathlib's `OrderHom.gfp` with `gfp_induction` (`Mathlib/Order/
FixedPoints.lean`) is the same greatest-fixpoint theory on the relation lattice, and cslib
already states `Bisimilarity.gfp` that way.

#### cslib beyond the pin

cslib `main` is ahead of PolyFun's pin and on a newer toolchain. Relevant additions:
`Computability/Languages/SafetyLiveness.lean` (the Alpern–Schneider safety/liveness
decomposition — closed sets are safety, dense sets are liveness), and
`Foundations/Data/OmegaSequence/Topology.lean`. Both overlap
`Interaction/Concurrent/Liveness.lean`.

Of the **three** breaking changes previously recorded, two landed with the v4.34.0-rc2
bump and one is still ahead of the pin:

1. *(landed at the pin, unused by PolyFun)* `LTS.Execution` is a `structure` (fields
   `length` / `start` / `last` / `trans`) instead of a `Prop`, with attribute
   `@[scoped grind]` instead of `@[scoped grind =]`. PolyFun does not destructure it.
2. *(landed at the pin, unused by PolyFun)* `LTS.Deterministic` is refactored: the single
   field is `∀ s, lts.DeterministicState s`, layered over `DeterministicStateLabel` /
   `DeterministicState`, with `not_tr_of_ne`, `image_singleton_iff_tr`, `image_char`, and
   `DeterministicStateLabel.finite_image`; the `Finite (lts.image s μ)` instance remains.
3. *(still beyond the pin)* `MapLabel.lean` is deleted in favour of a new `MapHom.lean` on
   `main`, so direct imports of the old module will break at the next bump. The `mapLabel`
   definition and its main lemmas survive in the new module, reimplemented through the more
   general `Hom.lift` API. `MapLabel.lean` still exists at `v4.34.0-rc2`.

Still absent on `main`, so still genuine upstreaming targets: delay bisimulation, a
well-placed `HasTau (Option α)`, and a cross-type `Bisimilarity.symm`.

## Unused surface

Not upstream duplicates, so secondary to this survey — but each deserves an explicit
verdict rather than being left to accrete. The declarations below have sparse or no
*named* in-repo uses across `PolyFun/` and `PolyFunTest/`:

**Every row of the previous version of this table was stale**, in both directions — two
described files that no longer exist, one described contents that had been replaced, and
one called a load-bearing file retirement-ready. The cause was grepping *import paths*
rather than declaration names; a file can be imported and unused, or unimported and
load-bearing through a re-export. Check declaration base names across `PolyFun/` and
`PolyFunTest/`, excluding each declaration's own file, and separate "unused **and**
untagged" (a real signal) from "unused but `@[simp]`/`@[grind]`-tagged" (automation
leaves no textual trace). The same caveat applies more strongly to typeclass instances:
instance synthesis leaves no textual reference at all. A declaration-name search can
identify candidates, but cannot by itself establish that an instance-providing public
module is orphaned or safe to remove.

| Surface | Lines | Verdict |
|---|---:|---|
| `Control/Comonad/Instances.lean` — `NonEmptyList`, `List.Zipper`, `EnvT`, `StoreT`, `Day` | 898 | **No named in-repo consumer, but not proved orphaned.** It is publicly imported by `PolyFun.lean` and contributes 65 typeclass instances, so downstream and in-repo typeclass use is invisible to the textual scan. The `Comonad` *class* is independently live via `PFunctor/Cofree.lean`. `Day` has `Comonad` but no `LawfulComonad`; Mathlib also has a distinct categorical Day convolution (`CategoryTheory/Monoidal/DayConvolution.lean`). Before deletion, audit instance synthesis and public API compatibility. Otherwise document it explicitly as a standalone instance library. |
| `Control/Monad/FreeCont.lean` | 229 | Test-only consumer. The previous note was wrong twice: the file has **no `inductive`** at all (it is a `structure FreeContT`, a Church/CPS encoding of the freer transformer over an arbitrary signature), and cslib's `FreeCont r := FreeM (ContF r)` is a free monad over a *continuation signature* — a different object, not the same construction. |
| `Control/Monad/Iter.lean` — `MonadIter` | 152 | Class justified against upstream (core's `repeatM` is a function, not a class, is partial-recursive, and needs `[Nonempty β]`), but it has **no instances in its own file**; the only one in the repo is `ITree F`. Keep. Add another instance only with a chosen iteration semantics and proofs of the separate `LawfulMonadIter` laws; a generic monad need not support iteration. |
| ~~`Control/Monad/Equiv.lean`~~ | — | **File deleted** (#143). No `MonadEquiv`, no `≃ᵐ`. |
| ~~`Control/Monad/Hom.lean` `MonadHomClass`~~ | — | **Declaration removed** (#143). Six stale `scripts/nolints.json` entries referenced it. |
| ~~`Control/Lawful/Basic.lean`~~ | 47 | **Load-bearing, not unused.** Pruned to four lemmas (#147), and `Interaction/TwoParty/Compose.lean` uses all four across ten-plus call sites. The open question is different: the file works around a **Lean 4.29** `do`-elaboration bug and all four lemmas now go through by `simp`, so check whether the bug is fixed and, if so, simplify the call sites rather than delete the file. |

`MAlgOrdered` is no longer speculative — `PFunctor/Free/WP.lean` consumes it in ~15
places. `wpOpt` is exercised only by a test. `wpExc` had **zero** consumers until
`rwpExc` was written against it.

## New candidates found at this re-run

Not in the previous survey at all. Ranked by leverage.

| Upstream | PolyFun counterpart | Verdict |
|---|---|---|
| `Lean.Order.MonadTail` + `repeatM.Internal.eq_of_monadTail` + `Loop.forIn_eq_of_monadTail` + ~40 `monotone_*` lemmas + the `monotonicity` tactic (`Init/Internal/Order/`) | `Control/Monad/Iter.lean`, `ITree/Do.lean` | **Track and instantiate.** PolyFun has *zero* references to `MonadTail`. It is not the same thing as `MonadIter` — order-theoretic rather than Elgot/Conway — so it does not displace it, but it is the class to *also* instantiate if `partial_fixpoint` is ever wanted in these monads, and its lemma library is free. `Internal`, so no stability promise. |
| `Mathlib.Control.ULiftable` (`ULiftable`, `adaptUp`, `adaptDown`, instances for `Id`/`StateT`/`ReaderT`/`ContT`/`WriterT`/`Except`/`Option`) | the universe friction documented in `Control/Monad/Support.lean` and the `ExceptT` single-universe alias | **Investigate as a transport tool.** Zero PolyFun references today. It moves computations between universe instantiations, but it does not repair core's `MonadAttach (ExceptT ε m)` instance signature and ships no `ExceptT` lifting instance. The local single-universe alias therefore remains necessary unless a concrete bridge proves otherwise. |
| `Mathlib.Control.Functor`'s `Liftp` / `Liftr` / `supp` | `MonadAttach.support` | **Cross-reference, do not adopt.** `Functor.supp` is the intersection of all predicates satisfying `Liftp`, not a `CanReturn` construction — a different definition of the same idea, which `Support.lean` should cite. |
| `Mathlib.Control.Basic`'s `CommApplicative` | the interleaving / independence layer | **Cross-reference only.** It commutes applicative effects extensionally; it does not by itself prove independence, fairness, or scheduler invariance for interleaved processes. Reuse it only where the process semantics reduces to that exact applicative law. |
| Core `LawfulMonad.mk'`, and the `bind_pure_comp` simp orientation | any local monadic simp set | **Hazard, not a duplicate.** Core orients `bind_pure_comp` left-to-right *into* `<$>`, so `Functor.map` is the normal form and `map_eq_pure_bind` is deliberately not `@[simp]`. A local simp set adding the reverse direction fights the default one. |

Genuine gaps nobody upstream fills, so hand-rolling is unavoidable if they are needed:
`LawfulAlternative` (absent from core *and* Mathlib), `LawfulMonadFunctor`,
`LawfulMonadControl`, `LawfulMonadFinally`, and coinduction-up-to beyond core's new
`strong_coinduct`.

## Related work

Where PolyFun sits relative to other Lean 4 projects in this space:

- [`sinhp/Poly`](https://github.com/sinhp/Poly) — polynomial functors in a locally
  cartesian closed category, used by HoTTLean. Categorical and actively maintained;
  complementary to PolyFun's concrete `Type`-level development rather than competing
  with it.
- [`alexkeizer/QpfTypes`](https://github.com/alexkeizer/QpfTypes) — `data` / `codata`
  commands over quotients of polynomial functors, from Keizer's MSc thesis. Actively
  maintained, and the only genuine `codata` in the ecosystem. Lean core is not heading
  that way: its `coinductive` command handles coinductive *predicates* only.
- [`boogie-org/lean-itrees`](https://github.com/boogie-org/lean-itrees) — a direct
  interaction-trees port with Dijkstra monads. Dormant. The published-ITrees niche in
  Lean 4 is effectively open.

## Maintenance

Re-run this survey when the toolchain pin moves, and when it does, check in order:
`Init/Control/`, `Std/Do/` and `Std/WP/`, `Cslib/Foundations/`, `Mathlib/Control/`.
Those four are where the abstractions PolyFun cares about keep appearing.

Two process lessons from this re-run, both of which cost more than the findings did:

- **Re-verify every row; do not diff.** Six of 23 rows were wrong, in four different
  directions — upstream gained it since, it was already in core, the adoption had
  already been done, and the unused-surface rows were wrong in *both* directions. A
  diff against the previous survey finds none of these, because the previous survey's
  own text is the thing that is wrong. Reading this file as a to-do list today would
  have produced four duplicate PRs and one unfounded one.
- **The file's own standard is the right one and was not met**: *"A name is a
  hypothesis; the declaration in the pinned tree is the evidence."* Extend it — an
  *absence* claim needs a named search that came back empty, not a recollection. The
  withdrawn Batteries `MonadHom` row is the case in point.

Acted on in this cycle: the two core `List` lemmas adopted, the `Std.Do` quarantine
given a CI check, the stale `whileM` / `GradedMonad` / `ToMathlib` / `rwpExc` references
cleared, `MonadAttach (Except ε)` marked for deletion at v4.35, and the
`MAlgOrdered` × `ExactMonadAttach` coverage gap on `WriterT` closed.
