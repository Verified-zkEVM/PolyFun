# Upstream alignment survey

A ledger of PolyFun's general-purpose machinery against what Lean core, Batteries,
Mathlib, and cslib already provide, with a verdict for each entry: **adopt** what
upstream owns, **redesign** an unsuitable abstraction, **keep** a justified local
interface, **upstream** what belongs elsewhere, and **track** forthcoming APIs.

Companion files: `program-logic-landscape.md` (the verification-tooling landscape),
`coalgebra-related-work.md` (coalgebras in other provers), `roadmap.md`.

## Why this file exists

PolyFun's former `MonadSupport` overlapped Lean core's `MonadAttach` return-reachability
interface. Core's lawful predicates need not be exact, so adoption retains optional
exactness laws while using core's carrier and transformer infrastructure. Searching
only for a class with the same name would have missed that design relationship.

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
| Lean core | **v4.34.0** (release 2026-09-14) | `master` / `v4.35.0-rc1`, via the GitHub API |
| Mathlib | v4.34.0 (`5ed2965256`) | `origin/master` |
| cslib | v4.34.0 (`990e65a685`) | `origin/main` |
| Batteries | `f2effa3d80` | `origin/main` + live GitHub search |

Re-run at the v4.34.0 pin (2026-09). The survey itself was done at the v4.34.0-rc2 pin and
re-checked against the final tags. The pin move is *not* content-free: `diff -rq` over the
v4.33.1 and v4.34.0 toolchains' `src/lean` trees touches some two hundred files (the
`Std/Do` and `Std/Tactic/Do` trees among the unchanged ones), Mathlib moves 1031 commits and
cslib 57. The changes that reached PolyFun's build:

- the deprecation of `if_pos` / `if_neg` / `dif_pos` / `dif_neg` in favour of
  `ite_eq_left` / `ite_eq_right` / `dite_eq_left` / `dite_eq_right` (statement-identical
  aliases, `Init/Core.lean`), renamed at every call site, and the rename of
  `repeatM_eq_of_monadTail` to `repeatM.Internal.eq_of_monadTail`;
- Mathlib #43056, which restates the `PFunctor.Obj` API through `Obj.mk` / `Obj.fst` /
  `Obj.snd` (with `Obj.rec` as the `cases` eliminator) and marks `Obj` and `comp`
  `@[implicit_reducible]`. The M-type lemmas (`M.bisim`, `M.dest_mk`, …) now state their
  equations with `Obj.mk`, so PolyFun's anonymous-constructor spellings no longer match them
  syntactically. PolyFun uses `Obj.mk` in the foundational object-producing APIs,
  and `Obj.rec` when constructor simplification is needed. The temporary sigma
  projection/map bridge lemmas and local reducibility overrides are removed.
  Position and direction types that are themselves sigma types retain their
  sigma constructors;
- cslib #856 (`IsMonadHom`), which also gives `FreeM.liftM_map` an explicit interpreter
  argument and makes `Cslib.Foundations.Data.PFunctor.Free` import legacy `Std.Do.WP.Monad`
  transitively (the quarantine below fences *direct* imports and instances), the rename
  `RelatesWithinSteps.of_le` → `RelatesWithinSteps.mono`, and the strictly implicit states of
  `LTS.IsSimulation` / `IsBisimulation`;
- the new `linter.unnecessarySeqFocus` warning on `tac₁ <;> tac₂` with a single goal.

Rows below that changed verdict at this re-run say so explicitly; the rest were re-checked
against the v4.34.0 trees.

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
  several findings below are on `master` but absent from `v4.34.0`, so they ship in
  v4.35 (whose rc1 is out) and the v4.34 bump buys none of them.
- Absence is harder to establish than presence, and it is where the first guess is
  most often wrong. For *abstractions*, claims of "nothing upstream has this" below
  come from grepping the full pinned trees for the class/def keyword, not just the
  name PolyFun happens to use. For individual *lemmas*, they come from running
  `exact?` against full Mathlib on the exact statement — a lemma that "looks like it
  must exist" repeatedly turned out not to.

## Whole-library design review, 2026-09-17

The baseline is PolyFun `efe111a4208adb853b7ce342f5ada634df817dbe` on Lean
v4.34.0. The census covers all **329 production modules**, excluding generated
root umbrellas. It records imports, public declaration shapes, class/instance
surfaces, transparency attributes, and automation hooks. The object API supplement
adds one production module. Tests and CI configuration were reviewed separately.
The implementation also incorporates main's subsequent support extension at
`91e9c02ed23af2259868805f80e6947d5cf38b8e`: continuation congruence uses core's
weak attachment law, and free support uses public object projections and permits
independent result universes.

The census is not a line-by-line proof audit. The deeper pass follows foundational
definitions through representative consumers and checks those choices against
upstream source. Remaining questions are explicit below; a passing build alone
does not settle the design of an interface.

| Area | Baseline modules | Deep-review anchors and representative consumers |
|---|---:|---|
| Polynomial substrate | 126 | `PFunctor/Basic`, free monads and displayed paths, M/cofree, resumption, lenses/charts, polynomial traces; ordinary-import object consumers |
| Indexed polynomials | 12 | `IPFunctor/Basic`, both free monads, indexed laws and `do` elaboration, indexed M observations |
| Control | 28 | Comonad hierarchy and transformers, coalgebras, monad hom/iteration, algebra/support/WP, LTS and traces |
| Interaction trees | 24 | One-step objects, strong/weak/cross-signature relations, handlers and their simp set, finite observations and `do` bridge |
| Interaction framework | 106 | `TypeTree`, decoration, strategy/composition; concurrent fairness/liveness; UC interfaces, wiring laws, sub-theories and activation observations |
| Realizability | 17 | `StepClass`, representation transport, machine closure, quantitative witnesses and trace accounting |
| Logic and complexity | 2 | HEq helpers and second-order polynomial syntax/substitution |
| Upstream staging | 11 | `ToCslib` free-monad/loop transport, order bridge, encoded polynomial time and machine-counting assumptions |
| Optional backend adapters | 3 | `PolyFunCslib` representation/certificate boundary and dependency direction |

### Design evidence and resulting changes

The reference standard is upstream's intended interface, including what its
assumptions and normal forms mean. Relevant primary sources are Mathlib's
[review guide](https://leanprover-community.github.io/contribute/pr-review.html),
[hierarchy design notes](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Algebra/HierarchyDesign.lean),
and [polynomial-object API](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/PFunctor/Univariate/Basic.lean),
plus cslib's [contribution guide](https://github.com/leanprover/cslib/blob/v4.34.0/CONTRIBUTING.md).
These support reviewing abstraction fit, instance coherence, and theorem reuse in
addition to syntax and naming.

| Finding | Verdict and implemented boundary | Evidence / regression |
|---|---|---|
| Object consumers destructured the Sigma implementation despite the native `Obj` interface | **Adopt.** Public `Obj.mk/fst/snd/rec`, with extensionality and constructor injectivity; analogous source-dependent indexed API. M/cofree/resumption and ITree observations use that interface. | Ordinary imports, independent universes, dependent child equality, and VCVio resumption-measure consumer. Actual Sigma-valued positions/directions keep their own constructors. |
| `Comonad` required optional pairing unrelated to the comonad laws | **Redesign.** Separate `Coapplicative`; keep minimal functor/extract/extend data and lawful-functor/comonad laws. Transformers require only operations they use. | Mathlib's categorical comonad definition; a generic comonad must not synthesize pairing; stream/Cofree functor-path coherence and transformer tests. |
| Generic transition proofs were duplicated after introducing the cslib bridge | **Adopt.** Transport composition, following and visible-trace operations through cslib simulation/saturation/MTr. | Empty visible trace versus nontrivial silent closure regression; existing strong, weak, delay and ITree examples. |
| Transparency guidance treated an elaboration failure as a reason to expose bodies | **Redesign policy.** Inspect the intended eliminator/equations first; justify reduction by type computation or instance coherence and test the actual consumer. | Native object migration above; retain documented `TypeTree.done/node` computation and deliberate hierarchy builders. |
| Realizability documentation claimed a wide subcategory of all types and full distributivity | **Narrow the claim.** Objects include chosen representations; current closure assumptions provide binary products/sums/distributivity, not nullary structure. | `StepClass.finite.Str Nat` is uninhabited. A two-point representation class has every `Distributive` mixin and represents `Bool`, but neither `Unit` nor `Empty`. No categorical adapter or stronger assumption is introduced. |
| Coalgebra and UC prose identified local interfaces with stronger categorical structures | **Narrow the claim.** `Coalg` is an F-coalgebra interface; UC classes state boundary-indexed wiring equations. A categorical comparison requires a separate construction and full axioms. | Source fields in `Control/Coalgebra.lean` and `Interaction/UC/OpenTheory.lean`; no claim that wire symmetry proves JSV yanking. |

### Intentional differences retained

- **Qualitative support.** `ExactMonadAttach` extends `LawfulMonadAttach` with
  proof-only introduction rules; the support predicate is core's `CanReturn`.
  Core's general, potentially inexact instances remain usable without exactness.
  `StateT` reachability includes the final state and is evaluated at a chosen
  initial state. This is structural reachability, independent of a downstream
  probability interpretation. The demonic and angelic WP constructions stay
  explicit/scoped so either can coexist with VCVio's quantitative interpretation.
- **Iteration and program logic.** `MonadIter` chooses an iteration semantics and
  separate laws; `repeatM` is not a replacement for that contract. Mathlib ordered
  algebras bridge to core's lattice-generic WP without installing a competing
  global WP interpretation. The `Std.Internal.Do` dependency remains fenced.
- **Indexed `do` and normalization.** Indexed free monads use upstream
  `doElem_elab` extension points with expected-type dispatch and fallthrough to
  ordinary monads. Existing mixed-monad tests exercise both paths. `FreeM` follows
  cslib's `liftBind` to `lift >>= continuation` simp direction; dependent-path
  equations and the scoped handler simp set do not reverse that global direction.
- **Bundled data and universes.** `BundledMonad` packages type-level syntax data;
  `Coalg` allows different source/target universes. Neither is automatically the
  same interface as a lawful categorical endofunctor on one category. Add a
  categorical adapter when a consumer needs one, with its hypotheses explicit.
- **Optional comonad instances.** `Day` retains its raw existential carrier and
  has no `LawfulComonad` instance. Identifying it with categorical Day convolution
  would require the coend quotient. Instance-providing public modules are not
  deleted on the basis of missing textual references.
- **Interaction semantics.** Move-indexed transitions, delay bisimulation,
  coinductive ITree relations, and boundary-indexed UC composition retain their
  semantic distinctions. In particular, activation equivalence does not establish
  sampler realizability or cryptographic security.
- **Representations and costs.** Quantitative step witnesses depend on chosen
  encodings and backend costs. Second-order polynomial syntax allows nested
  oracle-length applications; `MvPolynomial` does not directly express that syntax.
  Its first-order specialization participates in substitution. The cslib staging
  certificate already uses `Polynomial ℕ` where that is the intended object.
- **Small wrappers and module boundaries.** `Control.Trace.mapHom` delegates to
  `MonoidHom.compLeft`; `TraceList` uses upstream `FreeMonoid`. These are useful
  interfaces over upstream theory. `ToCslib` remains below PolyFun, with concrete
  backend adapters in `PolyFunCslib` and probability/security downstream.
- **CI.** The comparison with cslib, Batteries and VCVio supports the existing
  Lake lint/test drivers, lean-action builds, separate checks and `merge_group`
  triggers. VCVio's additional domain/FFI checks serve a different library surface.
  This review needs no new CI workflow or one-time audit script in the repository.

### Bounded follow-up work

| Question | Next concrete check | Acceptance / removal condition |
|---|---|---|
| Residual raw polynomial-object carriers in `PFunctor/Free/Polynomial.lean`, displayed paths and M vertices | Trace `FreeP.encode/decode` and public dependent indices before changing their Sigma presentation. Distinguish intentional position/direction Sigma from object implementation. | A focused migration with ordinary-import and mixed-universe consumers; no local override restoring old object normalization. The foundational migration does not claim every carrier has been converted. |
| Small object and LTS gaps upstream | Propose native `Obj.ext`/injectivity to Mathlib; relocate cslib's `HasTau (Option _)` next to the LTS API; minimize the delay/cross-type symmetry use cases. | Delete local supplements when the supported pin exposes equivalent interfaces without unrelated imports. |
| Remaining dependent `FreeM` elaboration friction | Minimize indexed `bind/lift` reduction and dependent-result simp matching failures against cslib. | Fix the owning API or use a supported eliminator; preserve upstream simp direction and remove each override once its reproducer works. |
| WP and coinductive API changes after v4.34 | At the coordinated toolchain bump, exercise support, StateT, both WP readings, quantitative VCVio consumers and weak-bisimulation examples against `Std.WP`, attachment soundness, `monotonicity_by` and strong coinduction. | Replace superseded local bridges/instances only when the new pin and tests support the same contract; no speculative compatibility hierarchy now. |
| Categorical adapters for represented types and UC wiring | Start from an actual consumer needing category-theory operations; construct objects/morphisms and prove all required laws. | State only the equivalence actually proved. Binary closure and boundary wiring equations alone do not certify the stronger structures. |

The [Lean roadmap for September 2026–February 2027](https://lean-lang.org/fro/roadmap/y4-1/)
prioritizes new `do` notation, verification-condition generation and `SymM`. It is
directional evidence for keeping adapters small, not a release contract. For the
next pin, use actual source changes such as
[`LawfulWPMonadAttach`](https://github.com/leanprover/lean4/pull/14801),
[`monotonicity_by`](https://github.com/leanprover/lean4/pull/14861) and
[strong (co)induction](https://github.com/leanprover/lean4/pull/14855), and test their
semantics rather than assuming a namespace rename completes the migration.

## Definitional-equality follow-up

The baseline is `88f0fa6fc23a8982b154b8a2ea65e9e982e393da`, with the same
Lean/Mathlib/cslib v4.34.0 pins as the design review. A fresh source census
covers **330 production modules** (316 PolyFun, 11 ToCslib, 3 PolyFunCslib),
excluding generated umbrellas. Tests and downstream examples are separate
consumer evidence, not part of that count.

| Source signal | PolyFun occurrences / files | ToCslib | PolyFunCslib |
|---|---:|---:|---:|
| Broad exposed public sections | 193 / 193 | 0 | 0 |
| Local implicit-reducibility attribute commands | 71 / 58 | 0 | 0 |
| Implementation imports (`import all`) | 60 / 38 | 0 | 0 |
| `with_unfolding_all` | 0 | 0 | 0 |

These are textual signals, including comments if a spelling occurs there,
not counts of defects. An attribute command can mention multiple definitions.
The census also locates `rfl`, `change`, `unfold`, and `dsimp`; their use inside
an implementation or to prove its public equations is not itself an API problem.
Reproduce the counts with `rg` over the three production roots and inspect the
matched files; temporary inventories stay outside the repository.

### Polynomial-object carriers

**Adopt the owning object API.** `FreeP.node`, `encode`, and `decode` now use
`(FreeP P).Obj` in their signatures, with `Obj.mk/fst/snd/rec/ext` in their
construction and equality proofs. Public node projections, encoding equations,
and `decode_mk` let consumers reason without expanding the carrier. `relabel`
delegates to `PFunctor.map`, with an explicit bridge to the ordinary map law.
The free-handler equivalence uses these projections; its interpretation proof
names `SubstMonoid.Extension` explicitly, since the object carrier alone does
not choose a monad instance. `M.Vertex` lens observations likewise use native
object equality rather than Sigma equality.

Positions of composite polynomials, dependent path decompositions, and display
fibers that are defined as Sigma types retain those types. `FreeP` itself stays
reducible: its positions and directions intentionally compute to free trees
and their paths. This is not a change to the polynomial's mathematical carrier.

The ordinary-import regressions in
`PolyFunTest/ModuleAPI/FreePolynomial.lean` cover independent universes, labelled
node observations, both encode/decode round trips, free-handler conversion,
M-type child transport, different response fibers, and an operation without
responses. A response-free node is tested extensionally: functions out of
`Empty` need not be definitionally equal merely because they have no arguments.

## Ledger

### Adopt — upstream owns it, PolyFun duplicates it

| PolyFun | Upstream | At the pin? | Status |
|---|---|---|---|
| `Control/Bisimulation.lean`, `Control/LTS/Trace.lean` | `Cslib.LTS` simulation, saturation, and multi-step theory | yes | **adopted through bridges** — strong/weak composition, silent/weak following, trace concatenation, and trace simulation use cslib. The move-indexed presentation, delay relations, and visible-only induction API remain local. |
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

with `SilentSteps` ⇝ `τSTr` and `WeakStep` ⇝ `STr`. `WeakTrace L s xs t`
corresponds to `L.toLts.saturate.MTr s (xs.map some) t`, as proved by
`weakTrace_iff_mTr`. This detail matters: an empty visible trace has equal
endpoints, whereas silent reachability can change state. The local inductive
trace remains useful to ITree consumers; concatenation and simulation transport
now go through the upstream multi-step theory.

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
| `Control/Comonad/Basic.lean` | No `Type`-level class in the surveyed upstream trees; Mathlib has `CategoryTheory.Comonad`. **Redesigned** to require only functor, extraction, and extension, with lawful-functor and comonad laws separately. Optional `Coapplicative` pairing is independent. |
| `Control/Monad/Iter.lean` | Nothing upstream axiomatises Elgot/Conway iteration. The nearest concrete instance is `PFun.fix : (α →. β ⊕ α) → (α →. β)` — the same `β ⊕ α` shape — and core's `Lean.Order.MonadTail` unrolling lemmas, which are `Init/Internal/` with no stability promise. |
| `Control/Monad/Algebra.lean` `MonadAlgebra` | No non-categorical Eilenberg–Moore class upstream. |
| `Control/Coalgebra.lean` `Coalg` | Mathlib's `CategoryTheory.Endofunctor.Coalgebra` is bundled in an arbitrary category; the `Type`-level unbundled form is not upstream. Worth borrowing upstream *names* (`isoMk`, `forget`, `functorOfNatTrans`, and `Terminal.strInv` for Lambek's lemma). |
| The `Poly` categorical layer — lenses, charts, comonoids, `SubstMonoid`, `Display`, `Cofree`, `InternalHom`, wiring | Mathlib's `PFunctor` is a bare `⟨A, B⟩` used only as scaffolding for W-types, M-types, and QPF. It has no lenses, charts, category instance, or monoidal structure. This is PolyFun's actual contribution. |
| Delay bisimulation | See above. |
| `Control/Monad/WriterT/WP.lean` `WriterT.wpMonadOf` | The pinned core and Mathlib provide no writer lift for the lattice-generic WP stack. PolyFun supplies an explicit construction compatible with Mathlib's `WriterT.monad empty append`, with a scoped monoid specialization. A future upstream lift with the same operations and instance coherence would supersede it. |
| `Control/Monad/Algebra/Restrict.lean` `MAlgOrdered.restrictIic` | A construction on PolyFun's own `MAlgOrdered`; the lattice on `Set.Iic c` it uses is Mathlib's. |

### Upstream — belongs elsewhere, PolyFun is the wrong home

cslib is already PolyFun's upstreaming channel: the `PFunctor` basic API is being moved
there, and cslib's `PFunctor.FreeM` is the free monad PolyFun builds on. Material bound for
cslib is staged in the `ToCslib/` library (see `docs/wiki/module-api.md`), which PolyFun imports
as its lowest layer:

| `ToCslib` module | Contents | Upstream target |
|---|---|---|
| `Data/PFunctor/Free/Basic.lean` | `map_pure`, `map_bind`, `liftM_lift_eq_self` | upstream candidate (proposed in cslib#716, closed unmerged) |
| `Data/PFunctor/Free/Basic.lean` | `foldFreeM` with substitution and uniqueness laws, `liftM_comp` | new cslib PR |
| `Data/PFunctor/Free/Loops.lean` | `liftM_forIn'`, `liftM_forIn`, `liftM_forIn_of_pureForIn` (and `liftM_forM` / `liftM_foldlM` / `liftM_mapM` as restatements of cslib#856's `IsMonadHom.map_list*`) | new cslib PR |
| `Control/Monad/HomTransport.lean` | `IsMonadHom.map_listForIn'`, `map_listForIn`, `map_forIn_of_pureForIn`, `map_forIn'_of_pureForIn'` | new cslib PR, next to `IsMonadHom/List.lean` |
| `Control/ForIn.lean` | `PureForIn` / `PureForIn'` / `LawfulMemForInId` for `Option`, `Vector` | Lean core (`Std.Internal.ForIn`) |
| `Order/LeanOrder.lean` | Mathlib `CompleteLattice` → `Lean.Order.CompleteLattice` | Mathlib or cslib |

Landed at cslib `v4.34.0` and therefore deleted from the staging library: cslib#856
(`IsMonadHom`, `IsMonadHom.map_listMapM` / `map_listForM` / `map_listFoldlM`,
`isMonadHom_liftM`, and the naturality of `liftM` along a monad morphism,
`IsMonadHom.map_pfunctorFreeMLiftM`). PolyFun's bundled `m →ᵐ n` reaches these through
`MonadHom.isMonadHom` (`PolyFun/Control/Monad/Hom/IsMonadHom.lean`).

Not stageable downstream: the node normal form inside type indices needs
`@[implicit_reducible]` at the definitions of `FreeM.bind` / `FreeM.lift` in cslib, because Lean
rejects global and `scoped` reducibility attributes on imported declarations
(`Lean/ReducibilityAttrs.lean`); see the node normal form below. Until then the files that
unify node indices carry `attribute [local implicit_reducible] PFunctor.FreeM.bind
PFunctor.FreeM.lift`.

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
  `v4.34.0`, so shipping in **v4.35**). PolyFun's local instance is marked for
  deletion at that bump; the `ExactMonadAttach (Except ε)` half stays, since core does
  not ship the introduction rules.
- **Mathlib**: the HEq helpers below. Each was checked with `exact?` against full
  Mathlib and **none** is subsumed, so they are contributions rather than reuse — the
  opposite of the first guess, which is why the check matters:
  - `Logic/HEq.lean`'s `dependent_apply_heq` and `Prod.mk_heq`. Neighbours exist
    (`congr_arg_heq`, `eqRec_heq_iff`, `Subtype.heq_iff_coe_eq`) but neither lemma
    follows from them by `exact?`. The file's own docstring already says they "belong
    in Mathlib".
  - `heq_forall_iff` and `instIsEmptySigma`, currently parked in `section find_home`
    blocks in `PFunctor/Lens/Basic.lean` and `PFunctor/Equiv/Basic.lean`.
- **Mathlib's native object API**: `PFunctor.Obj.ext` and constructor injectivity
  in `PolyFun/PFunctor/Obj.lean`. The pinned object module does not provide them.
  These use `Obj.rec`; upstreaming them would let PolyFun delete the local
  supplement without exposing the Sigma carrier.

### Track — heading into core

#### Core is absorbing Loom's weakest-precondition design — adopted, behind the quarantine

**There are two complete WP stacks at the pin, and PolyFun targets this one.** The tree
described here is `Std/Internal/Do/`, the lattice-generic stack that `vcgen` drives and that
becomes the public `Std.WP` in v4.35; the older public `Std/Do/` is `SPred`/`PostShape`-indexed
and is what `mvcgen` consumes. PolyFun's kernel instances (`Control/Monad/{Algebra,Support,Hom}/WP.lean`,
`PFunctor/Free/WP/Upstream.lean`, `PFunctor/Free/Do.lean`) all live on `Std/Internal/Do/`;
nothing in PolyFun imports `Std.Do` for its own sake (cslib's `IsMonadHom` module brings its
`WP` classes in transitively). Confusing the two is easy and consequential — they differ on
conjunctivity, which decides what PolyFun can express. The comparison table and that
consequence are in
[`docs/wiki/program-logic.md`](../wiki/program-logic.md#the-two-upstream-wp-stacks); the
short version is that `Std.Do.PredTrans` makes conjunctivity a *structure field* stated as a
bi-entailment, so the angelic support reading could never be a `Std.Do` instance, whereas the
inequational `Std.Internal.Do.WPMonad` admits both readings (`MonadAttach.toWPMonadDemonic` /
`toWPMonadAngelic`) and records conjunctivity per program.

At the pin, `Std/Internal/Do/` contains:

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
subtree. Upstream of the pin this whole tree is renamed out of `Internal` into a public
`Std.WP` namespace (#14783) and gains `Std.WP.LawfulWPMonadAttach` (#14801), whose single
field concludes from a `MonadAttach.CanReturn` witness directly. Both land in **v4.35**.

This is structurally PolyFun's `MAlgOrdered` — a monotone predicate transformer into a
complete lattice — and core's frame and conjunctivity layers sit where a relational
extension of it would sit. Its author is the first author of the Loom paper that
`Control/Monad/Algebra.lean` credits. In other words, the lattice-generic program logic
PolyFun adapted from Loom, and that VCVio depends on a pinned Loom fork for, is being
upstreamed into Lean core.

**Verdict: adopted at v4.34.0, with the three original reservations answered in place:**

1. It is `Std.Internal` at the pin and public only from v4.35 → the kernel's bridges are
   behind the two-tier `Std.Do` quarantine (`scripts/check-modules.sh`), every construction
   is `local`/`scoped` rather than a global instance, and each declaration that the v4.35
   rename touches carries an `-- upstream:` comment (`Std.Internal.Do` → `Std.WP`,
   `EPost.Nil` → `EStack⟨⟩`, `MonadAttach.LawfulWPMonadAttach` → `Std.WP.LawfulWPMonadAttach`).
2. It is churning → the churn is confined to those comments and to
   `PolyFunTest/Do/`, whose `#guard_msgs` texts pin the experimental-tactic diagnostic.
3. It is built on `Lean.Order.CompleteLattice`, while `MAlgOrdered` uses Mathlib's, and the
   pinned Mathlib has no bridge → `ToCslib/Order/LeanOrder.lean` supplies it (Mathlib's
   `CompleteLattice` as core's, low priority, definitionally Mathlib's `≤`), so `MAlgOrdered`
   is **not** ported off Mathlib's hierarchy; `MAlgOrdered.toWPMonad` is a bridge whose `wp`
   is `MAlgOrdered.wp` by `rfl`, and `MAlgOrdered.top_eq_top` / `meet_eq_inf` / `join_eq_sup`
   move between the two spellings of the lattice operations (core's `scoped notation` for
   `⊓`/`⊔`/`⊤` collides with Mathlib's, so transfer lemmas stay out of the `Lean.Order`
   namespace).

#### `mvcgen` is deprecated in favour of `vcgen`

Upstream marks `mvcgen` deprecated via `deprecated_syntax`, directing users to `vcgen`
(#14874, `since := "2026-08-21"`). That deprecation is on `master` only — not at the
`v4.34.0` pin — so it is a **v4.35** item. `vcgen` itself already exists at the pin
(`Std/Tactic/Do/Syntax.lean:464`) and consumes `Std.Internal.Do.WPMonad` /
`Std.Internal.Do.Triple` (`Lean/Elab/Tactic/Do/Internal/VCGen/Frontend.lean`), not the
`Std.Do.WP` structures. PolyFun's kernel instantiates that stack directly
(`Control/Monad/{Algebra,Support,Hom}/WP.lean`, `PFunctor/Free/WP/Upstream.lean`,
`PFunctor/Free/Do.lean`) and every `PolyFunTest/Do/` file runs `vcgen`, so the deprecation
has nothing left to migrate here. `vcgen` warns on every call (`mvcgen.warning`; behind
`experimental.vcgen` from v4.35), so production proofs do not call it and the test canaries
assert the warning with `#guard_msgs` under `--wfail`.

Two gaps in the `@[spec]` database at the pin, both still present on `master`, are closed in
`PolyFun/Control/Do/Spec.lean` and are upstream asks for `SpecLemmas.lean`: `try … catch`
elaborates to `MonadExcept.tryCatch`, whose lifting rule `Spec.tryCatch_MonadExcept` core states
but does not tag (its twin `Spec.throw_MonadExcept` is tagged), so every `try … catch` on a
transformer stack stopped with "no spec found"; and `forM` over a list has no rule at all
(`Spec.forM_list`, an `Invariant α PUnit Pred` rule in the shape of `Spec.forIn_list`). A third
ask concerns the matcher rather than the database: `vcgen` compares a spec's program and value
type structurally (`Lean.Meta.Sym`), so a rule at a dependent value type such as `P.B a` misses
an operation in tail position once that type has been normalized (gotcha 12f); matching those
slots up to reducible defeq would make dependently typed operations first-class.

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
absent from `v4.34.0`, so again **v4.35**. Calibrate the payoff: `strong_coinduct` is
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

Of the **three** breaking changes previously recorded, all three landed by the v4.34.0
tag:

1. *(landed at the pin, unused by PolyFun)* `LTS.Execution` is a `structure` (fields
   `length` / `start` / `last` / `trans`) instead of a `Prop`, with attribute
   `@[scoped grind]` instead of `@[scoped grind =]`. PolyFun does not destructure it.
2. *(landed at the pin, unused by PolyFun)* `LTS.Deterministic` is refactored: the single
   field is `∀ s, lts.DeterministicState s`, layered over `DeterministicStateLabel` /
   `DeterministicState`, with `not_tr_of_ne`, `image_singleton_iff_tr`, `image_char`, and
   `DeterministicStateLabel.finite_image`; the `Finite (lts.image s μ)` instance remains.
3. *(landed at the pin, unused by PolyFun)* `MapLabel.lean` is deleted in favour of
   `MapHom.lean`. The `mapLabel` definition and its main lemmas survive in the new module,
   reimplemented through the more general `Hom.lift` API.

Still absent on `main`, so still genuine upstreaming targets: delay bisimulation, a
well-placed `HasTau (Option α)`, and a cross-type `Bisimilarity.symm`.

#### The `FreeM` node normal form

PolyFun consumes the pinned cslib normalization convention unchanged. Use
upstream monadic interpretation, `IsMonadHom` transport, and general bind laws;
use named structural equations when reasoning about dependent paths.

Two narrow upstream concerns remain: dependent indices sometimes require
`FreeM.bind` and `FreeM.lift` to be implicit-reducible, and simp's indexing of
dependent result types can miss equations on concrete signatures. These need
isolated reproductions and targeted fixes, not a local normalization API.
For example, on the signature `⟨Nat, Fin⟩`, interpreting `lift n >>= k` works
with `rw [FreeM.liftM_bind, FreeM.liftM_lift]` even when bare `simp` leaves the
single-operation interpretation unreduced.

cslib#893 discusses the tradeoff between universe-polymorphic `.bind` and the
standard `>>=` laws used by `LawfulMonad` and WP automation. PolyFun does not
assume that proposal will land or change those attributes locally.

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
| `Control/Comonad/Instances.lean` — `NonEmptyList`, `List.Zipper`, `EnvT`, `StoreT`, `Day` | 892 | **Retain the standalone instance library.** It is publicly imported by `PolyFun.lean`; instance synthesis is invisible to a textual reference scan. The hierarchy tests exercise minimal transformer assumptions and stream pairing. The `Comonad` class is independently live via `PFunctor/Cofree.lean`. `Day` has `Comonad` but no `LawfulComonad`; its raw existential carrier is not Mathlib's categorical Day convolution (`CategoryTheory/Monoidal/DayConvolution.lean`). |
| `Control/Monad/FreeCont.lean` | 229 | Test-only consumer. The previous note was wrong twice: the file has **no `inductive`** at all (it is a `structure FreeContT`, a Church/CPS encoding of the freer transformer over an arbitrary signature), and cslib's `FreeCont r := FreeM (ContF r)` is a free monad over a *continuation signature* — a different object, not the same construction. |
| `Control/Monad/Iter.lean` — `MonadIter` | 152 | Class justified against upstream (core's `repeatM` is a function, not a class, is partial-recursive, and needs `[Nonempty β]`), but it has **no instances in its own file**; the only one in the repo is `ITree F`. Keep. Add another instance only with a chosen iteration semantics and proofs of the separate `LawfulMonadIter` laws; a generic monad need not support iteration. |
| ~~`Control/Monad/Equiv.lean`~~ | — | **File deleted** (#143). No `MonadEquiv`, no `≃ᵐ`. |
| ~~`Control/Monad/Hom.lean` `MonadHomClass`~~ | — | **Declaration removed** (#143). Six stale `scripts/nolints.json` entries referenced it. |
| ~~`Control/Lawful/Basic.lean`~~ | 47 | **Deleted.** Core's `bind_assoc`, `bind_pure_comp`, and `bind_map_left` directly prove the corresponding `do`-form goals under the same `LawfulMonad` assumptions. `Interaction/TwoParty/Compose.lean` uses these laws and transports the dependent-pair equality with `congrArg` and `pure_bind`. `PolyFunTest/Control/LawfulDo.lean` checks the laws through an ordinary import of that public module. |

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
