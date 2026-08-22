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

| Tree | Revision surveyed |
|---|---|
| Lean core | **v4.33.0** (the `lean-toolchain` pin), compared against v4.34.0-rc1 |
| Mathlib | v4.33.0 (pinned), compared against `master` |
| cslib | v4.33.0 (pinned), compared against `main` |
| Batteries | `main` |

Availability is always reported **at the pin**, because that is what PolyFun can
actually use today. Where something exists only upstream of the pin, it is filed under
*Track*, not *Adopt*.

Two traps worth recording for whoever repeats this:

- A toolchain directory named `nightly-<later date>` is not necessarily newer. The
  `nightly-2026-01-22` toolchain reports `4.28.0-nightly` — **older** than the v4.33.0
  pin. Check `bin/lean --version`, not the directory name. The correct local proxy for
  upstream HEAD is the newest `vX.Y.0-rc*` toolchain present.
- Absence is harder to establish than presence, and it is where the first guess is
  most often wrong. For *abstractions*, claims of "nothing upstream has this" below
  come from grepping the full pinned trees for the class/def keyword, not just the
  name PolyFun happens to use. For individual *lemmas*, they come from running
  `exact?` against full Mathlib on the exact statement — a lemma that "looks like it
  must exist" repeatedly turned out not to.

## Ledger

### Adopt — upstream owns it, PolyFun duplicates it

| PolyFun | Upstream | At the pin? |
|---|---|---|
| `Control/Bisimulation.lean`, `Control/LTS/Trace.lean` | `Cslib.LTS` and its `Simulation` / `Bisimulation` / `HasTau` / `TraceEq` theory | yes |
| `Interaction/Concurrent/Fairness.lean`, `Liveness.lean` — the `Always` / `Eventually` / `EventuallyAlways` / `InfinitelyOften` block | `Filter.atTop` | yes |
| `Control/Trace.lean` `mapHom` | `MonoidHom.compLeft`, `Mathlib/Algebra/Group/Pi/Lemmas.lean` | yes |
| `Control/Monad/Hom.lean` | `LawfulMonadLift` / `LawfulMonadLiftT`, `Init/Control/Lawful/MonadLift/` | yes |

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
with this family rather than ignore it. This is the substance of issue #118.

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
- **Batteries**: a bundled `MonadHom`, matching the in-flight draft.
- **Lean core**: `MonadAttach (Except ε)`, which core lacks entirely; and the
  `MonadAttach (ExceptT ε m)` universe bug, which forces a single-universe alias in the
  support layer.
- **Mathlib**: the small helpers below. Each was checked with `exact?` against full
  Mathlib and **none** is subsumed, so they are contributions rather than reuse — the
  opposite of the first guess, which is why the check matters:
  - `Logic/HEq.lean`'s `dependent_apply_heq` and `Prod.mk_heq`. Neighbours exist
    (`congr_arg_heq`, `eqRec_heq_iff`, `Subtype.heq_iff_coe_eq`) but neither lemma
    follows from them by `exact?`. The file's own docstring already says they "belong
    in Mathlib".
  - `List.take_set_self` / `List.drop_set_self` (`PFunctor/Supply.lean`), against the
    Batteries/Mathlib `List.set` API.
  - `heq_forall_iff` and `instIsEmptySigma`, currently parked in `section find_home`
    blocks in `PFunctor/Lens/Basic.lean` and `PFunctor/Equiv/Basic.lean`.

### Track — heading into core, not ready to adopt

#### Core is absorbing Loom's weakest-precondition design

At the v4.33.0 pin, `Std/Internal/Do/` already contains a lattice-generic
weakest-precondition stack:

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
public `Std.WP` namespace and gained `Std.WP.LawfulWPMonadAttach`.

This is structurally PolyFun's `MAlgOrdered` — a monotone predicate transformer into a
complete lattice — and core's frame and conjunctivity layers sit where a relational
extension of it would sit. Its author is the first author of the Loom paper that
`Control/Monad/Algebra.lean` credits. In other words, the lattice-generic program logic
PolyFun adapted from Loom, and that VCVio depends on a pinned Loom fork for, is being
upstreamed into Lean core.

**Verdict: track, do not adopt yet.** Three reasons:

1. It is `Std.Internal` at the pin and public only upstream of it.
2. It is churning: several breaking refactors landed in the week this survey was
   written.
3. It is built on `Lean.Order.CompleteLattice`, while `MAlgOrdered` uses Mathlib's.
   Reconciling those is real work, not a rename.

Revisit after a toolchain bump. Recording the trajectory now is the point — this is
exactly the drift that produced the `MonadSupport` situation.

#### `mvcgen` is deprecated in favour of `vcgen`

Upstream has marked `mvcgen` `@[deprecated]`, directing users to `vcgen`. **`vcgen`
already exists at the v4.33.0 pin** (`Std/Tactic/Do/Syntax.lean`; it was renamed from
the experimental `mvcgen'` in v4.33), so retargeting needs no toolchain bump.

Relatedly, `Batteries.Classes.SatisfiesM` has been deprecated in favour of
`Std.Do.Triple`. The `SatisfiesM` / `MonadSatisfying` line — the other abstraction
PolyFun's support layer resembled — is superseded by core's `MonadAttach` plus
`Std.Do.Triple`.

#### Coinductive predicates in core

`ITree/Bisim/Defs.lean` builds weak bisimulation as an explicit Tarski greatest
fixpoint (`∃ R, R t s ∧ closure`), justified in its docstring by core's *syntactic*
monotonicity checker. Core has since shipped a `coinductive` command for coinductive
predicates, implemented via a reverse-implication order plus `partial_fixpoint`, and
there is upstream work in progress on a strengthened coinduction rule (coinduction
up-to) and on an explicit escape hatch for the monotonicity obligation when automation
fails.

Both address the exact objection the docstring raises. This is worth re-evaluating once
they land; it touches the whole bisimulation development, so it is not a small change.

#### cslib beyond the pin

cslib `main` is ahead of PolyFun's pin and on a newer toolchain. Relevant additions:
`Computability/Languages/SafetyLiveness.lean` (the Alpern–Schneider safety/liveness
decomposition — closed sets are safety, dense sets are liveness), and
`Foundations/Data/OmegaSequence/Topology.lean`. Both overlap
`Interaction/Concurrent/Liveness.lean`.

One known breaking change to plan for: cslib changed `LTS.Execution` from a `Prop` to a
`structure`.

## Unused surface

Not upstream duplicates, so secondary to this survey — but each deserves an explicit
verdict rather than being left to accrete. All are defining-file-only across `PolyFun/`
and `PolyFunTest/`:

| Surface | Note |
|---|---|
| `Control/Monad/Equiv.lean` — `NatEquiv` / `PureEquiv` / `BindEquiv` / `MonadEquiv` | Named by issue #118. |
| `Control/Monad/FreeCont.lean` | Contains a *third* `inductive FreeM`, alongside `Cslib.FreeM` and `PFunctor.FreeM`. cslib's `Foundations/Control/Monad/Free/Effects.lean` already provides `ContF` / `FreeCont` with `callCC` and a `MonadCont` instance. |
| `Control/Comonad/Instances.lean` — `NonEmptyList`, `List.Zipper`, `EnvT`, `StoreT`, `Day` | No upstream equivalents. `Day` convolution is real mathematical content; the list helpers are incidental. |
| `Control/Monad/Hom.lean` `MonadHomClass` | Dead, with its whole namespace body commented out. |
| `Control/Lawful/Basic.lean` | A `do`-elaboration workaround from Lean 4.29; six of its seven lemmas are unused. |

`MAlgOrdered`, `wpExc`, and `wpOpt` also read as unused, but are consumed by the
in-flight program-logic work. They are not dead.

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
