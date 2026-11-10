# Interaction cost

This guide covers how PolyFun accounts for the use of an interface: how many calls a program
makes, of which kinds, and at what price. It is about interaction with an interface, not about
the running time of a machine; [realizability](realizability.md) covers backend-relative time.
Pure Lean code between calls is free, so a cost is a function of the program's interaction tree,
and no statement needs the cost of a Lean function.

## Charges

A **charge** prices the calls of an interface `P` in a cost type `ω`: a call at position `a`
costs `c a`. A charge is a plain function `c : P.A → ω`, paid when the call is made, before the
answer arrives. Cost types are Mathlib's ordered additive monoids, so the same API covers:

- call counts in `ℕ`;
- per-kind counts in `K → ℕ` or `K →₀ ℕ`;
- weights in `ℕ∞`, `ℝ≥0∞` or `ℤ`;
- records of counters such as `ExecutionCost`.

As a polynomial map, a charge is a lens into the constant polynomial `C ω`, namely `Lens.toConst c`
(`PolyFun/PFunctor/Charge.lean`). Pulling a charge back along a lens is lens composition, and the
charge on a sum of interfaces is the copairing `Sum.elim c d`. Intrinsic costs such as ticks need
no new construction: a tick is a call to `PFunctor.linear ω` charged by `id`. A charge read off
events, `e : P.Idx → ω`, prices a call together with its answer, and `TraceList.charge e` extends
it additively to event traces.

## Budgets on free programs

`x.IsChargeBound c B s` (`PolyFun/PFunctor/Free/Cost.lean`) says that, starting with `s` spent,
every call of `x : FreeM P α` keeps the amount spent at most `B`, and so does every leaf. It is
the fold of `OpSpec.budget c B`, whose carrier is a predicate on the amount spent, so a call at
`a` asks `s + c a ≤ B` and continues from `s + c a`. No subtraction or existential is involved,
and natural-number and vector budgets reduce to linear arithmetic. `simp` decides the budget of a
concrete `do` program.

A call whose answer type is empty is still charged. A run that reaches such a call never
completes, but the call is still made.

Indexed programs keep their natural-number `IsChargeBound` on what remains
(`PolyFun/IPFunctor/Free/Bound.lean`), the indexed counterpart of
`isChargeBound_iff_isRollBound_nat` below.

### Relation to roll bounds

`IsRollBound x b canRoll cost` (`PolyFun/PFunctor/Bound.lean`) is the general budget automaton:
an arbitrary state, an admission test and an update, read off each call position. It is also a
fold, of `OpSpec.roll canRoll cost` (`isRollBound_iff_wpFold`).

- A charge bound is the additive instance whose state is the amount spent, plus a check at each
  leaf (`isChargeBound_iff_isRollBound`, in canonically ordered monoids).
- With natural-number charges it is the subtractive budget on what remains, which VCVio's
  `IsQueryBound` family uses (`isChargeBound_iff_isRollBound_nat`).
  `isChargeBound_iff_isRollBound_orderedSub` is the same for vectors and pairs.
- Unit charges give `IsTotalRollBound` (`isChargeBound_one_iff_isTotalRollBound`).

Roll bounds also express protocols that are not additive, such as "never call `b` after `a`".
Charge bounds trade that generality for the additive laws below. Sequencing and the relation to
roll bounds need a canonically ordered cost type, in which `a ≤ a + b`; the other laws need only an
ordered additive monoid.

### Restricted answers

A handler may return only some answers to a call, for example those in the support of a sampled
distribution. The continuations at the other answers never run, so they need no budget. Both
automata take a relation `allows : (a : P.A) → P.B a → Prop` for this, as `demonicUnder` restricts
the demonic reading:

- `IsRollBoundUnder` and `IsChargeBoundUnder` are the folds of `OpSpec.rollUnder` and
  `OpSpec.budgetUnder`, which constrain only the continuations at allowed answers.
- With every answer allowed they are `IsRollBound` and `IsChargeBound` (`isRollBoundUnder_true_iff`,
  `isChargeBoundUnder_true_iff`), and both hold under every restriction (`IsRollBound.under`,
  `IsChargeBound.under`). Allowing fewer answers keeps either bound (`mono_allows`).
- A restricted charge bound is a restricted roll bound whose state is the amount spent
  (`isChargeBoundUnder_iff_isRollBoundUnder`).
- Restriction is also a lens. `P.restrict allows` keeps only the allowed answers, and
  `x.restrict allows` relabels `x` along the inclusion (`PolyFun/PFunctor/Free/Restrict.lean`). A
  restricted bound is the plain bound of the restricted program (`isChargeBoundUnder_iff_restrict`,
  `isRollBoundUnder_iff_restrict`), through `wpFold_mapLens`, which reads any fold over a
  relabelled program as a fold over the original.
- Sequencing takes a demonic postcondition on the results the first program can return along
  allowed answers (`IsChargeBoundUnder.bind_of_le`). A free handler transfers a restricted bound
  when each implementation returns only allowed source answers along the target's allowed answers
  (`IsChargeBoundUnder.liftM`).

## Worst-case cost

`cost c x` (`PolyFun/PFunctor/Free/Cost/Value.lean`) is the worst-case cost of `x`: the fold of
`OpSpec.charge c`, which reads a call at `a` as `c a` followed by its worst continuation, with zero
leaves. It lives in a complete lattice such as `ℕ∞`, `ℝ≥0∞` or `ι → ℕ∞`. `costWith c x k` adds a
leaf cost `k`, which makes sequencing exact.

| Reading | Definition | Cost types |
|---|---|---|
| Budget | `x.IsChargeBound c B s` | any ordered additive monoid |
| Worst-case cost | `cost c x`, `costWith c x k` | complete lattices such as `ℕ∞` |

The two readings agree in canonically ordered monoids:

- `isChargeBound_of_cost_le` holds in general;
- `cost_le_of_isChargeBound` needs addition to distribute over nonempty suprema (`AddSupDistrib`,
  which holds for `ℕ∞` and pointwise, and for `ℝ≥0∞` once `ToCslib.Data.ENNReal.AddSupDistrib` is
  imported);
- `isChargeBound_iff_cost_natCast_le` reads a natural-number budget as a bound in `ℕ∞`.

A natural-number charge `χ` enters through its cast, `cost (fun a => (χ a : ℕ∞)) x`. Programs related
by the relational lift `FreeRel` have the same cost at any charge (`FreeRel.cost_eq`, in
`PolyFun/PFunctor/Free/WP/Cost.lean`).

Over restricted answers, `costUnder c allows x` is the fold of `OpSpec.chargeUnder c allows`,
which takes the worst continuation over the allowed answers only. It is `cost` when every answer
is allowed (`costUnder_true`) and at most `cost` in general (`costUnder_le_cost`). When addition
distributes over suprema, a restricted budget is a bound on `costUnder`
(`isChargeBoundUnder_iff_costUnder_le`). The restricted cost is the cost of the restricted program
(`costUnder_eq_cost_restrict`), and sequencing charges the continuation only at results satisfying
a demonic invariant (`costUnder_bind_le_of_wpFold`; `cost_bind_le_of_wpFold` and
`IsChargeBound.bind_of_wpFold` without restriction). Through a handler whose implementations
return only allowed source answers along the target's allowed answers, each call costs the
restricted worst case of its implementation (`costUnder_liftM_le`).

## Completed paths

`Path.charge c x p` (`PolyFun/PFunctor/Free/Path/Charge.lean`) is the total charge along a
completed path `p` through `x`: the cost of one run, once every answer is fixed. It is the
additive valuation of the path's event trace (`charge_eq_traceList_charge`), and it generalizes
`Path.length` (`length_eq_charge_one`).

- A budget bounds every completed path (`charge_le_of_isChargeBound`), and so does the worst-case
  cost (`charge_le_cost`). When every reachable call has an answer and addition distributes over
  suprema (`AddSupDistrib`), the worst-case cost is the supremum of the path charges
  (`cost_eq_iSup_charge`).
- The converse needs every reachable call to have an answer (`isChargeBound_of_forall_charge_le`,
  under `ProgramProgress`): a call with no answers ends no completed path but is still charged.
- With signed weights the readings differ even then: a prefix may overspend a budget that every
  completed path respects. So the completed-path reading has its own calculus, valid in any
  ordered cost type.

The calculus:

- `Path.splitBind` splits a path through `x >>= f` into a path through `x` and one through the
  continuation at its output, and `Path.joinBind` is its inverse (`splitBind_joinBind`,
  `joinBind_splitBind`). The charge adds (`charge_splitBind`, `charge_joinBind`).
  The path a fixed answer selector picks through `x >>= f` joins the paths it picks through `x`
  and through the continuation at that path's output (`Path.ofHandler_bind`).
- Paths pull back along lenses and leaf maps (`charge_pullMapLens`, `charge_pullMap`); along a
  lens whose charges agree up to an additive map, the charge is that map applied
  (`charge_mapLens_eq_map`).
- A path through a program simulated by a free handler refines to a path through the source with
  the same output, when each implementation stays within its call's charge on every completed
  path (`exists_path_liftM`, `charge_liftM_le_of_forall`), also for bounds on the paths whose
  output satisfies a predicate such as success (`charge_liftM_le_of_forall_output`). Exactly, the
  paths through a simulated program are the source paths together with a path through each call's
  implementation returning the answer taken (`exists_path_liftM_iff`, with `Demand`).
- With subsingleton answers there is exactly one path (`forall_charge_le_iff_ofHandler`).
- A program relabelled into a common interface, followed by relabelled continuations, has every
  path within the sum of the two path budgets (`charge_bind_mapLens_le`), over any presentation of
  the common interface.
- Charges of sums and coordinates distribute (`charge_finsetSum`, `charge_apply`), and
  `withPathCharge c x` runs `x` and returns the charge of the path taken, generalizing
  `withPathLength`.

**Node weights.** A charge that depends on the node rather than the operation is a decoration:
`Path.chargeDec` sums the weights a `Decoration (fun _ => ω)` puts on the nodes along a path. It
generalizes `Path.charge` through `Decoration.ofCharge` (`chargeDec_ofCharge`), and node weights
at most `bound` (`Decoration.AllLE`) bound it by `length • bound` (`chargeDec_le_length_nsmul`).

**Non-additive valuations.** Some costs are not additive under sequencing.
`TraceList.freshCharge w K t` (`PolyFun/PFunctor/Charge.lean`) charges each position of `t`
outside `K` once, however often it is called: the weighted count of distinct new queries. It is
subadditive under concatenation (`freshCharge_mul_le`), at most the additive charge
(`freshCharge_le_charge`), and antitone in the set of known positions (`freshCharge_antitone`).

## Accounting boundary

A charge bound is a bound on interface use, relative to an accounting boundary. It charges the
calls a program makes and nothing else. At this layer the following are free:

- the code between calls, including any view or encoding of the input;
- the answers, and whatever handler, oracle or machine produces them;
- handler state, and the cost of reading or updating it.

Each free component is bounded one layer down: by a certified handler into the next interface,
by a machine that refines the program, or by a quantitative realization, which charges backend
work. A bound is useful only together with a statement of which layer picks up what this one
leaves free.

### Bounds as contracts

A bound presented as a resource contract needs more than the laws of this guide:

- **A canonically ordered cost type.** With negative prices, a program can be padded with refund
  calls to meet any budget. Signed prices belong inside potential and completed-path arguments,
  not in contracts.
- **Finitely many kinds.** With `K → ℕ` and infinite `K`, a pointwise budget does not bound total
  use: one call to each of many kinds meets a budget of `1` per kind. Use `K →₀ ℕ`, or `[Finite K]`.
- **The usual order and addition.** A reversed order, or a max-based addition, makes `≤ B` mean
  something else: under the reversed order every program meets the budget `0`, and with `max` as
  addition a budget bounds only the largest price (both tested in
  `PolyFunTest/PFunctor/Charge/Basic.lean`).
- **Availability stated separately.** A budget says nothing about whether a call can be answered:
  a call whose answer type is empty meets its budget and never returns. Keep `ProgramProgress`
  (`programProgress_of_nonempty`) or an availability predicate as its own conjunct.

## Laws

**Sequencing.** `isChargeBound_bind_iff` and `cost c (x >>= f) = costWith c x fun a => cost c
(f a)` are exact: the continuation starts from the amount spent at each leaf. A call whose answer is
ignored, such as a tick, merges into what follows when it has an answer
(`isChargeBound_liftBind_const_iff`). `IsChargeBound.bind` adds budgets, `cost_bind_le` adds costs,
and `IsChargeBound.bind_of_le` lets the continuation start from any amount within a bound.

**Reachable results** (`PolyFun/PFunctor/Free/Cost/Support.lean`). The continuation's budget is
needed only where `x` can return: `IsChargeBound.bind_supp` and `cost_bind_le_supp` take it on the
support `x.supp`. `x.CallsIn S` says every call of `x` is in `S`; then charges and handlers matter
only on `S` (`IsChargeBound.congr_charge`, `costWith_congr_charge`, `liftM_congr_of_callsIn`).
`x.MayCall a` says a call at `a` occurs in the tree, and the calls that occur form the least such
`S` (`callsIn_iff_forall_mayCall`, `callsIn_setOf_mayCall`).

**Monotonicity.** `IsChargeBound.mono`, `.mono_charge` and `.mono_spent`; `cost_mono` is tagged
`@[gcongr]`.

**Changing the cost type.**

- Bounds push forward along monotone additive maps (`IsChargeBound.map`). A per-kind vector bound
  weighted by a linear form is a weighted bound.
- Bounds transfer both ways along additive order embeddings, such as `ℕ ↪ ℕ∞` or `ℕ ↪ ℝ≥0∞`
  (`isChargeBound_comp_iff`, `isChargeBound_natCast_iff`).
- Pairs and families split componentwise (`isChargeBound_prod_iff`, `isChargeBound_pi_iff`), a
  family sums to a total (`IsChargeBound.sum`), and a bound holds in every coordinate of a constant
  family (`IsChargeBound.const`). Per-index unit budgets are the subtractive per-index roll bound
  (`isChargeBound_single_iff_isRollBound`).

**Loops** (`PolyFun/PFunctor/Free/Cost/Loops.lean`). `forM`, `mapM`, `foldlM` and `forIn` stay
within the sum of their per-iteration budgets, or `xs.length • B` for a uniform budget `B`.
`cost_forM_le` and `cost_forIn_le` are the value forms.

## Lenses and handlers

**Lenses.** A bound with the pulled-back charge bounds the relabelled program
(`IsChargeBound.mapLens`), and the two agree when the lens reaches every answer
(`isChargeBound_mapLens_iff`). In value form, `cost_mapLens_le` bounds the cost of the relabelled
program, with equality when the lens reaches every answer (`cost_mapLens_of_surjective`).
Roll bounds transport the same way (`IsRollBound.mapLens`,
`isRollBound_mapLens_iff`).

**Free handlers.** `Handler.WithinCharge h d c` (`PolyFun/PFunctor/Handler/Charge.lean`) says
that each implementation `h a` stays within `c a` under the target charge `d`. Simulating a
program within budget through such a handler stays within the same budget
(`IsChargeBound.liftM`). With a uniform step bound `k`, a program of `n` calls is simulated within
`n • k` (`IsChargeBound.liftM_nsmul`). Certificates hold for identity, lens and sum handlers, and
they compose (`WithinCharge.comp`). In value form, a simulated program costs at most the original
with each call charged the worst case of its implementation, `handlerCost` (`cost_liftM_le`).

**Stateful handlers.** For handlers into `StateT σ (FreeM Q)`, a step bound that holds from every
state gives the same transfer (`IsChargeBound.run_liftM`). When the step's target charge depends
on the state, a potential pays for it: `Path.exists_run_liftM_amortized` bounds the target charge
of every completed path by the source charge plus the growth of the potential. A cache whose size
is the potential makes at most as many target calls as it grows. A handler that may pause
(`runUntil`, returning the pending call and its continuation) has a budget form
(`IsChargeBound.runUntil`, in a cancellative cost type such as `ℕ`), and every paused
continuation stays within the interrupted program's budget (`IsChargeBound.runUntil_paused`).

The budget form's potential has the opposite sign. It is nonnegative and pays by decreasing, so the
program's budget plus the initial potential is a target budget. A budget must bound every prefix
before the run starts. A nonnegative potential that decreases does this, while a growing potential
bounds the charge only by its final value. In a cost type with negation, such as `ℤ`, negating the
potential turns one step condition into the other.

All three transfers require the step bound from every handler state. A handler that meets it only
on reachable states needs a state type that excludes the unreachable ones.

**Handlers into any monad.**

- `h.withCharge c` keeps the amount spent as `StateT` state, and forgetting it recovers the
  handler (`fst_map_run_liftM_withCharge`). `h.withChargeW c` logs it in a writer instead, as
  writer tracing of the charge (`withChargeW_eq_withTraceBefore`, `fst_map_run_liftM_writerT`,
  `run_liftM_withChargeW_id`, `supp_run_liftM_id_withChargeW`).
- On every possible result of a run of a program within budget `B`, the amount spent is at most
  `B` (`IsChargeBound.le_of_canReturn_run_liftM_withCharge`).
- That is an instance of resource growth (`IsChargeBound.le_of_canReturn_run_liftM`): if each call
  at `a` raises a measure of the handler state by at most `c a`, a program within budget `B`
  raises it by at most `B`. Counters, logs, caches and tables are such measures.
- A run through a deterministic handler returns the output and the charge of the one path that
  handler picks (`run_liftM_withCharge_id`): the instrumentation measures that path, not the
  program's worst case.
- An expected-cost reading needs a probability semantics, which this guide does not cover. It
  transfers through a handler only from a per-call bound that holds for every call argument and
  every handler state. A bound that holds only on average can fail once later calls depend on
  earlier answers.
- `h.withBudget c B` refuses any call that would overspend, and `h.withBudgetOr c B fallback`
  answers it with a fallback. On a program within budget neither intervenes
  (`run_liftM_withBudget_of_isChargeBound`, `run_liftM_withBudgetOr_of_isChargeBound`).

The upper-bound readings share one transfer principle: if each implementation is observed below the
spec of its call, the simulated program is observed below the program (`wpFold_liftM_le`).
`costWith_liftM_le` is an instance. The budget reading is its dual, which is why its transfer
lemmas are proved directly. Readings of one program compare the same way: a spec below a monotone
spec at every call folds below it (`wpFold_le_wpFold_of_le`). A larger charge therefore gives a
larger cost (`costWith_mono_charge`), and the fold of any spec below `OpSpec.charge c` at every
call is at most `costWith c`.

## Layers and certified implementations

A cost argument usually spans layers. A specification is priced by its calls, an algorithm
implements each call by operations, and the operations run as instructions or gates. Each link
between two layers is a **certified implementation** (`PolyFun/PFunctor/Handler/Certified.lean`):

- an implementation of the upper interface `P` by programs over the lower interface `Q`;
- an **exchange** `E : ω →+o ω'` that converts prices, such as "one hash is two compressions";
- a certificate that each call at `a` is implemented within `E (c a)`.

`Handler.Certified P Q c d` packages the three. Bounds transfer along it: a program within `B` is
simulated within `E B` (`Certified.transfer`), and in value form a simulated program costs at most
`E` of the original's cost (`Certified.cost_liftM_le`). Certified implementations compose, and so
do their exchanges (`Certified.comp`), so a chain of layers gives a bound at the bottom by
composition, without unfolding the programs. A reduction runs a setup program, the source program
through a certified handler, and a finishing program, and the handler and the finishing program may
use what the setup returned. Its bound is affine in the source budget,
`setupCost + E B + finishCost` (`CostedReduction.run_isChargeBound`).

Charges with values in `ι → ω` count one resource per index
(`PolyFun/PFunctor/Handler/CertifiedVec.lean`). Worst-case vector costs are computed componentwise
(`cost_pi_apply`, `cost_le_pi_iff`). Pricing at nonnegative prices `p`, `u ↦ ∑ i, p i * u i`
(`priceHom`), turns a vector bound into a scalar one (`IsChargeBound.price`, `cost_price_le`).
Per-resource demands `d : ι → ι' → ω` give the exchange `u ↦ ∑ i, u i • d i` (`demandHom`): a
handler whose call at `a` uses at most `∑ i, c a i • d i` is certified by it
(`Certified.ofDemand`), a program with use vector `u` then runs with use vector `∑ i, u i • d i`
(`Handler.isChargeBound_liftM_demand`), and demands compose
(`demandHom_demandHom`, `Handler.isChargeBound_liftM_demand_comp`).

Stateful packages have certificates in a single cost type
(`PolyFun/PFunctor/Handler/Stateful/Charge.lean`): `Stateful.WithinCharge` bounds each call from
every state. A stateless certificate lifts to it
(`Handler.WithinCharge.lift`), a change of cost type pushes it forward
(`Stateful.WithinCharge.map`), and certificates compose along `Stateful.link`
(`Stateful.WithinCharge.link`).

## Measured and budgeted programs

`MeasuredProgram Input Result ω` (`PolyFun/PFunctor/Free/Cost/Measured.lean`) computes a function
by a free program whose interface depends on an uncharged view of the input, with deterministic
answers and a price per operation.

- `run` answers every call and returns the output of the one path the answers pick
  (`run_eq_output`).
- `Realizes f` says the run computes `f`.
- `CostAtMost B` bounds the charge of every completed path of every view's program, so signed
  prices are allowed.

`comp outer inner` runs `inner`, computes `outer`'s view from the actual intermediate result, and
runs `outer`, on the sum of the two interfaces, each operation tagged with the view it belongs to.
It realizes the composite (`run_comp`, `Realizes.comp`), and budgets add (`CostAtMost.comp`).
`contramap` precomposes an uncharged map, and `ofFun` is the program with no operations. `BudgetedProgram f ω` bundles a measured program realizing `f` with its budget, and
composes the same way.

Only the operations are charged: the view, the answering function and the code between calls are
free, so `ofFun f` realizes any `f` at cost `0`. A cost statement therefore names its measured
program instead of quantifying over one, and the uncharged parts are bounded one layer down. Prices
do not depend on the view; for a family of inputs, fix the size measure and the budget envelope
independently of the program, and prove growth separately.

`Budgeted c B α` is the subtype of free programs within budget `B`. Graded by `Multiplicative ω`,
it is a `GradedMonad`: `gbind` adds budgets.

## Other models

The other models of computation reduce to free programs: resumptions, machines and interaction
trees through their finite truncations, indexed programs through their Σ-erasure, and `TypeTree`
by definition. Resumptions, machines and indexed programs also have a worst-case `cost`, the
supremum of the costs of the truncations or the cost of the erasure
(`Resumption.isChargeBound_iff_cost_le`).

| Model | Bound | Agreement |
|---|---|---|
| `Resumption p β` | `IsChargeBound`: every `truncate k r` within budget (safety reading) | `isChargeBound_toResumption_iff`, `isChargeBound_query_iff` |
| `DynComputation p α β` | every `unroll k state` within budget | `isChargeBound_iff_behavior`, `Implements.isChargeBound_init_iff` (any machine implementing a program has its bound), `isChargeBound_ofFreeM_iff`, `IsChargeBound.wrap`; `ImplementsWithinCharge` is bounded implementation with a charge |
| `ITree F α` | visible calls charged by `c`, silent steps by `tau` (default `0`) | `isChargeBound_step_iff` (free silent steps are invisible), `isChargeBound_step_iff_add`, `isChargeBound_iff_toDynComputation` |
| `IFreeM P X s` | the bound of the Σ-erasure | `isChargeBound_iff_toSigmaFreeM`: the natural-number `IsChargeBound` of indexed programs is the bound of the erasure |
| `TypeTree` | a `FreeM` over move types; a unit charge counts rounds | definitional |

The safety reading allows runs that never return: such a run is within budget when all of its
finite prefixes are.

## Proving bounds

- **Concrete programs.** `cost_bound [defs]` (`PolyFun/PFunctor/Free/Cost/Tactic.lean`) unfolds
  the definitions and runs `simp` with the cost equations and with finite-supremum unfolding
  (`Fin.iSup_succ`, `iSup_of_empty`, `iSup_bool_eq`, `iSup_option`, `iSup_sum`). Then `norm_num`
  and `omega` handle the arithmetic. It proves budgets and evaluates worst-case costs of concrete
  `do` programs over finite answer types, and returns any goal it cannot close in simplified
  form.
- **Loops with a symbolic number of iterations.** Use the loop lemmas.
- **Programs with symbolic structure, through `vcgen`.** Read a budget as a core `WPMonad`
  (`budgetWPMonad`), or keep the amount spent as `StateT` state (`withCharge`), and let `vcgen`
  step through the calls with loop invariants
  ([program logic](program-logic.md#charges-and-budgets)).
- **Universes of the interface.** State helper lemmas over an interface `P : PFunctor.{u, v}` with
  universe variables. A helper stated at `PFunctor.{0, 0}` does not match an interface whose answer
  universe is a variable, such as VCVio's `OracleSpec`, and `rw` then reports only that it found no
  occurrence of the pattern.
