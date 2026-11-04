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

As a polynomial map, a charge is a lens into the constant polynomial `C ω`
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
Charge bounds trade that generality for the laws below, which hold with no side conditions.

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

The laws above hold for any ordered additive monoid. A bound presented as a resource contract
needs more:

- **A canonically ordered cost type.** With negative prices, a program can be padded with refund
  calls to meet any budget. Signed prices belong inside potential and completed-path arguments,
  not in contracts.
- **Finitely many kinds.** With `K → ℕ` and infinite `K`, a pointwise budget does not bound total
  use: one call to each of many kinds meets a budget of `1` per kind. Use `K →₀ ℕ`, or `[Finite K]`.
- **The usual order and addition.** A reversed order, or a max-based addition, makes `≤ B` mean
  something else.
- **Availability and termination stated separately.** A budget says nothing about divergence, or
  about whether a call can be answered. Keep `CallsIn` or an availability predicate as its own
  conjunct.

## Laws

**Sequencing.** `isChargeBound_bind_iff` is exact: the continuation starts from the amount spent
at each leaf. `IsChargeBound.bind` adds budgets, and `IsChargeBound.bind_of_le` lets the
continuation start from any amount within a bound.

**Monotonicity.** `IsChargeBound.mono`, `.mono_charge` and `.mono_spent`.

**Changing the cost type.**

- Bounds push forward along monotone additive maps (`IsChargeBound.map`). A per-kind vector bound
  weighted by a linear form is a weighted bound.
- Bounds transfer both ways along additive order embeddings, such as `ℕ ↪ ℕ∞`
  (`isChargeBound_comp_iff`, `isChargeBound_natCast_iff`).
- Pairs and families split componentwise (`isChargeBound_prod_iff`, `isChargeBound_pi_iff`).

## Lenses and handlers

**Lenses.** A bound with the pulled-back charge bounds the relabelled program
(`IsChargeBound.mapLens`), and the two agree when the lens reaches every answer
(`isChargeBound_mapLens_iff`). Roll bounds transport the same way (`IsRollBound.mapLens`,
`isRollBound_mapLens_iff`).

**Free handlers.** If each implementation `h a` stays within `c a` under the target charge `d`,
simulating a program within budget through `h` stays within the same budget
(`IsChargeBound.liftM`).
