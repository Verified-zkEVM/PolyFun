# How much does the captain need to know?

At one harbor the captain asks a ferryman to cross. At another the captain must name a channel. East works at low tide and west at high tide. Each harbor can get the captain across at either tide. Yet a single instruction to the second harbor fails: east fails at high tide, and west fails at low tide. A signal with two values suffices. Lean computes the signal and the instructions together and proves that every valid signal uses at least two values.

## Run the crossing

```sh
lake build Examples.Tutorials.FerryCrossing
lake env lean --stdin <<'LEAN'
import Examples.Tutorials.FerryCrossing
open PolyFunExamples.Bargaining.Ferry
#eval directions.forM IO.println
#eval withoutHint.forM IO.println
LEAN
```

The first report tells the captain to take east on signal 0 and west on signal 1. The second report explains the failure of a constant hint. Waiting fails at low tide, east fails at high tide, and west fails at low tide. The counterexample belongs to the candidate move: neither tide alone rules out both channels. [Runnable boards and reports](../../Examples/Tutorials/FerryCrossing.lean)

## Which moves need to be replayed?

The signal may depend on the tide. The decoder sees only the signal and the requested source move. Both harbors use the same opening observation at each tide. In gain mode the decoder must preserve a strict improvement for **every** integer payoff function on observations. Whenever the source move changes the opening observation, the target must reproduce the resulting observation. To see why, reward that result with one coin and every other result with zero. When the source move reproduces the opening, it cannot have improved the payoff.

Exact replay requires the target to reproduce all source observations. Suppose the source captain can wait, always cross, or cross **only** at low tide. The target captain can wait or always cross. A translator may always cross on the conditional request in gain mode. That works at low tide and the source earns no improvement at high tide. Exact replay must distinguish the tides to decide whether to wait. A decoder is the backward map of a monomial lens on signals; two valid decoders can be composed when they share the signal and opening. [Payoff characterizations and composition](../../Examples/Tutorials/MoveTranslation.lean)

| Board | Minimum for strict gains | Minimum for exact replay |
|---|---:|---:|
| East or west open | 2 | 2 |
| Three channels, each closed at one tide | 2 | 2 |
| Three channels, each open at one tide | 3 | 3 |
| Optional crossing only at low tide | 1 | 2 |
| Crossing requested, all channels closed | Impossible | Impossible |

In the second row, any pair of tides shares an open channel, yet the three tides together do not. Pairwise checks alone miss this obstruction. In the third row, every pair of distinct tides requires different channels.

## Use the certified search

A `Board` supplies the common opening observation, source and target outcome functions, and an available target move so the decoder can be total. To check a given signal, call `MinimumHint.searchHints mode board hint`. The result contains either a decoder and its validity proof, or a source move, a representative tide, and a refuting tide for every candidate target move. The explicit-list `search` also accepts a caller-chosen order for reproducible witnesses. Its validity claim concerns hints that can actually occur.

To choose the signal itself, call `minimumHint mode board`. An `.optimal k h d valid minimal` result contains a proof of the lower bound against every competing signal and decoder. An `.impossible t b reject` result identifies a tide and source move at which every target move fails, even with full information. Use `.size?` for just the size. Empty state spaces use zero signal values.

The implementation uses `FinEnum` for the hidden states and each move type, and decidable equality for observations. It first checks a signal that reveals the state. A failed check returns the state and source move that defeat every target. A successful check supplies a decoder while the solver searches smaller numbers of occupied signal values. For each count, it builds state partitions by joining a block or opening a new one. Each partition occurs once; changing label names gives the same partition. A block can support a source move exactly when some target move works throughout the block. The cost can grow with the number of partitions of the state set. These examples use small finite games. [Minimum search and proof](../../Examples/Tutorials/MinimumHint.lean)

The solver and the Mathlib-facing enumeration use the same partition codes. `Finpartition.allWithCard n k` returns standard finpartitions of `Fin n` with exactly `k` occupied parts, each once. Its length is the Stirling number of the second kind. For five possible states the counts for one through five signal values are 1, 15, 25, 10 and 1. [Enumeration and proof](../../ToCslib/Order/Finpartition.lean)
