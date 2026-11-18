# Two lighthouse sightings in five signals

Five lighthouses stand on a ring. A lookout sees which one flashes. A navigator gets a clue naming two neighboring lighthouses, one of which flashed. Only the navigator sees the clue. What can the lookout send so the navigator always identifies the flash?

One sighting needs three labels, so sending separate labels for two sightings gives nine possible pairs. If the lookout encodes the two sightings together, **five labels suffice, and five are necessary**.

## Decode a pair

Number the lighthouses 0 through 4. For one flash, neighboring lighthouses must have different labels because they share a possible clue. Alternating two labels fails when the ring closes. The labels `0, 1, 0, 1, 2` work. In Lean, the graph of pairs that can share a clue is Mathlib’s five-cycle. [Odd-cycle theorem](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Combinatorics/SimpleGraph/Coloring/Constructions.lean#L122-L124)

For flashes at `(x, y)`, send `x + 2*y` modulo five. Suppose the navigator’s clues are `{4, 0}` and `{0, 1}`. The four possibilities give four different signals.

| Sightings | (4, 0) | (4, 1) | (0, 0) | (0, 1) |
|---|---:|---:|---:|---:|
| Signal | 4 | 1 | 0 | 2 |

Receiving 1 identifies `(4, 1)`. The same rule works for every clue pair. Starting at the first endpoint of each clue, advancing along the first edge adds one to the signal and advancing along the second adds two. The four offsets are 0, 1, 2, and 3, all distinct modulo five.

```lean
import Examples.Tutorials.Lighthouse.Coding
open PolyFunExamples.Lighthouse

#eval jointDecoder 1 (4, 0)  -- (4, 1)
#check single_optimal
#check joint_optimal
```

## Why four labels fail

Lay out the 25 ordered pairs in five rows. Consider two neighboring rows. Within those rows, two distinct cells with the same label must lie in distinct, non-neighboring columns. Otherwise the navigator could receive the same two clues for both cells. Only two pairwise non-neighboring columns fit on a ring of five. A label therefore appears at most twice in each neighboring row pair. Summing over all five row pairs counts each cell twice, so a label covers at most five cells. Covering all 25 takes at least five labels. [Encoder, decoder, and optimality proofs](../../Examples/Tutorials/Lighthouse/Coding.lean) · [Coding reference](../../REFERENCES.md#zero-error-coding)

The two optimality theorems quantify over encoders and decoders that recover the sighting on every legal clue. The executable regression checks all 100 legal combinations of two clues and two sightings. [Decoder tests](../../PolyFunTest/Examples/LighthouseCoding.lean)

## Certify the ferry solver’s answer

The [ferry solver](ferry-crossing.md) also accepts this puzzle as a recovery board. On a legal clue, preserving the board’s gain means reproducing the sighting. An illegal clue imposes no recovery requirement. The adapter uses the encoders and lower bounds above to certify the solver’s answers of three and five without enumerating partitions of the 25 pairs. [Single-sighting certificate](../../Examples/Tutorials/Lighthouse.lean) · [Joint certificate](../../Examples/Tutorials/LighthouseCounting.lean)
