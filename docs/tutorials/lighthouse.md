# Five lighthouses and two sightings

Five lighthouses stand on a ring, numbered 0 through 4. The sender sees which lighthouse flashed. The receiver sees a clue naming two neighboring lighthouses, one of which flashed. A message must identify the lighthouse for every legal clue. Neighbors need different messages, so alternating two labels around the ring fails where the ends meet. The labels `0, 1, 0, 1, 2` show that three suffice. The proof identifies these confusable pairs with Mathlib’s five-cycle and uses its chromatic number. [Odd-cycle theorem](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Combinatorics/SimpleGraph/Coloring/Constructions.lean#L122-L124)

The recovery board gives the opening observation when the clue excludes the true lighthouse. On a legal clue it reveals the sighting, which the target must reproduce. Gain validity therefore asks for correct recovery on exactly the legal inputs. Two distinct sightings must have different signals whenever the receiver could get the same clue for both. These pairs form a simple graph. A fixed signal admits a decoder exactly when it is a proper Mathlib coloring of that graph.

Now the sender sees two flashes and the receiver gets a clue for each. Two separate three-label messages have nine possible values. A joint message needs only five. For flashes at `(x, y)`, send `x + 2*y` modulo five. The four pairs allowed by the receiver's clues have different residues. For example, clues `{4, 0}` and `{0, 1}` allow four pairs. Only `(4, 1)` gives residue 1. [Encoder and decoder](../../Examples/Tutorials/Lighthouse.lean)

To see why four messages cannot suffice, arrange the 25 pairs in five rows. Among any two neighboring rows, a message can occur at most twice. Two occurrences in the same or neighboring columns would share both clues, and the five-cycle has room for at most two pairwise non-neighboring columns. Summing over the five neighboring row pairs counts each cell twice. Each message therefore covers at most five of the 25 cells. The counting bound and the five-signal decoder certify the minimum directly. The executable test separately replays all 100 legal sighting and clue combinations. This is a finite example of zero-error coding with side information at the decoder. [Counting proof](../../Examples/Tutorials/LighthouseCounting.lean) · [Decoder tests](../../PolyFunTest/Examples/Lighthouse.lean) · [Coding reference](../../REFERENCES.md#zero-error-coding)

```lean
import Examples.Tutorials.LighthouseCounting
open PolyFunExamples.Bargaining.Replay.Lighthouse
#eval jointDecoder (jointHint (4, 1)) (4, 0)
#check minimum_single
#check minimum_joint
```
