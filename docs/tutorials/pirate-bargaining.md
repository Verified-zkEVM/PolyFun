# Can a pirate's bluff be erased?

Two pirates split four coins. The captain offers the mate one or two coins. Acceptance pays the proposed split. Rejection gives both pirates zero. The captain offers two and the mate accepts. Could the captain have done better? That depends on what the mate would have done after an offer of one coin.

| Offer | Mate's reply to one | Mate's reply to two | Why neither pirate gains by changing strategy |
|---|---|---|---|
| One | Accept | Reject | The captain keeps three. Switching to two would give the captain zero. |
| One | Accept | Accept | The captain keeps three. Switching to two would give the captain two. |
| Two | Reject | Accept | The captain keeps two. Switching to one would give the captain zero. |

These are all three pure Nash equilibria among the eight profiles. Only the middle row is subgame-perfect. The mate accepts either positive offer there. In each other row the mate would turn down coins after an offer the captain never makes. Take the last row and change only the reply to one coin to acceptance. The same handshake now admits a profitable deviation. The checker returns the captain, an offer of one, and the gain from two coins to three.

## What a payoff table can distinguish

Fix the opening offer and a public observation of the offer and reply. Allow any integer payoff for each player as a function of that observation. Suppose two mate policies give the same visible result at the opening. Then they agree on the Nash verdict for every such payoff table exactly when the captain can reach the same set of visible results by varying the offer.

The mate can try every legal reply to the opening in either game. The captain can try every offer, with the reply determined by the fixed mate policy. This proves sufficiency. For necessity, pick an observation reachable under only one policy. Give the captain one coin for that observation and zero otherwise, and give the mate zero throughout. Changing the offer can now improve the captain's payoff under exactly one policy. The general theorem works for arbitrary offer and reply types. Finiteness enters only when the checker searches explicit lists of legal moves.

When both the offer and its reply are visible, each attainable set is the graph of the mate's policy. Every change to an off-path reply is detectable by some payoff table. For a coarser observation, allow a third offer and reveal only acceptance or rejection to the payoff table. One mate policy rejects only one coin. The other rejects only three. Both accept the opening offer of two, and both allow the captain to obtain either visible result. They agree on equilibrium for every observable payoff. Give the captain one coin for a rejection, and the two witnesses instruct the captain to make different offers. The payoff table in this experiment measures rejection alone. The four-coin split uses a table that can also see the offer.

## What comes from PolyFun

The positions of a polynomial are offers and its directions are the legal replies at each offer. Fixing the mate's policy gives a monomial lens. It sends each offer to its visible result and sends the captain's share of a payoff pair back to the offer. Composing with the terminal payoff lens computes the captain's return at *each* alternative offer. The theorem `nash_iff_wired` identifies the resulting local checks with unilateral deviations in normal form. Player ownership, strict improvement, and the set of visible results enter in the game-theoretic proofs. Those proofs also work with ordinary functions.

Ghani, Hedges, Winschel and Zahn developed the compositional game theory behind this comparison. Related Lean developments provide sequential open-game composition, a game-tree to strategic-form Nash theorem, and a verified finite checker. The example here proves the observation criterion and exercises it with replayable deviations. [Compositional game theory](../../REFERENCES.md#compositional-game-theory) · [Lean open games](https://github.com/mdnestor/GameTheory/blob/2eb58acdf620314b31c12477aaf22c6bbfb7e01e/GameTheory/OpenGame.lean) · [EconCSLib's game-tree theorem](https://github.com/gametheoryinlean/EconCSLib/blob/7cf3a05abbad108bdda61e018444aa58995e47cc/EconCSLib/GameTheory/ExtensiveGame/GameTreeStrategicForm.lean) · [EconCSLib's checker](https://github.com/gametheoryinlean/EconCSLib/blob/7cf3a05abbad108bdda61e018444aa58995e47cc/EconCSLib/GameTheory/StrategicGame/Checker.lean)

For a fixed profile, the finite checker enumerates the offers and just the replies legal at its opening. A returned deviation carries the player's replacement move and the old and new payoffs. The entry-game tutorial checks a market with a single legal reply when the rival stays out and two when it enters. A regression goes further: entering an auction allows any natural-number bid, yet the checker at the passing profile still finds the deviation that raises the payoff from zero to seven. [Auction regression](../../PolyFunTest/Examples/BargainingSearch.lean) · [Finite search and market-entry example](../../Examples/Tutorials/BargainingSearch.lean)

## Run the eight profiles

From the PolyFun repository root, run the following commands.

```sh
lake build Examples.Tutorials.PirateBargaining
lake env lean --stdin <<'LEAN'
import Examples.Tutorials.PirateBargaining
#eval PolyFunExamples.Bargaining.FourCoins.report.forM IO.println
LEAN
```

The module checks the profile lists, compares against an independent enumeration of all replacement policies, and proves the two hidden-offer witnesses. A reported move always replays to the displayed strict gain. A search that finds no such move certifies Nash when both input lists cover all legal moves. [Lean source](../../Examples/Tutorials/PirateBargaining.lean)
