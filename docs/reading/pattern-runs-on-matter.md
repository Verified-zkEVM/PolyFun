# Libkind--Spivak: pattern runs on matter

This note records the source correspondence and scope of the formalization of
Sophie Libkind and David I. Spivak, *Pattern Runs on Matter: The Free Monad
Monad as a Module over the Cofree Comonad Comonad*, EPTCS 429 (2025),
[doi:10.4204/EPTCS.429.1](https://doi.org/10.4204/EPTCS.429.1),
[arXiv:2404.16321](https://arxiv.org/abs/2404.16321).

## Central construction

Equation (1) and Section 3.2 construct

```text
Xi(P,Q) : Free(P) ⊗ Cofree(Q) → Free(P ⊗ Q).
```

Operationally, a finite `P`-tree is the pattern and a possibly infinite
`Q`-tree is the matter. A pattern leaf stops without advancing matter. At a
pattern node, the current operation symbols are paired; a product direction
selects both the next pattern branch and matter subtree. Thus an output leaf
determines a complete pattern path and a finite matter vertex.

`FreeP.runObj` is this executable traversal, including its dependent backward
map, and `FreeP.runOn` packages it as a lens. `FreeP.xi` follows the paper's
categorical construction: curry the synchronized generator, extend from the
free substitution monoid into the internal-hom convolution monoid, and
uncurry. `FreeP.runOn_eq_xi` proves the two constructions equal as full lenses,
not merely on forward shapes.

## Source ledger

| Source | Lean statement |
|---|---|
| Equation (1), Section 3.2 | `FreeP.runOn`, `FreeP.xi`, `FreeP.runOn_eq_xi` |
| Proposition 3.3 | `FreeP.runOn_natural` |
| Theorem 3.4 | `FreeP.runOn_unit`, `FreeP.runOn_assoc` |
| Appendix C.1 | `CofreeP.laxUnit`, `CofreeP.laxTensor`, and coherence laws |
| Substitution compatibility implicit in the universal construction | `FreeP.runOn_preserves_substitution`, `FreeP.runTree_append` |
| Section 4 generic schema `m p ⊗ c q → m r` | `FreeP.runThrough` |
| Section 4 internal-hom evaluation | `FreeP.evaluation`, `FreeP.runAgainst` |
| Equation (6), substitution-monoid target | `FreeP.runAgainstMonoid` |
| Dynamical-system presentation of matter | `FreeP.runOnSystem`, `DynSystem.runPattern` |
| Existing game wiring, for every finite horizon | `DynSystem.runPattern_game` |
| Behavior/simulation invariance | `runBehaviorThrough_eq_of_obsEq`, `runBehaviorThrough_eq_of_isSimulation`, `runBehaviorThrough_eq_of_isStrongSimulation` |
| Moore-machine Equation (2) | executable depth-three example in `PolyFunTest/PFunctor/PatternRunsOnMatterApplications.lean` |

`FreeP.runTree` decodes the synchronized object to an ordinary `FreeM` tree.
Its constructor and grafting equations expose executable computation without
discarding the dependent path and vertex. `FreeP.runWithHandler` interprets
that finite tree through any lawful monadic handler for paired operations.
`DynSystem.runPattern` is defined through the object map of `runOn`; its
recursive equations and `runPattern_game` prove that this boundary agrees with
the repository's established finite dynamical-game semantics.

## Orientation and universes

The paper calls the result a left module, while its principal displayed map is
written `Free(P) ⊗ Cofree(Q)`. Appendix D also uses symmetry-equivalent
diagrams in the opposite order. PolyFun follows Equation (1), so the concrete
API is a right action and no symmetry is hidden in theorem statements.

The executable `runOn` keeps all four generator universes independent. The
universal `xi` requires only `P : PFunctor.{pA, max qA qB}` for
`Q : PFunctor.{qA,qB}` because the current homogeneous `SubstMonoid.Hom` API
fixes the carrier universe pair. Module coherence laws and the existing
`DynSystem.game` combinator remain square-universe statements. These
restrictions are explicit; no `ULift` transport is concealed.

## Exact scope and deferrals

The formalized results are structural and deterministic. They establish no
cryptographic security, probability, advantage, indistinguishability, or
complexity claim.

The paper's voting/operadic/gerrymandering development needs operad and
aggregation theory not currently in PolyFun. Stochastic players and
probabilistic security belong downstream in VCVio. The paper's transfinite
construction is represented by the equivalent inductive `FreeM` W-type, not
reconstructed stage by stage. `IOMachine.runWith` selects one effectful path
and may halt early, whereas `runOn` constructs the complete finite branching
tree; `runWithHandler` is the honest interpreter bridge, not an equality with
arbitrary `IOMachine.runWith` executions.
