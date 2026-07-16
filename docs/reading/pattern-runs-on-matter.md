# Libkind--Spivak: pattern runs on matter

This note records the source correspondence for the formalization of
Libkind and Spivak, *Pattern Runs on Matter: The Free Monad Monad as a Module
over the Cofree Comonad Comonad* (arXiv:2404.16321v3).

## Formalized map

The paper's Equation (1) and Section 3.2 construct

```text
Xi(P,Q) : Free(P) ⊗ Cofree(Q) → Free(P ⊗ Q).
```

Operationally, a finite `P`-tree is the pattern and a possibly infinite
`Q`-tree is the matter. A pattern leaf stops without advancing the matter. At
a pattern node, the two current operation symbols are paired. A direction in
the product selects both the next pattern branch and the next matter subtree.
An output leaf therefore determines a complete path through the pattern and a
finite vertex of the matter.

`FreeP.runObj` is this executable traversal, including its dependent backward
map, and `FreeP.runOn` packages it as a polynomial lens. `FreeP.xi` follows the
paper's categorical construction: curry the synchronized generator, extend it
from the free substitution monoid into the convolution monoid, and uncurry.
`FreeP.runOn_eq_xi` proves that the executable map is the source construction,
not merely an implementation with similar forward behavior.

## Source ledger

| Source | Lean statement |
|---|---|
| Equation (1), Section 3.2 | `FreeP.runOn`, `FreeP.xi`, `FreeP.runOn_eq_xi` |
| Proposition 3.3 | covariance in both generators, `FreeP.runOn_natural` |
| Theorem 3.4 | the right action's unit and associativity equations |
| Appendix C.1 | `CofreeP.laxUnit`, `CofreeP.laxTensor`, and their coherence laws |
| Appendix D | proof guidance for naturality and the module equations |

The paper calls the result a left module, while its principal displayed map is
written `Free(P) ⊗ Cofree(Q)`. Appendix D draws symmetry-equivalent diagrams
in the opposite tensor order. PolyFun follows Equation (1): its concrete API is
a right action. No symmetry is hidden in the theorem statements.

## Universe boundary

The executable `runOn` keeps the position and direction universes of `P` and
`Q` independent. The universal `xi` also keeps both position universes and
both universes of `Q` independent; it requires only
`P : PFunctor.{pA, max qA qB}` for `Q : PFunctor.{qA,qB}`. This direction
ceiling is forced by the current homogeneous `SubstMonoid.Hom` API:
`CofreeP Q` raises both carrier universes to `max qA qB`, while `FreeP.extend`
requires its target substitution monoid to have exactly the free monoid's
universe pair. The module coherence laws remain in `PFunctor.{u,u}` because
they compare this interaction with fixed-category monoidal structure maps.
The formalization does not conceal either boundary with `ULift` transport.

## Scope

These results are structural and deterministic. They establish no
cryptographic security claim. Protocol, game, voting, and generalized-duality
applications from Section 4 belong to the downstream examples layer.
