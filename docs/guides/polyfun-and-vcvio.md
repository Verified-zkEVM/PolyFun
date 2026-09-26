# PolyFun and VCVio

PolyFun supplies general constructions for typed interaction. VCVio specializes
those constructions to cryptographic computations and security proofs. Their
connection is a dependency and an API boundary: the generic library can be
used independently in semantics, effect handling, and concurrent systems.

## Who owns what

| Layer | Responsibility |
|---|---|
| Mathlib | `PFunctor`, W-types and M-types, algebra and order theory, and supporting mathematics |
| CSLib | `PFunctor.FreeM`, the functor-generic `Cslib.FreeM`, and reusable computer-science infrastructure |
| PolyFun | Polynomial morphisms and handlers; paths and replay structure; programs, behaviors, machines, and their laws; protocol shapes; open composition; generic support/WP and realizability |
| `ToCslib` | Staged extensions of upstream interfaces: free-monad and loop laws, an order bridge, bitvector and polynomial lemmas |
| `ComplexityBackends` | Optional concrete machine models and the backend-specific certificates connecting them to PolyFun realizability |
| VCVio | Probability and distributions, cryptographic experiments and adversary restrictions, security definitions, reductions, and concrete cryptographic applications |

Generic resource accounting is already part of PolyFun. Concrete complexity
theory lives in `ComplexityBackends`, whose cslib single-tape backend includes a
non-uniform, boundary-pinned P/poly certificate. Such a certificate yields a generic
`PolynomialProgramWitness` at each parameter, with a constant second-order bound
(`Witness.toPolynomialProgramWitness`). These facts do not identify a generic
realization with a cryptographic PPT adversary. Such an interpretation needs
its own encoding, probability, resource, and adequacy obligations.

## Vocabulary at the boundary

| VCVio vocabulary | Generic construction |
|---|---|
| `OracleSpec I` | A response family indexed by requests; `toPFunctor` bundles it as a polynomial interface |
| `OracleComp spec α` | `PFunctor.FreeM spec.toPFunctor α` |
| `QueryImpl spec m` | Definitionally `PFunctor.Handler m spec.toPFunctor` |
| `QueryImpl.add` and the `simulateQ_add_*` routing lemmas | `PFunctor.Handler.sum` with `liftM_sum_lift_inl`, `liftM_sum_mapLens_inl`, and their right-hand and `sumLift` variants |
| ArkLib's `Statement.Lens`, `Witness.Lens`, and context lenses | `PFunctor.Lens.ofMonomial`, `monomialMapFst`, `monomialMapSnd` between monomials |
| Positions of an indexed oracle sum `Σₚ i, spec i` | `PFunctor.sigma.mk`, `sigma.fst`, `sigma.snd`, `sigma.rec`, `sigma.B_mk` |
| `simulateQ` | Interpretation through the free-monad handler extension |
| Oracle strategies and returning implementations | Specializations of polynomial dynamical systems and returning computations |
| Probability of an output or event | A downstream interpretation, not a field of the generic request tree |

The program and handler correspondences can be inspected in VCVio's
[OracleComp](https://github.com/Verified-zkEVM/VCVio/blob/main/VCVio/OracleComp/OracleComp.lean)
and [QueryImpl](https://github.com/Verified-zkEVM/VCVio/blob/main/VCVio/OracleComp/SimSemantics/QueryImpl/Basic.lean).
The selected VCVio revision determines which PolyFun pin and import layout it
supports; matching a current PolyFun API requires an explicit dependency update.

## Reuse of laws

A handler-composition law can be proved for an arbitrary lawful target monad.
VCVio can instantiate it with a stateful probabilistic interpretation to compose
oracle simulations. That structural law alone does not prove that two different
handlers induce equal distributions, preserve a shared random-oracle cache, or
have the same running time. Those are additional statements about the chosen
interpretations.

Likewise, a replay cursor identifies and reconstructs branches of a free
program. A forking probability bound needs probability semantics and the
cryptographic experiment. PolyFun's open-system composition laws need a chosen
observation; a concrete security interpretation must establish that its
observation and allowed contexts satisfy the required laws.

## Choosing a contribution's home

Put reusable polynomial, monadic, machine, and structural interaction laws in
PolyFun. Put reusable upstream extensions in `ToCslib` while they are staged.
Put a concrete machine model in its own subdirectory of `ComplexityBackends`.
Put definitions whose
meaning depends on probability or cryptographic security in VCVio or a more
specialized downstream library.

The [program-logic guide](program-logic.md), [realizability guide](realizability.md),
and [open-systems guide](open-systems.md) make these boundaries precise for their
respective APIs. See [REFERENCES.md](../../REFERENCES.md) for the public literature
behind the constructions.
