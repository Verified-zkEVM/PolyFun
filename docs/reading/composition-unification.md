# Composition unification: two axes, one eventual double category

This memo records what can and cannot be unified among PolyFun's composition
operations. It replaces the version that was accidentally merged only into an
obsolete PR branch. The earlier draft also predated the removal of `CompTriple`;
the account below describes the current lens-valued API.

Companions: `roadmap.md` for the formalization tickets and
`vcv-connection.md` for downstream payoffs. The main reference is Niu–Spivak,
*Polynomial Functors: A Mathematical Theory of Interaction* (Cambridge
University Press, 2025; arXiv:2312.00990).

## The important distinction

There are two orthogonal meanings of “compose”.

1. **Interface composition.** A lens `p ⇆ q` followed by a lens `q ⇆ r` is
   ordinary categorical composition. Substitution `p ◃ q`, tensor `p ⊗ q`, and
   the duoidal maps organize interfaces. A lens into a substitution composite
   is inspected directly through `l.compOuter`, `l.compInner`, and
   `l.compPullback`; no parallel `CompTriple` representation is needed.
2. **Program composition over a fixed interface.** `FreeM.append` grafts one
   interaction tree into another. `PointedMachine.seqComp` runs one pointed
   machine until it returns an intermediate value and then initializes the
   next machine. This is Kleisli composition, not lens composition.

The distinction matters because `seqComp` cannot be encoded merely as a lens
into `q ◃ r`:

- its state is the phase coproduct `M₁.State ⊕ M₂.State`, whereas directions
  of a substitution composite contain dependent data from both phases;
- the handoff occurs after an unbounded, dynamically determined number of
  interface steps;
- the handoff is silent and depends on `init` and `output`, data absent from a
  bare `DynSystem` lens;
- both phases use the same external interface rather than producing a static
  composite interface.

The current bridge between machine and program presentations is
`PointedMachine.toComp`. Its run semantics is the fold
`runWith = FreeM.liftM ∘ toComp`. Under a `ResolvesIn` certificate, the
fuel-exact `runWithInput_seqComp` theorem says that machine sequencing denotes
the corresponding `OptionT` Kleisli composition at the summed budget. Without
that termination witness, a fixed-fuel statement is false because fuel is
threaded continuously through the handoff. Once both denotations exist, their
Kleisli composition associates by the monad laws even though nested sum state
types do not associate definitionally.

## What has already unified cleanly

- Lenses and charts use their `Category` instances; their identity and
  associativity laws are definitional.
- `DynSystem S p` is definitionally a lens `selfMonomial S ⇆ p`, so interface
  wrapping and polynomial products reuse lens composition and monoidal maps.
- `FreeM.liftM` and monad morphisms move programs between interpretations.
- `DynSystem.behavior` / `M.corec` moves a machine into its final behavior
  tree, with uniqueness providing the simulation proof principle.
- `nStep` uses the state comonoid's iterated comultiplication to package a
  fixed number of interface steps. It is not the dynamically bounded handoff
  used by `seqComp`.

These bridges should remain small and explicit. Giving unrelated operations
the same notation does not itself create a common abstraction.

## The maximal common framework

Chapter 8's double category of comonoids and bicomodules is the natural home in
which both axes coexist. Comonoids are objects, retrofunctors are vertical
morphisms, bicomodules are horizontal morphisms, and bicomodule composition is
the general “run by connecting a boundary” operation. Ordinary polynomial
lenses occur at the trivial boundary; dynamical systems and data-boundary
programs occur at nontrivial boundaries. Tensor and substitution provide the
duoidal structure behind the interchange laws.

This is an architectural target, not permission to collapse today's APIs into
an untested generic layer. The generic construction earns its place only when
it makes an existing consumer simpler. In particular, it should eventually
explain rather than obscure:

- the relation between `FreeM.append` and `PointedMachine.seqComp`;
- the shared wiring core behind UC `par`, `wire`, and `plug`;
- `DynSystem` behavior as the mate into the cofree comonoid;
- fixed finite runs (`nStep`) as projections of the same behavior.

## Staged path

### 1. Retrofunctors — completed

`Comonoid.Hom` is now a law-carrying retrofunctor with identity, composition,
and the resulting category of comonoids (`Cat♯`). Its state-comonoid
specialization is connected to very-well-behaved state lenses, providing the
concrete category example rather than testing only the abstract structure.

### 2. Program-axis bridge — completed at finite fuel

`runWithInput_seqComp` proves the certified finite-fuel Kleisli equation, and
`run_seqComp_eq_append` identifies its free syntax with `FreeM.append` through
`append_output_eq_bind`. The raw type `FreeM p (Option β)` already is the
`OptionT (FreeM p)` representation at the value level, so an additional
wrapper would add no laws or eliminators. The theorem equates denotations and
does not identify the machines' incompatible nested-sum state presentations.

### 3. Cofree comonoid and mate

Build paths in behavior trees, the cofree comonoid on a polynomial, and the
mate whose underlying map is `M.corec`. This should re-express existing
`behavior` and `nStep` theorems before adding new theory.

### 4. Comodules, then bicomodule composition

Start with diagonal/state instances, where many laws reduce definitionally.
Only then implement generic bicomodule composition. The generic case carries
real transport through the non-definitional `◃` associator; named equivalences
and reusable heterogeneous-equality lemmas belong at this boundary, never raw
casts in user-facing definitions.

## Acceptance tests

Each stage has a falsifiable payoff:

- retrofunctors replace an ad-hoc implementation-map vocabulary;
- the machine/program bridge proves `seqComp` and `append` agree after
  interpretation;
- the cofree mate derives the existing behavior uniqueness and finite-run
  projections;
- bicomodule composition reduces the number of primitive UC wiring operations
  or their independent coherence proofs.

If a stage adds more representation shuffling than it removes from its named
consumer, stop there. The correct abstraction boundary is the most general one
whose laws and eliminators improve the code that already exists.

## Known risks

- `Comonoid` supports independent position and direction universes, but
  `Comonoid.Hom` currently relates objects at one fixed universe pair because
  its counit law compares specific universe instances of `y`. A category or
  bicomodule layer spanning universe pairs will require explicit unit lifts and
  coherence.
- `◃` associativity is an equivalence, not definitional equality. Generic
  coaction and bicomodule-composition laws therefore contain genuine dependent
  transport.
- UC state sharing (for example, a global random oracle) is not modeled by
  taking a disjoint union of local states. The eventual boundary must support a
  shared resource algebra and explicit ownership/access maps. Bicomodules may
  organize the wiring, but they do not by themselves choose the resource
  semantics.

The last point is a guardrail: state aggregation is a policy supplied by a
model, not a universal `Sum` or product chosen by the core calculus.
