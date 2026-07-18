# Aberlé's parallel composition in PolyFun

This note records the G6 implementation of the parallel constructions from
Aberlé, *Compositional Program Verification with Polynomial Functors in
Dependent Type Theory* ([Abe26](../../REFERENCES.md#abe26--aberlé-compositional-program-verification-with-polynomial-functors)).

## The interface operation

For polynomial interfaces `P` and `Q`, the parallel sum `P ∥ Q` has three
kinds of operation:

- a left operation, with a left answer;
- a right operation, with a right answer;
- a joint operation, with a pair of answers.

It is therefore neither the coproduct nor the Dirichlet tensor. PolyFun uses
the direct carrier `ParallelChoice` and proves

```text
P ∥ Q ≃ₚ (P + Q) + (P ⊗ Q).
```

The zero polynomial is the unit, and explicit polynomial equivalences give
symmetry and associativity. The implementation follows the existing
`PFunctor.sum`/handler convention that the two interfaces share a direction
universe; their position universes remain independent.

## Displays and programs

An arbitrary display over `P ∥ Q` has three independently chosen components:
a display over `P`, a display over `Q`, and a display over `P ⊗ Q` for the
joint branch. `Display.parallelSumComponents S T U` constructs this general
form, while `leftComponent`, `rightComponent`, and `jointComponent` recover
the three pieces. The joint component `U` is genuinely relational: for
example, its position evidence can require the two simultaneous operations to
be equal, a condition that cannot in general factor into unary evidence.
The strict constructor and decomposition use a common evidence universe for
definitional round trips. `Display.parallelSumComponentsLift` accepts three
independent position and direction evidence universes, lifts each branch into
their maxima, and exposes canonical equivalences back to every component.

The paper's concrete binary operation `r ∥Dep s` is the separable
specialization `Display.parallelSum S T`: its joint component is
`Display.tensor S T`, so joint position and direction evidence are products.
One-sided branches contain only the active evidence and use `ULift` to place
independently universe-polymorphic evidence in the common result universe.

`FreeM.parallel` is the paper's synchronized `bothProg`: it emits a joint node
while both programs are blocked, then one-sided nodes after either program
returns. `FreeM.parallelAfterLeftReturn` names this residual phase explicitly.
Left/right program embeddings, parallel handlers, and all their displayed
lifts use the same operational definition.

Although unrestricted handler composition interchange fails below, ordinary
and displayed parallel handlers do preserve identities; the displayed law is
stated over the ordinary `Handler.parallel_id` index equality.

At the polynomial-lens level, parallel sum is a genuine symmetric monoidal
bifunctor: the implementation proves functoriality, braiding naturality and
involutivity, associator naturality, the pentagon, and the triangle. Lockstep
`FreeM.parallel` also respects the unit, symmetry, and associativity maps as a
program operation.

It is important not to strengthen the latter fact into unrestricted Kleisli
bifunctoriality. In general,

```text
(g₁ ∥Prog g₂) ∘ (f₁ ∥Prog f₂)
  ≠ (g₁ ∘ f₁) ∥Prog (g₂ ∘ f₂).
```

Interpreting the first layer can erase an operation on one side and thereby
change which later operations synchronize. The regression suite contains a
concrete counterexample whose two sides begin with different constructors.
Thus the paper's fully monoidal handler interpretation requires an additional
synchronization, commutativity, or scheduling discipline; it does not follow
for arbitrary `FreeM` handlers from the lockstep definition alone.

## Responders and verified behavior

`Responder.parallel` has product state. A left-only query advances the left
state and freezes the right; a right-only query does the converse; a joint
query advances both. `Responder.parallelCoalgebra` proves that paired
proof-relevant invariants are preserved for `Display.parallelSum`.

State-free behavior is obtained by running the parallel product of the two
terminal responders from a pair of behavior trees. This is deliberately not
presented as merely `CofreeP.laxTensor`: the synchronized joint component is
tensor-like, but the one-sided branches must retain the inactive behavior.
`parallelVerifiedBehavior` applies terminal displayed semantics to the same
coalgebra construction.

## Compatibility and scope

Execution theorems show that one-sided runs freeze the inactive state and that
a synchronized run returns exactly the pair of component results and final
states. Consequently responder reindexing commutes with parallel handlers.
The G5 Pattern-Runs-on-Matter reconstruction inherits the same theorem through
`reindexViaRunAgainst_eq_reindex`.

`Wiring.evalParallel` specializes recursive-wiring evaluation to two
independent inputs and combines the resulting handlers. Its target is the
duplicated interface `sigma inputInterface ∥ sigma inputInterface`, rather
than a shared input: this exposes the absence of contraction instead of
silently asserting ownership or race freedom. `evalDisplayedParallel` gives
the corresponding displayed handler.

This layer does **not** claim that arbitrary recursive `Wiring` is race-free.
Such a theorem needs an affine/ownership discipline controlling shared inputs;
the one-or-both interface and verified responder closure alone do not provide
that hypothesis.
