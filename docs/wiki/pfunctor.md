# Polynomial Functors and `FreeM`

This page is the agent-facing tour of `PolyFun/PFunctor/`. It is
descriptive, not load-bearing:
the source files are the canonical reference. Cite Lean source by file path
plus declaration name when accuracy matters.

## Why polynomial functors

A **polynomial functor** is a pair `⟨A, B⟩` where

- `A : Type*` is the *position* / *shape* type;
- `B : A → Type*` is the *direction* / *arity* family.

Concretely, a `PFunctor` is a generic notion of "branching tree shape":
each shape `a : A` chooses a branching arity `B a`. This single primitive
captures inductive types (`W`-types), free monads on signatures, M-types
(coinductive types), event signatures for interaction trees, and the kind
of dependent typing needed for protocol move spaces.

The Spivak-Niu *Poly* category (positions and directions composed via
`Σ` / `Π`) is the categorical home of all of these. PolyFun internalizes
enough of that category to model:

- free monads on signatures (`PFunctor.FreeM`);
- displayed families and decorations over them
  (`PFunctor.FreeM.Displayed`);
- branch paths through trees (`PFunctor.FreeM.Path`);
- finite typed prefixes selecting residual subtrees (`PFunctor.FreeM.Cursor`);
- the cofree comonad / M-type (`PFunctor.CofreeC`);
- lenses and charts between polynomial functors as morphisms of two
  natural categories on `Poly`;
- numeric and structural ornaments (`PFunctor.Bound`).

References:
[`REFERENCES.md`](../../REFERENCES.md). Hancock-Setzer 2000,
Altenkirch-Ghani-Hancock-McBride-Morris 2015 (*Indexed Containers*),
Spivak-Niu 2024 (*Polynomial Functors: A Mathematical Theory of Interaction*),
McBride 2010 / Dagand-McBride 2014 (displayed algebras / ornaments).

## File index

### Substrate (cycle root)

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Basic.lean`](../../PolyFun/PFunctor/Basic.lean) | `PFunctor` core, `Obj`, sum / product / sigma / pi / tensor / composition, `Lens`, `selfMonomial`, ring-style `0` / `1` / `+` / `*`. |
| [`PolyFun/PFunctor/Equiv/Basic.lean`](../../PolyFun/PFunctor/Equiv/Basic.lean) | Equivalences `P ≃ₚ Q` and canonical equivalences for sums, products, sigma / pi, tensor, composition, universe lifts. |
| [`PolyFun/PFunctor/M.lean`](../../PolyFun/PFunctor/M.lean) | Extensions to Mathlib's `PFunctor.M` (M-type / final coalgebra) used downstream. |
| [`PolyFun/PFunctor/M/Vertex.lean`](../../PolyFun/PFunctor/M/Vertex.lean) | Finite rooted vertices of an M-type tree: subtree selection, concatenation, canonical depth splitting, prefixes, dependent transport, and contravariant path mapping along lenses. This is the coinductive counterpart of `FreeM.Cursor`; the selected subtree is computed rather than stored as a second index so that vertices directly form the cofree polynomial's direction family. |
| [`PolyFun/PFunctor/Bound.lean`](../../PolyFun/PFunctor/Bound.lean) | Roll bounds for `FreeM` (budget-based termination predicate). |

### Lenses and charts

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Lens/Basic.lean`](../../PolyFun/PFunctor/Lens/Basic.lean) | Properties of `Lens P Q`: extensionality, composition lemmas, action on `Obj`, and the standard polynomial combinators. |
| [`PolyFun/PFunctor/Lens/Cartesian.lean`](../../PolyFun/PFunctor/Lens/Cartesian.lean) | Cartesian lenses (`toFunB a` is a bijection); fiberwise isomorphisms over a forward position map. |
| [`PolyFun/PFunctor/Lens/State.lean`](../../PolyFun/PFunctor/Lens/State.lean) | Lawful state-lens specialization for the self-monomial polynomial (`get`, `put`, `PutGet` / `GetPut` / `PutPut`). |
| [`PolyFun/PFunctor/Lens/Composite.lean`](../../PolyFun/PFunctor/Lens/Composite.lean) | Direct `Lens.compOuter` / `compInner` / `compPullback` views of a lens into `q ◃ r` (Ex 6.40), plus `Lens.compNthMap` (φ^◁n) and its `zero` / `succ` / `id` laws. |
| [`PolyFun/PFunctor/Lens/Distributivity.lean`](../../PolyFun/PFunctor/Lens/Distributivity.lean) | Left-distributivity of `◃`: Π-indexed `piCompDistrib` (6.51), `prodCompDistrib` (6.49), `scalarCompDistrib` (Ex 6.55), `homMonomialEquiv` (6.65), and the Ex 6.56 right-distributivity failure. |
| [`PolyFun/PFunctor/Lens/Factorization.lean`](../../PolyFun/PFunctor/Lens/Factorization.lean) | Vertical–cartesian factorization (Prop 5.52/5.53), closure under polynomial operations, `equivOfVerticalCartesian`, and vertical-left/cartesian-right orthogonality through the unique `DiagonalFiller`. |
| [`PolyFun/PFunctor/Lens/Duoidal.lean`](../../PolyFun/PFunctor/Lens/Duoidal.lean) | `orderingLens` and `duoidalLens` with cartesianness, naturality, middle-four compatibility, the internal/external associativity and four mixed-unit diagrams, and the common unit object's monoid/comonoid laws; the Ex 6.84 catalogue of `⊗`/`◃` coincidences. Only abstract duoidal-category packaging is deferred. |
| [`PolyFun/PFunctor/Chart/Basic.lean`](../../PolyFun/PFunctor/Chart/Basic.lean) | Charts (forward map on both positions and directions). Chart category is isomorphic to `Set^→` and has a different monoidal structure from the lens category. |
| [`PolyFun/PFunctor/Category.lean`](../../PolyFun/PFunctor/Category.lean) | Category-theoretic packaging where applicable. |
| [`PolyFun/PFunctor/InternalHom.lean`](../../PolyFun/PFunctor/InternalHom.lean) | The `⊗`-internal hom `ihom q r` = `[q, r]` (Ex 4.78; positions are lenses `q ⇆ r`), the evaluation lens `Lens.eval`, and the tensor–hom adjunction `curry` / `uncurry` / `curryEquiv : Lens (p ⊗ q) r ≃ Lens p (ihom q r)`; `ihomSum`, `ihomX`. |
| [`PolyFun/PFunctor/CartesianClosed.lean`](../../PolyFun/PFunctor/CartesianClosed.lean) | Cartesian-closed structure w.r.t. the categorical product `*`: the exponential `exp`'s `CartesianClosed.eval` / `curry` / `uncurry` (Thm 5.31). Reference API — the load-bearing `⊗`-transposes are in `InternalHom.lean`. |
| [`PolyFun/PFunctor/Adjunctions.lean`](../../PolyFun/PFunctor/Adjunctions.lean) | Trivial-interface hom-set equivalences plus binary tensor gluing (Prop 5.49): direct one-sided lens views, `tensorGlue`, its β laws, and `tensorGlueEquiv` over compatible ordinary lenses. |
| [`PolyFun/PFunctor/Comonoid.lean`](../../PolyFun/PFunctor/Comonoid.lean) | Comonoids in `(Poly, ◃, y)`, state comonoids, `IsStateSystem`, and `comultN`; `Comonoid.Hom` packages retrofunctors and supplies the `Category Comonoid` (`Cat♯`). |
| [`PolyFun/PFunctor/Comonoid/Category.lean`](../../PolyFun/PFunctor/Comonoid/Category.lean) | The extraction direction of the Ahman–Uustalu outgoing-arrow dictionary for a polynomial comonoid: identities, categorical targets, composition, their category laws, and the corresponding identity/target/composition laws of retrofunctors. `Hom.ofCategoryLaws` reconstructs a comonoid homomorphism from those three retrofunctor laws; the reverse object-level category construction and packaged equivalence are deferred. |
| [`PolyFun/PFunctor/Comonoid/Tensor.lean`](../../PolyFun/PFunctor/Comonoid/Tensor.lean) | The composition-unit comonoid, heterogeneous tensor product of composition comonoids built from duoidal interchange, componentwise tensor of retrofunctors, and pointwise tensor-unit/associativity isomorphisms. This is the concrete object/morphism and coherence construction behind Proposition 8.77 in the current edition (Proposition 8.79 in earlier-edition notes), not abstract monoidal-category or natural-isomorphism packaging, pentagon/triangle laws, or the categorical-product universal property. |

### Substitution monoids and their free construction

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/SubstMonoid.lean`](../../PolyFun/PFunctor/SubstMonoid.lean) | Monoid objects in `(Poly, ◃, y)`, their unit/multiplication-preserving lens homomorphisms, and the category of substitution monoids. |
| [`PolyFun/PFunctor/SubstMonoid/Extension.lean`](../../PolyFun/PFunctor/SubstMonoid/Extension.lean) | The extension of a substitution monoid as a `LawfulMonad` and the induced ordinary `MonadHom` of a substitution-monoid homomorphism. |
| [`PolyFun/PFunctor/SubstMonoid/Convolution.lean`](../../PolyFun/PFunctor/SubstMonoid/Convolution.lean) | The internal-hom convolution substitution monoid `[C,M]` induced by a composition comonoid `C`, a substitution monoid `M`, tensor closure, and duoidal interchange. This is the algebraic dependency used to construct the Libkind–Spivak free/cofree interaction map; the interaction itself is downstream. |
| [`PolyFun/PFunctor/Free/Polynomial.lean`](../../PolyFun/PFunctor/Free/Polynomial.lean) | `FreeP P`, whose positions are unlabelled well-founded `P`-trees and whose directions are complete leaf paths; its equivalence with `FreeM P`, functorial action, and substitution-monoid laws. |
| [`PolyFun/PFunctor/Free/Universal.lean`](../../PolyFun/PFunctor/Free/Universal.lean) | The universal property `SubstMonoid.Hom (FreeP.substMonoid P) M ≃ Lens P M.carrier`; its fold is identified with `FreeM.liftM` in the extension monad, including the full dependent backward-path law. |

### Dynamical systems (Spivak–Niu Ch. 4)

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Dynamical/Basic.lean`](../../PolyFun/PFunctor/Dynamical/Basic.lean) | `DynSystem S p` (a `p`-system on states `S`, definitionally the lens type `Lens (selfMonomial S) p`, with accessors `expose` / `update` and constructor `mk'`); `Machine p`, the minimal bundle of a state type and `toDynSystem`; the coalgebra structure map `out : S → p.Obj S` with its packaging `DynSystem.coalg : Coalg p.Obj S`; concrete `Step`s and `StepRel` (`comp` / `top` / `reverse` / `inter` / `sync`); `MooreMachine`, `DeterministicAutomaton`, `Closed` / `Closed.iterate`, `Point` (`X ⟹ p`) and `Section` (`p ⟹ X`) / `sectionLens`. |
| [`PolyFun/PFunctor/Dynamical/Safety.lean`](../../PolyFun/PFunctor/Dynamical/Safety.lean) | Transition metadata and safety specifications extending `Machine`: `EventMap` / `Tickets`, `Labeled` / `Ticketed`, and `SafetySpec` (`init` / `assumptions` / `safe`). Their dynamics are uniformly available as `.toDynSystem`. Instantiated by concurrent machines and processes. |
| [`PolyFun/PFunctor/Dynamical/Combinators.lean`](../../PolyFun/PFunctor/Dynamical/Combinators.lean) | Building systems from old ones: `wrap` (§4.3.3), `close` / `MooreMachine.feedback` (§4.3.4), `tensor` (§4.3.2), `pairing` (§4.3.1), `choiceProd` (asynchronous choice), `Wiring₂` / `wire₂` (§4.4). |
| [`PolyFun/PFunctor/Dynamical/Run.lean`](../../PolyFun/PFunctor/Dynamical/Run.lean) | Generic orbits: `DynSystem.Prefix` / `DynSystem.Run` (with `take`, `event(s)`/`ticket(s)`, `Prefix.last`, `RelUpTo` / `Rel`); `DynSystem.ReachableIn` (`n`-step reachability via `Prefix`); Moore finite runs `run`, `trace`, `outputOn`, `DeterministicAutomaton.accepts`; input streams `stateStream` / `outputStream` with `stateStream_eq_run`; `streamRun` / `iterateRun` identifying them with generic runs. |
| [`PolyFun/PFunctor/Dynamical/Trajectory.lean`](../../PolyFun/PFunctor/Dynamical/Trajectory.lean) | Infinite behaviour: terminal-coalgebra `behavior : S → M p` with `behavior_unique` and `ObsEq`; cofree `trajectory : DynSystem S p → S → CofreeC p p.A` with `trajectory_eq_selfLabel_behavior`; closed-system spine `CofreeC.next`, `next_iterate_trajectory`. |
| [`PolyFun/PFunctor/Dynamical/CofreeMate.lean`](../../PolyFun/PFunctor/Dynamical/CofreeMate.lean) | The dynamical specialization of the cofree universal property: generic coiteration has object map `behavior`; applying the full mate lens to arbitrary state labels and decoding yields `labeledTrajectory`; at the current homogeneous maximum, `cofreeMate` is the unique full retrofunctor restricting to the original system. The existing `trajectory` is the exposed-position specialization. |
| [`PolyFun/PFunctor/Dynamical/CofreeMate/FiniteProjection.lean`](../../PolyFun/PFunctor/Dynamical/CofreeMate/FiniteProjection.lean) | Proposition 8.49 for dynamical systems: composing `cofreeMate` with the depth-`n` cofree projection is exactly `DynSystem.nStep n`; the depth-two corollary agrees with `twoStep` after the inner right unitor. |
| [`PolyFun/PFunctor/Dynamical/Behavior.lean`](../../PolyFun/PFunctor/Dynamical/Behavior.lean) | Closed-loop behaviour of a Moore machine: `feedbackStep`, `feedbackStream`, `next_iterate_feedback`. |
| [`PolyFun/PFunctor/Handler.lean`](../../PolyFun/PFunctor/Handler.lean) | `Handler m p`: a monadic choice of direction at every position of `p`; the generic interface consumed by `FreeM.liftM`, with indexed coproduct combination. |
| [`PolyFun/PFunctor/Handler/Free.lean`](../../PolyFun/PFunctor/Handler/Free.lean) | Identity and categorical-order Kleisli composition for handlers valued in `FreeM`. |
| [`PolyFun/PFunctor/Resumption.lean`](../../PolyFun/PFunctor/Resumption.lean) | `Resumption p β := M (C β + p)`, the canonical possibly infinite tau-free return-or-query behavior, with `corec`, `pure`, `query`, universe-polymorphic `map` / `bind`, and lawful monad structure. |
| [`PolyFun/PFunctor/Dynamical/DynComputation.lean`](../../PolyFun/PFunctor/Dynamical/DynComputation.lean) | `DynComputation p α β`, extending `Machine (C β + p)` with `init`; `view` exposes returns or visible queries and `denote` gives `α → Resumption p β`. `ofResumption` and `ofFreeM` are canonical realizations, while `Implements` and `implements_of_isSimulation` provide qualitative correctness. |
| [`PolyFun/PFunctor/Dynamical/IOMachine.lean`](../../PolyFun/PFunctor/Dynamical/IOMachine.lean) | `IOMachine`, extending the minimal `Machine` substrate with `init` and partial `output`; variance/wrapping laws, chosen-position `pureAt`, state-level `toComp`, input-level `run`, and interpreted `runWithInput`; `seqComp` has syntactic/semantic identity laws and the fuel-exact Kleisli composition theorem. Its dynamics are uniformly available as `.toDynSystem`. |
| [`PolyFun/PFunctor/Dynamical/RunN.lean`](../../PolyFun/PFunctor/Dynamical/RunN.lean) | `DynSystem.twoStep` (Ex 6.44) and `DynSystem.nStep` = `Run_n(φ) = δ^{(n)} ⨟ φ^{◁n}` (§7.1.5) over `compNth p n`; `nStep_two_eq_twoStep` identifies the `n = 2` specialization after the inner unitor. The transition lens itself is `Lens.fixState`. |
| [`PolyFun/PFunctor/Dynamical/Simulation.lean`](../../PolyFun/PFunctor/Dynamical/Simulation.lean) | `DynSystem.IsSimulation` (step-synchronized relation) with `behavior_eq_of_isSimulation` — related states have equal `behavior`, via `M.corec_eq_corec`; `isSimulation_graph` / `behavior_coalgHom` — coalgebra morphisms are the functional simulations. |
| [`PolyFun/PFunctor/Dynamical/Refinement.lean`](../../PolyFun/PFunctor/Dynamical/Refinement.lean) | Operational `DynSystem.ForwardSimulation` between bare systems, with `mapRun` and its transport lemmas; `SafetyRefinement` extends it with initial-state coverage, assumption preservation, and safety reflection; `ReverseSafetyRefinement` / `MutualSafetyRefinement` package one- and two-way safety refinement; `ForwardSimulation.ofIsSimulation` embeds `IsSimulation` at `StepRel.sync`. Instantiated by the concurrent refinement layers. |
| [`PolyFun/PFunctor/Dynamical/Responder.lean`](../../PolyFun/PFunctor/Dynamical/Responder.lean) | `Responder S q := DynSystem S (q ⊸ X)`: state systems whose positions are committed answer-sections (`committed` / `answer` / `next`); the Kleisli–Mealy `equivStateHandler : Responder S q ≃ Handler (StateT S Id) q` with `rfl` round-trips. |
| [`PolyFun/PFunctor/Dynamical/Game.lean`](../../PolyFun/PFunctor/Dynamical/Game.lean) | Game wiring: `DynSystem.game := wire₂ (Lens.eval q r)` and its autonomous `closedGame`, `game_eq_uncurry` (the adjunction reading); monadic runs `kleisliStep` / `kleisliIterate` / `stepWith` / `iterWith`; two-phase `Lens.eval₂` / `orderPair` / `game₂` (Eq 6.86 / Ex 6.85). |
| [`PolyFun/PFunctor/Dynamical/Bisimulation.lean`](../../PolyFun/PFunctor/Dynamical/Bisimulation.lean) | `DynSystem.toLTS` exhibits a `p`-system as a labelled transition system; `isStrongSimulation_toLTS_iff_isSimulation` identifies generic strong simulation with the native synchronized notion, and `obsEq_of_isStrongSimulation` derives behaviour-tree equality through finality. See [`bisimulation.md`](bisimulation.md). |
| [`PolyFun/ITree/Unfold.lean`](../../PolyFun/ITree/Unfold.lean) | `DynSystem.toITree`: unfold a dynamical system into an all-query interaction tree; `M.toITree` embeds behaviour trees. |
| [`PolyFunTest/PFunctor/Dynamical/Examples.lean`](../../PolyFunTest/PFunctor/Dynamical/Examples.lean) | Worked examples / regression tests (counter, parity automaton, mode-dependent `gate`, feedback / stream behaviour, the `univ`-system `toggle`, generic runs, `choiceProd`, behaviour / ITree unfolding). |

### Displays over a polynomial

`PFunctor.Display P` is local polynomial data over one base polynomial:

```text
position : (a : P.A) → Type
direction : (a : P.A) → position a → P.B a → Type
```

It is intentionally distinct from the older `FreeM.Displayed` namespace:

| Layer | Meaning | Generality |
|------|---------|------------|
| `PFunctor.Display P` | One-step displayed positions and directions over `P` | Polynomial and `Type`-valued |
| `FreeM.Displayed.Algebra P E` | Higher-order recipe assigning leaf and node fibers | Arbitrary `Sort`-valued node operation; need not be functorial |
| `FreeM.Displayed D t` | Evaluation of one algebra over a concrete free tree `t` | A fiber, not new one-step structure |
| `FreeM.Displayed.Over R t d` | A second fiber over existing displayed data `d` | Depends on both the tree and first-layer inhabitant |

`Display.toDisplayedAlgebra` embeds a display into the generic algebra layer. Its
node operation is exactly the polynomial action
`X ↦ Σ c, ∀ b, direction a c b → X b`; this restriction is what supports
`Display.bind`, displayed handlers, and displayed Kleisli composition.

A display also has two complementary structural readings. `Display.total`
packages its total positions and directions and `Display.forget` is a chart
back to `P`; conversely, `Display.ofChart` takes the literal fibers of any
chart into `P`, at the cost of equality witnesses and transports. Meanwhile
`Display.incidence` and `Display.action` are `IPFunctor`s. An arbitrary
`IPFunctor I J` fixes unrelated input/output index types, while a display
uniformly derives those indexed actions from one base polynomial as its
carrier varies.

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Display/Basic.lean`](../../PolyFun/PFunctor/Display/Basic.lean) | Core display, object action, predicate contracts, and coproducts. |
| [`PolyFun/PFunctor/Display/Chart.lean`](../../PolyFun/PFunctor/Display/Chart.lean) | Total-polynomial chart and chart-fiber normalization. |
| [`PolyFun/PFunctor/Display/Coalgebra.lean`](../../PolyFun/PFunctor/Display/Coalgebra.lean) | Proof-relevant displayed coalgebras over a fixed base coalgebra map. |
| [`PolyFun/PFunctor/Display/Indexed.lean`](../../PolyFun/PFunctor/Display/Indexed.lean) | Incidence/action `IPFunctor`s and object-action equivalence. |
| [`PolyFun/PFunctor/Display/M.lean`](../../PolyFun/PFunctor/Display/M.lean) | `Display.M S tree`, the greatest displayed fixed point over an ordinary M-tree; transport equivalences and cancellation, constructor/destructor equivalence, native displayed corecursion and related-seed coinduction, finality, and cast-free displayed bisimulation. |
| [`PolyFun/PFunctor/Display/Free.lean`](../../PolyFun/PFunctor/Display/Free.lean) | Embedding into `Displayed.Algebra` and dependent substitution. |
| [`PolyFun/PFunctor/Display/Handler.lean`](../../PolyFun/PFunctor/Display/Handler.lean) | Displayed handlers, free extension, and Kleisli composition. |
| [`PolyFun/PFunctor/Display/Category.lean`](../../PolyFun/PFunctor/Display/Category.lean) | Structural equivalence between free handlers and lenses into `FreeP`; compatibility with the existing free-polynomial fold; and transported identity/associativity for proof-relevant displayed-handler hom fibers. |
| [`PolyFun/PFunctor/Dynamical/Responder/Display.lean`](../../PolyFun/PFunctor/Dynamical/Responder/Display.lean) | The responder display, its forgetful chart, and the equivalence between displayed responder coalgebras and the paper's local dependent-Mealy obligation. The projection is not generally a lens because a bare query does not supply the required precondition witness. |
| [`PolyFun/PFunctor/Display/Handler/Sigma.lean`](../../PolyFun/PFunctor/Display/Handler/Sigma.lean) | Displayed witnesses for indexed handler coproducts, plus displayed coproduct injections. |
| [`PolyFun/PFunctor/Wiring.lean`](../../PolyFun/PFunctor/Wiring.lean) | Recursive many-box wiring with external inputs, base and displayed evaluation, display-compatibility witnesses, wiring substitution, and the free-handler fusion law. Distinct from the binary dynamical lens alias `DynSystem.Wiring₂`. |
| [`PolyFun/PFunctor/Dynamical/Responder/Reindex.lean`](../../PolyFun/PFunctor/Dynamical/Responder/Reindex.lean) | Universe-polymorphic finite free-program execution against responders; contravariant responder reindexing; proof-relevant displayed execution and coalgebra reindexing; transported identity, composition, substitution, and execution-fusion laws. |
| [`PolyFun/PFunctor/Dynamical/Responder/Behavior.lean`](../../PolyFun/PFunctor/Dynamical/Responder/Behavior.lean) | State-free responder behavior as the existing `M (P ⊸ X)`; coinductive `respondDisplayed` (the intrinsic form of Aberlé's `appD`) and observation-shaped bisimulation through `Display.M (Display.responder S)`; agreement of finite displayed execution with state presentations; and ordinary/verified state-free handler reindexing with transported identity/composition and exact post/continuation equations. |

Displayed responder coalgebras preserve proof-relevant evidence over one
responder. They are distinct from `DynSystem.SafetyRefinement`, whose policy is
a proposition-valued relation between two systems.

### Free monad `FreeM`

`PFunctor.FreeM` is **re-exported from upstream cslib**
(`Cslib.Foundations.Data.PFunctor.Free`, originally ported from VCVio). cslib
supplies the inductive type (constructors `pure` / `liftBind`), the `bind` / `map`
/ `Monad` / `LawfulMonad` / `MonadLift` instances, the `@[induction_eliminator]
induction` principle (non-pure case `lift_bind`), the shape lift `lift : P.A →
FreeM (P.B a)` and object lift `liftObj : P.Obj α → FreeM α`, and the `liftM`
interpreter with its `Interprets` universal property. PolyFun layers its own API
(`mapLens`, `liftM` monad-hom and naturality lemmas, `toW` / `equivWOfIsEmpty`, paths,
displayed families, roll bounds) on top of the upstream type.

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Free/Basic.lean`](../../PolyFun/PFunctor/Free/Basic.lean) | Re-exports cslib's `FreeM P α` (`pure` / `liftBind`) and canonical `liftM` evaluator; adds `mapLens`, `liftMHom` naturality, arbitrary-monad handler fusion, and `toW` / `ofW` / `equivWOfIsEmpty`. |
| [`PolyFun/PFunctor/Free/Resumption.lean`](../../PolyFun/PFunctor/Free/Resumption.lean) | Injective monad-hom embedding `FreeM.toResumption`, with constructor, bind, and map compatibility laws. Kept separate to preserve the base `Resumption` import layer. |
| [`PolyFun/PFunctor/Free/Path.lean`](../../PolyFun/PFunctor/Free/Path.lean) | `FreeM.Path s` (explicit polynomial direction at every node), `PathAlong`, `output`, `append`, the generic `StoppingTree` initial algebra, and its canonical-path `Telescope` specialization. |
| [`PolyFun/PFunctor/Free/Path/Execution.lean`](../../PolyFun/PFunctor/Free/Path/Execution.lean) | Structural `withPath` execution, erased `Path.trace`, and the exact recovery law `map_output_withPath`. |
| [`PolyFun/PFunctor/Free/Cursor.lean`](../../PolyFun/PFunctor/Free/Cursor.lean) | `FreeM.Cursor s`, a finite typed path prefix with an explicit residual subtree; composition, prefix traces, residual-path plugging, extension witnesses, and the equivalence between terminal cursors and complete `Path`s. |
| [`PolyFun/PFunctor/Free/Cursor/Append.lean`](../../PolyFun/PFunctor/Free/Cursor/Append.lean) | Cast-free classification of cursors through dependent `FreeM.append`, with prefix/suffix split-join equivalences, terminal-path compatibility, and decoration restriction laws. |
| [`PolyFun/PFunctor/Free/Cursor/Occurrence.lean`](../../PolyFun/PFunctor/Free/Cursor/Occurrence.lean) | Path-independent `Occurrence` refinements of `Cursor`, certified execution splitting, completion, and prefix-first `forkAt`. |
| [`PolyFun/PFunctor/Free/Cursor/Fork.lean`](../../PolyFun/PFunctor/Free/Cursor/Fork.lean) | Locating occurrences in completed paths, total forking from a located context, fixed and dynamically selected optional forking, observation fusion, and the prefix-first/path-first factorization theorem. |
| [`PolyFun/PFunctor/Free/Displayed.lean`](../../PolyFun/PFunctor/Free/Displayed.lean) | `FreeM.Displayed D s` (displayed family over a tree), `Displayed.Section` (global dependent section), and `Section.ofConstructors` (constructor-local fold). The substrate behind decorations, paths, and compact observations. |
| [`PolyFun/PFunctor/Free/Displayed/Decoration.lean`](../../PolyFun/PFunctor/Free/Displayed/Decoration.lean) | `Decoration Γ s`: every node carries one `Γ a` and recursively decorates children. |
| [`PolyFun/PFunctor/Free/Displayed/Cursor.lean`](../../PolyFun/PFunctor/Free/Displayed/Cursor.lean) | Explicit child-projection capabilities and restriction of navigable displayed data, node decorations, and dependent over-decorations to a `Cursor` residual. |

### Cofree / M-type companion

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Cofree.lean`](../../PolyFun/PFunctor/Cofree.lean) | `CofreeC` (cofree comonad on a `PFunctor`), built from `PFunctor.M` of the `constProd` polynomial. The dual of `FreeM`. |
| [`PolyFun/PFunctor/M/Vertex.lean`](../../PolyFun/PFunctor/M/Vertex.lean) | `M.Vertex t`, the finite path calculus selecting rooted subtrees of a potentially infinite `t : M P`; unlike the doubly indexed `FreeM.Cursor`, the residual is the `subtree` projection, which is the indexing choice needed for the cofree polynomial's direction type. |
| [`PolyFun/PFunctor/Display/M.lean`](../../PolyFun/PFunctor/Display/M.lean) | Coinductive proof-relevant fibers over fixed ordinary M-trees. Unlike `FreeM.Displayed`, this is greatest-fixed-point semantics generated by a one-step `Display`. |
| [`PolyFun/PFunctor/Cofree/Polynomial.lean`](../../PolyFun/PFunctor/Cofree/Polynomial.lean) | `CofreeP P`, whose positions are potentially infinite `P`-trees and whose directions are finite rooted vertices; its extension equivalence with `CofreeC P`, functorial action on lenses, and substitution-comonoid structure. Its carrier uses `max uA uB` for both polynomial universes because a vertex stores directions along an ambient `M P` tree. |
| [`PolyFun/PFunctor/Cofree/Universal.lean`](../../PolyFun/PFunctor/Cofree/Universal.lean) | Generic coiteration and the cofree-comonoid universal property `Comonoid.Hom C (CofreeP.comonoid P) ≃ Lens C.carrier P`, with explicit naturality in both variables. The generic unfolding keeps the comonoid and generator universe pairs independent; the hom-set packaging specializes `C` to the homogeneous `max uA uB` universe pair required by the existing `Comonoid.Hom`. This is unbundled adjunction data, not a `CategoryTheory.Adjunction`. |
| [`PolyFun/PFunctor/Cofree/FiniteProjection.lean`](../../PolyFun/PFunctor/Cofree/FiniteProjection.lean) | Universe-polymorphic structural finite projections `projectionN P n : CofreeP P ⇆ compNth P n`, their exact backward-map depth semantics and low-stage unitors, and the homogeneous algebraic bridge yielding the arbitrary-retrofunctor and cofree-extension forms of Proposition 8.49. Additive splitting (Equation 8.32) is deferred until its required composition-power reassociation equivalence is available. |
| [`PolyFun/PFunctor/Cofree/LaxMonoidal.lean`](../../PolyFun/PFunctor/Cofree/LaxMonoidal.lean) | The cofree functor's unit comparison `y ⇆ CofreeP y` and synchronized-tree laxator `CofreeP P ⊗ CofreeP Q ⇆ CofreeP (P ⊗ Q)`, packaged as retrofunctors and equipped with generator equations, fixed-universe categorical naturality, and the two unit and associativity laws. This is Proposition 8.79 in the current Spivak–Niu edition (Proposition 8.81 in the earlier-edition notes). Cross-universe naturality needs a heterogeneous retrofunctor-law API; abstract monoidal-functor packaging remains downstream. |
| [`PolyFun/PFunctor/PatternRunsOnMatter/Basic.lean`](../../PolyFun/PFunctor/PatternRunsOnMatter/Basic.lean) | The fully heterogeneous executable traversal `FreeP.runOn : FreeP P ⊗ CofreeP Q ⇆ FreeP (P ⊗ Q)`, including the complete backward map from output paths to pattern paths and finite matter vertices, and covariance in both generators. |
| [`PolyFun/PFunctor/PatternRunsOnMatter/Universal.lean`](../../PolyFun/PFunctor/PatternRunsOnMatter/Universal.lean) | The paper's curried convolution construction `FreeP.xi` and its equality with the independently executable traversal. For `Q : PFunctor.{qA,qB}`, the homogeneous free-extension API requires only `P`'s direction universe to be `max qA qB`; their position universes remain independent. |
| [`PolyFun/PFunctor/PatternRunsOnMatter/Module.lean`](../../PolyFun/PFunctor/PatternRunsOnMatter/Module.lean) | The concrete right-module unit and associativity laws for the Libkind--Spivak interaction. |
| [`PolyFun/PFunctor/PatternRunsOnMatter/Operational.lean`](../../PolyFun/PFunctor/PatternRunsOnMatter/Operational.lean) | Decoded execution, recursive and grafting laws, substitution-monoid compatibility, and lawful monadic handler interpretation. |
| [`PolyFun/PFunctor/PatternRunsOnMatter/Dynamical.lean`](../../PolyFun/PFunctor/PatternRunsOnMatter/Dynamical.lean) | Object-labelled execution on cofree behavior, reached-state semantics, observational/simulation invariance, and exact finite-game compatibility. |
| [`PolyFun/PFunctor/PatternRunsOnMatter/Applications.lean`](../../PolyFun/PFunctor/PatternRunsOnMatter/Applications.lean) | The Section 4 generic interaction composite, internal-hom evaluation and Equation (6), plus behavior and strong-simulation bridges. |
| [`PolyFun/PFunctor/PatternRunsOnMatter/Display.lean`](../../PolyFun/PFunctor/PatternRunsOnMatter/Display.lean) | Identification of responder and state-free handler reindexing with evaluated `runAgainstSystem`, including returned-state equality and transport of proof-relevant displayed coalgebra/behavior evidence. Raw `runOnSystem` is only the preceding Xi synchronization stage. |
| [`PolyFun/PFunctor/Trace.lean`](../../PolyFun/PFunctor/Trace.lean) | Polynomial-trace machinery shared between `PFunctor` and downstream layers. |

### Control helpers

`PolyFun/Control/` is logically below `PFunctor/Free` in the import DAG and
provides the reusable monad / comonad / coalgebra plumbing. See
[`PolyFun/Control/`](../../PolyFun/Control/) for the full inventory:
`Coalgebra` (the `Coalg` class: every `DynSystem S p` yields a `Coalg p.Obj S` via `DynSystem.coalg`),
`Comonad/{Basic, Instances}`, `Lawful/Basic`,
`Monad/{Algebra, Equiv, Free, FreeCont, Hom, Iter}`, `Trace`.

## Mental model

- `PFunctor` is a *small* gadget: just `(A : Type, B : A → Type)`. Almost
  every interesting structure in PolyFun is built by combining a few of
  these via `+` / `*` / `⊗` / `Σ` / `Π` / composition, or by taking the
  free monad / cofree comonad / lens / chart of one.
- `FreeM P` is the free monad on `P` (the upstream cslib type). Operationally
  it is the inductive type of well-founded `P`-branching trees with `α`-leaves,
  built from a `pure` leaf and a combined `liftBind` step. It is the syntax of
  "programs" in the signature `P`.
- `CofreeC P` is the cofree comonad on `P`. Coinductively, it is the
  type of infinite, fully-decorated `P`-trees. `CofreeP P` packages the
  same data polynomially: an unlabelled M-tree is a position and each finite
  rooted vertex is a direction; `(CofreeP P).Obj X ≃ CofreeC P X` labels all
  such vertices by `X`. Its root/vertex-concatenation lenses form the cofree
  substitution comonoid, while `CofreeP.map` supplies the heterogeneous
  lens-level functorial action. `Comonoid.Hom` requires its two carrier
  universe pairs to agree. The current `CofreeP.mapHom` API ensures that by
  choosing a common generator universe pair, so both resulting comonoid
  universes are definitionally `max uA uB`; a future lift/equal-maximum API
  could relax this specialization. `CofreeP.homEquiv` packages the cofree
  universal property at the same fixed-maximum boundary, while its underlying
  coiteration remains fully heterogeneous. `CofreeP.laxTensor` synchronizes
  two behavior trees node by node and proves the concrete naturality and
  monoidal coherence equations without installing an abstract monoidal-functor
  instance. PolyFun separately formalizes
  `LawfulMonad (FreeM P)` and `LawfulComonad (CofreeC F)`; those type-level
  structures are not the paper's polynomial module action. The latter is
  `FreeP.runOn : FreeP p ⊗ CofreeP q ⇆ FreeP (p ⊗ q)`: it executes a
  finite pattern against potentially infinite matter, is natural in both
  inputs, agrees with the paper's convolution/free-universal construction
  `FreeP.xi`, and satisfies the concrete unit and associativity equations.
- `Lens P Q` and `Chart P Q` are the two natural categorical morphisms
  between polynomial functors. Lenses go `forward on positions, backward
  on directions`; charts go forward on both. Both categories are useful
  and distinct.
- `Displayed D s` is the dependent-types view of "decorating every node
  of a tree with extra data". `Decoration Γ s` is the special case where
  the data only depends on the local position.

## What lives where downstream

- `PolyFun/ITree/` (see [`itree.md`](itree.md)) builds interaction trees
  as the M-type of a one-step polynomial functor. It uses
  `PolyFun/PFunctor/M.lean` and the cofree apparatus.
- `PolyFun/Interaction/Basic/` (see [`interaction.md`](interaction.md))
  builds protocol `TypeTree`s as `PFunctor.FreeM TypeTree.basePFunctor PUnit`,
  i.e. `PUnit`-leaved free trees on a particular base polynomial. Most
  of the interaction framework is just a dependent-typed dressing on top
  of `FreeM` plus `Decoration` / `Displayed`.

If a concept appears redundant between layers, the substrate version
(here, in `PFunctor/`) is almost always the load-bearing one. Downstream
layers exist to give protocol-flavored names and ergonomics; the maths
lives in `PFunctor/Free/`, `PFunctor/Cofree.lean`, and `PFunctor/Cofree/`.
