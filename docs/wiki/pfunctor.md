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
- the cofree comonad / M-type (`PFunctor.CofreeC`);
- lenses and charts between polynomial functors as morphisms of two
  natural categories on `Poly`;
- numeric and structural ornaments (`PFunctor.Bound`).

References:
[`REFERENCES.md`](../../REFERENCES.md). Hancock-Setzer 2000,
Altenkirch-Ghani-Hancock-McBride-Morris 2015 (*Indexed Containers*),
Spivak-Niu 2024 (*Polynomial Functors: A General Theory of Interaction*),
McBride 2010 / Dagand-McBride 2014 (displayed algebras / ornaments).

## File index

### Substrate (cycle root)

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Basic.lean`](../../PolyFun/PFunctor/Basic.lean) | `PFunctor` core, `Obj`, sum / product / sigma / pi / tensor / composition, `Lens`, `selfMonomial`, ring-style `0` / `1` / `+` / `*`. |
| [`PolyFun/PFunctor/Equiv/Basic.lean`](../../PolyFun/PFunctor/Equiv/Basic.lean) | Equivalences `P ≃ₚ Q` and canonical equivalences for sums, products, sigma / pi, tensor, composition, universe lifts. |
| [`PolyFun/PFunctor/M.lean`](../../PolyFun/PFunctor/M.lean) | Extensions to Mathlib's `PFunctor.M` (M-type / final coalgebra) used downstream. |
| [`PolyFun/PFunctor/Bound.lean`](../../PolyFun/PFunctor/Bound.lean) | Roll bounds for `FreeM` (budget-based termination predicate). |

### Lenses and charts

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Lens/Basic.lean`](../../PolyFun/PFunctor/Lens/Basic.lean) | Properties of `Lens P Q`: extensionality, composition lemmas, action on `Obj`. |
| [`PolyFun/PFunctor/Lens/Cartesian.lean`](../../PolyFun/PFunctor/Lens/Cartesian.lean) | Cartesian lenses (`toFunB a` is a bijection); fiberwise isomorphisms over a forward position map. |
| [`PolyFun/PFunctor/Lens/State.lean`](../../PolyFun/PFunctor/Lens/State.lean) | Lawful state-lens specialization for the self-monomial polynomial (`get`, `put`, `PutGet` / `GetPut` / `PutPut`). |
| [`PolyFun/PFunctor/Chart/Basic.lean`](../../PolyFun/PFunctor/Chart/Basic.lean) | Charts (forward map on both positions and directions). Chart category is isomorphic to `Set^→` and has a different monoidal structure from the lens category. |
| [`PolyFun/PFunctor/Category.lean`](../../PolyFun/PFunctor/Category.lean) | Category-theoretic packaging where applicable. |
| [`PolyFun/PFunctor/Comonoid.lean`](../../PolyFun/PFunctor/Comonoid.lean) | Comonoids in `(Poly, ◃, y)` (= small categories, Def 7.14): `Comonoid` structure with counit/comult and the lens laws; the state comonoid `stateComonoid S` on `Sy^S`; `IsStateSystem` (Ex 7.22); the `n`-fold comultiplication `comultN` = `δ^{(n)}` (Prop 7.20). |

### Dynamical systems (Spivak–Niu Ch. 4)

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Dynamical/Basic.lean`](../../PolyFun/PFunctor/Dynamical/Basic.lean) | `DynSystem p` (a `p`-system = lens `selfMonomial State ⟹ p`), `toLens`/`ofLens`; the coalgebra structure map `out : State → p.Obj State` with its `Coalg p.Obj` instance; `MooreMachine`, `DeterministicAutomaton`, `Closed` / `Closed.iterate`, `Point` (`X ⟹ p`) and `Section` (`p ⟹ X`) / `sectionLens`. |
| [`PolyFun/PFunctor/Dynamical/Safety.lean`](../../PolyFun/PFunctor/Dynamical/Safety.lean) | Transition metadata and safety specifications: `EventMap` / `Tickets`, `Labeled` / `Ticketed`, `SafetySpec` (`init` / `assumptions` / `safe`), and the step-matching relations `DirRel` (`top` / `reverse` / `inter`). Instantiated by concurrent machines and processes. |
| [`PolyFun/PFunctor/Dynamical/Combinators.lean`](../../PolyFun/PFunctor/Dynamical/Combinators.lean) | Building systems from old ones: `wrap` (§4.3.3), `close` / `MooreMachine.feedback` (§4.3.4), `tensor` (§4.3.2), `pairing` (§4.3.1), `choiceProd` (asynchronous choice), `Wiring₂` / `wire₂` (§4.4). |
| [`PolyFun/PFunctor/Dynamical/Run.lean`](../../PolyFun/PFunctor/Dynamical/Run.lean) | Generic orbits: `DynSystem.Prefix` / `DynSystem.Run` (with `take`, `event(s)`/`ticket(s)`, `Prefix.last`, `RelUpTo` / `Rel`); `DynSystem.ReachableIn` (`n`-step reachability via `Prefix`); Moore finite runs `run`, `trace`, `outputOn`, `DeterministicAutomaton.accepts`; input streams `stateStream` / `outputStream` with `stateStream_eq_run`; `streamRun` / `iterateRun` identifying them with generic runs. |
| [`PolyFun/PFunctor/Dynamical/Trajectory.lean`](../../PolyFun/PFunctor/Dynamical/Trajectory.lean) | Infinite behaviour: terminal-coalgebra `behavior : State → M p` with `behavior_unique` and `ObsEq`; cofree `trajectory : DynSystem p → State → CofreeC p p.A` with `trajectory_eq_selfLabel_behavior`; closed-system spine `CofreeC.next`, `next_iterate_trajectory`. |
| [`PolyFun/PFunctor/Dynamical/Behavior.lean`](../../PolyFun/PFunctor/Dynamical/Behavior.lean) | Closed-loop behaviour of a Moore machine: `feedbackStep`, `feedbackStream`, `next_iterate_feedback`. |
| [`PolyFun/PFunctor/Dynamical/Speedup.lean`](../../PolyFun/PFunctor/Dynamical/Speedup.lean) | The transition lens `δ = Lens.transitionLens` (Ex 6.44) and `DynSystem.twoStep` (the `n = 2` composite over `p ◃ p`). |
| [`PolyFun/PFunctor/Dynamical/PointedMachine.lean`](../../PolyFun/PFunctor/Dynamical/PointedMachine.lean) | `PointedMachine`: pointed machines (`init` / partial `output`) over an interface; `seqComp` (⊕-state sequential composition, Ex 6.41) with `toComp_seqComp_inl/inr`; fuelled `toComp`; monad-parametric `runWith` = `mapM ∘ toComp` with `runWith_succ` / `runWith_output_some` (fuel irrelevance). |
| [`PolyFun/PFunctor/Dynamical/RunN.lean`](../../PolyFun/PFunctor/Dynamical/RunN.lean) | `DynSystem.nStep` = `Run_n(φ) = δ^{(n)} ⨟ φ^{◁n}` (§7.1.5) over the composition power `compNth p n`; `twoStep_toLens_eq` collapses `n = 2` to `twoStep`. |
| [`PolyFun/PFunctor/Dynamical/Simulation.lean`](../../PolyFun/PFunctor/Dynamical/Simulation.lean) | `DynSystem.IsSimulation` (step-synchronized relation) with `implements_of_isSimulation` — related states have equal `behavior`, via `M.corec_eq_corec`; `isSimulation_graph` / `behavior_coalgHom` — coalgebra morphisms are the functional simulations. |
| [`PolyFun/PFunctor/Dynamical/Refinement.lean`](../../PolyFun/PFunctor/Dynamical/Refinement.lean) | `DynSystem.SafetyRefinement` (existential refinement between `SafetySpec`s over possibly different interfaces, step-matched by a `DirRel`) with `mapRun` and its transport lemmas; `ReverseSafetyRefinement` / `MutualSafetyRefinement` packagings; `SafetyRefinement.ofIsSimulation` embedding `IsSimulation` at `DirRel.sync`. Instantiated by the concurrent refinement layers. |
| [`PolyFun/ITree/Unfold.lean`](../../PolyFun/ITree/Unfold.lean) | `DynSystem.toITree`: unfold a dynamical system into an all-query interaction tree; `M.toITree` embeds behaviour trees. |
| [`PolyFunTest/PFunctor/Dynamical/Examples.lean`](../../PolyFunTest/PFunctor/Dynamical/Examples.lean) | Worked examples / regression tests (counter, parity automaton, mode-dependent `gate`, feedback / stream behaviour, the `univ`-system `toggle`, generic runs, `choiceProd`, behaviour / ITree unfolding). |

### Free monad `FreeM`

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Free/Basic.lean`](../../PolyFun/PFunctor/Free/Basic.lean) | `FreeM P α` (`pure` / `roll`), `lift`, `liftPos`, `bind`, `Monad` and `LawfulMonad` instances, eliminator combinators. |
| [`PolyFun/PFunctor/Free/Path.lean`](../../PolyFun/PFunctor/Free/Path.lean) | `FreeM.Path s` (explicit polynomial direction at every node), `PathAlong`, `output`, `append`, `TelescopeWith` (state-indexed initial algebra). |
| [`PolyFun/PFunctor/Free/Displayed.lean`](../../PolyFun/PFunctor/Free/Displayed.lean) | `FreeM.Displayed D s` (displayed family over a tree), `Displayed.Section` (displayed catamorphism). The substrate behind decorations, paths, and compact observations. |
| [`PolyFun/PFunctor/Free/Displayed/Decoration.lean`](../../PolyFun/PFunctor/Free/Displayed/Decoration.lean) | `Decoration Γ s`: every node carries one `Γ a` and recursively decorates children. |

### Cofree / M-type companion

| File | Purpose |
|------|---------|
| [`PolyFun/PFunctor/Cofree.lean`](../../PolyFun/PFunctor/Cofree.lean) | `CofreeC` (cofree comonad on a `PFunctor`), built from `PFunctor.M` of the `constProd` polynomial. The dual of `FreeM`. |
| [`PolyFun/PFunctor/Trace.lean`](../../PolyFun/PFunctor/Trace.lean) | Polynomial-trace machinery shared between `PFunctor` and downstream layers. |

### Control helpers

`PolyFun/Control/` is logically below `PFunctor/Free` in the import DAG and
provides the reusable monad / comonad / coalgebra plumbing. See
[`PolyFun/Control/`](../../PolyFun/Control/) for the full inventory:
`Coalgebra` (the `Coalg` class: every `DynSystem p` is a `Coalg p.Obj`),
`Comonad/{Basic, Instances}`, `Lawful/Basic`,
`Monad/{Algebra, Equiv, Free, FreeCont, Hom, Iter}`, `Trace`.

## Mental model

- `PFunctor` is a *small* gadget: just `(A : Type, B : A → Type)`. Almost
  every interesting structure in PolyFun is built by combining a few of
  these via `+` / `*` / `⊗` / `Σ` / `Π` / composition, or by taking the
  free monad / cofree comonad / lens / chart of one.
- `FreeM P` is the free monad on `P`. Operationally it is the inductive
  type of well-founded `P`-branching trees with `α`-leaves. It is the
  syntax of "programs" in the signature `P`.
- `CofreeC P` is the cofree comonad on `P`. Coinductively, it is the
  type of infinite, fully-decorated `P`-trees. It is the patterns/matter
  pairing `FreeM ⊣ Cofree` from Spivak-Niu.
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
  builds protocol `Spec`s as `PFunctor.FreeM Spec.basePFunctor PUnit`,
  i.e. `PUnit`-leaved free trees on a particular base polynomial. Most
  of the interaction framework is just a dependent-typed dressing on top
  of `FreeM` plus `Decoration` / `Displayed`.

If a concept appears redundant between layers, the substrate version
(here, in `PFunctor/`) is almost always the load-bearing one. Downstream
layers exist to give protocol-flavored names and ergonomics; the maths
lives in `PFunctor/Free/` and `PFunctor/Cofree.lean`.
