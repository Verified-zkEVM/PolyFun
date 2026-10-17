# Upstream ownership and ongoing work

PolyFun builds on the definitions in its pinned dependencies. Read
[`lakefile.toml`](../../lakefile.toml), [`lake-manifest.json`](../../lake-manifest.json),
and [`lean-toolchain`](../../lean-toolchain) for the exact versions. A newer
upstream README can describe APIs that the pinned revision does not yet supply.

## Where a contribution belongs

| Project | Existing role | Guidance for PolyFun contributors |
|---|---|---|
| [Lean](https://github.com/leanprover/lean4) | Language, module system, basic effects, weakest-precondition infrastructure | Use core monad laws and the pinned `Std.WP` interfaces through the documented quarantine. |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | `PFunctor`, W/M-types, algebra, order and category theory | Extend existing structures, notation, and typeclasses; use its naming and documentation conventions. |
| [CSLib](https://github.com/leanprover/cslib) | Polynomial and generic free monads, transition systems, temporal and machine foundations | Reuse `PFunctor.FreeM`, `Cslib.FreeM`, relational LTS laws and machine APIs; stage reusable additions in `ToCslib`. |
| [Batteries](https://github.com/leanprover-community/batteries) | Lean utilities and environment linter driver | Use the existing linter integration rather than a second policy implementation. |
| PolyFun | Polynomial interaction, machines, handlers, open composition, generic logic and realizability | Keep applications and cryptographic interpretations separate from the generic APIs. |
| [VCVio](https://github.com/Verified-zkEVM/VCVio) | Oracle computations, probabilistic semantics, cryptographic definitions and proofs | Consume PolyFun's public equations and instantiate its abstract observations and resource predicates. |

The remaining resolved packages support proof automation, widgets, import
graphs, search, and testing. They do not introduce another interaction model.
Their pins are recorded in the manifest; their README files live under
`.lake/packages/` after dependency setup.

## Integration contracts

- **Polynomial constructions:** CSLib's
  `Cslib.Foundations.Data.PFunctor.Basic` owns the monomial `A y^ B` and its
  special cases `C`, `linear`, `selfMonomial`, `purePower` (`y^ B`) and `y`,
  the constants `0` and `1`, `P + Q` (through `PFunctor.add`), `P * Q`
  (through `PFunctor.prod`) and `PFunctor.ext`, together with their simp
  lemmas. `PolyFun/PFunctor/Basic.lean` re-exports that module and adds the
  universe polynomial, the named sum `PFunctor.sum`, indexed sums and
  products, tensor, lifts, exponentials, lenses and charts. The reducibility of
  the shared constructions is CSLib's; the
  [polynomial guide](../guides/pfunctor.md#cslibs-polynomial-constructions)
  describes what it implies for instance search and simp.
- **Free monads:** import the CSLib definitions through the appropriate public
  module. CSLib owns the carrier `PFunctor.FreeM`, its fold `FreeM.foldFreeM`
  with the fold laws (`Free.Fold`), and the W-type equivalence
  `FreeM.equivWOfIsEmpty` with its directions `FreeM.toWOfIsEmpty` and
  `W.toFreeM` (`Free.W`). `ToCslib/Data/PFunctor/Free/` adds
  constructor-spelled equations and loop transport without redeclaring any of
  them, and PolyFun-specific decorations, paths, machines, and handlers remain
  in `PolyFun/PFunctor/`.
- **Co-import:** neither PolyFun nor `ToCslib` redeclares a CSLib name, so
  `import Cslib` elaborates together with `import PolyFun`, `import ToCslib`
  and `import ComplexityBackends`. The ordinary-import canary
  [`CslibCoImport.lean`](../../PolyFunTest/ModuleAPI/CslibCoImport.lean)
  imports each owning CSLib module together with the PolyFun and `ToCslib`
  modules that build on it, so a redeclared name fails the test build without
  building the whole CSLib root.
- **Resumable execution:** `DynComputation.Resumable` retains machine state
  and derives budget composition and handler transport from the existing
  `FreeM.liftM` laws. The pinned CSLib, Mathlib, and Batteries APIs supply no
  residual-state driver for PolyFun's `DynComputation`. Keep this extension
  beside bounded execution; revisit ownership if the returning-machine
  abstraction moves upstream. The IO adapter adds no domain policy.
- **Handled execution:** `HandledDiagram.initial`, `runToken` and `runFIFO`
  wrap PolyFun's routed runtime and retain residuals. Their composition laws
  delegate to that runtime; CSLib's free-monad interpreters do not own
  PolyFun's packet topology.
- **Transition systems:** `Control.LTS.toLts` forgets the polynomial witness
  move. Generic relational simulation and finite-trace results use CSLib;
  dependent response witnesses and delay semantics remain explicit in PolyFun.
  See [bisimulation](../guides/bisimulation.md).
- **Temporal reasoning:** reuse the pinned temporal operators and prove
  application-specific fairness statements over the chosen event/ticket model.
  The ticket-predicate characterizations stay beside `ProcessOver.Ticketed`.
- **Program logic:** ordered algebras and exact support connect to core's
  lattice-generic weakest-precondition framework `Std.WP`, which `vcgen` uses.
  Core's `Std.Do` framework, which `mvcgen` uses, is a distinct interface that
  PolyFun does not instantiate. See [program logic](../guides/program-logic.md).
- **Complexity:** `ComplexityBackends/` holds machine-relative theory and the
  adapters that certify PolyFun step maps with it, one subdirectory per
  backend. Generic PolyFun does not acquire a concrete complexity backend
  transitively through its umbrella.
- **Module APIs:** ordinary-import consumers should use named equations.
  Downstream `import all` is not a substitute for a missing public API.

When updating dependencies, compare the pinned and proposed definitions,
remove superseded local helpers, check ordinary imports, and run the full
[validation workflow](validation.md). An upstream theorem with the same name
is useful only if its universe parameters, hypotheses, and computational
behavior match the consumer.

## Finite case compilation

`ToCslib/Data/Fin/Cases.lean` proves compiler simplifications for core's
`Fin.cases` and Mathlib's `Fin.cons`/`Matrix.vecCons` wrappers. At the pinned
v4.35 release candidate, strict evaluation of the induction-based definition
computes discarded recursive results; nested vector lookup compounds that
work. The replacement selects the underlying natural-number case directly,
with a kernel-checked equality and unchanged logical computation rules.
The wrapper equations matter because imported wrappers can be inlined after
the compiler simplification pass. Remove these staging lemmas when the owning
core and Mathlib definitions acquire equivalent compiled implementations.

## Omega-CPO fixed points

`ToCslib/Order/` extends Mathlib’s omega-CPO API with continuous currying,
least fixed points, admissibility, discrete, lifted, and disjoint-sum orders,
and finite prefix recursion. Order-only results are candidates for Mathlib or
CSLib; remove superseded local instances before upgrading their owning
dependency. The pinned Mathlib has no omega-CPO instance for `WithBot` or for
disjoint sums, and no equality-ordered wrapper; `DiscreteOrder` leaves the
ordinary order on numbers and Booleans intact.

Mathlib already supplies the Kleene chain
`OmegaCompletePartialOrder.fixedPoints.iterateChain`, its facts
`ωSup_iterate_mem_fixedPoint` and `ωSup_iterate_le_prefixedPoint`, and Kleene's
theorem `fixedPoints.lfp_eq_sSup_iterate` for complete lattices. It has no
least-fixed-point operator on a pointed omega-CPO that is not a lattice; `LawfulFix`
asks only for the unfolding equation, and Mathlib instantiates it for `Part`-valued
carriers. `ContinuousHom.approximants` is that chain started at bottom, so
`ContinuousHom.fix` is its supremum (`fix_eq_ωSup_iterateChain`, by `rfl`), and
`map_fix` and `fix_le` specialize the two Mathlib facts. `isLeast_fix`
characterizes `fix` as the least prefixed point. On the omega-CPO structure of a
complete lattice, `fix_eq_lfp` identifies it with `OrderHom.lfp`; carriers with a
separate pointwise instance, such as function types, combine `isLeast_fix` with
`OrderHom.isLeast_lfp_le`. The local additions are fixed-point induction, fusion
through strict maps, and continuity in the recursive body. `fix_induction` takes
the chain-closure hypothesis in unfolded form, so an `Admissible` proof can be
passed directly; `Admissible.fix_induction` states the same principle with the
named predicate. An upstream version belongs beside `fixedPoints.iterateChain`.

## Object, path, and trace interfaces

`FreeP.node`, `FreeP.encode`, and `FreeP.decode` use the owning polynomial
object API: `Obj.mk`, `fst`, `snd`, `rec`, and `ext`. Node projections and
encoding/decoding equations support ordinary imports. Positions of an indexed
sum have the parallel interface `sigma.mk`, `sigma.fst`, `sigma.snd`,
`sigma.rec`, `sigma.ext`, and `sigma.B_mk`. `Handler.sigma`, the sigma lenses
and charts, wiring evaluation, and the sigma displays and displayed handlers
are stated through it, so consumers need no reducibility override on `sigma`
to work with those positions. `FreeP.relabel` delegates
to `PFunctor.map`. Positions of composite polynomials and dependent path
decompositions that are defined as Sigma types retain those types; they are
distinct from the object carrier. The free-handler bridge explicitly selects
`SubstMonoid.Extension`, since a carrier alone does not determine its monad.

Trace observations use Mathlib's free-monoid operations and its `recOn`
eliminator. Cross into lists through `toList`/`ofList`; use the public
position, occurrence, lookup, and partial-map equations in consumers.
Polynomial-specific dependent lookup remains in PolyFun. The
[module API guide](module-api.md#monoid-traces-and-dependent-events) explains
these laws and the dependent-event elaboration boundary.

The ordinary-import regressions for
[objects](../../PolyFunTest/ModuleAPI/FreePolynomial.lean),
[paths](../../PolyFunTest/ModuleAPI/DependentPaths.lean), and
[traces](../../PolyFunTest/ModuleAPI/Traces.lean) exercise independent universes,
empty response fibers, path composition, displayed transport, ordered repeated
events, and filtering with dependent payloads. The replay consumers isolate
the structural boundary used by VCVio; they do not validate probability proofs.

## Remaining abstraction boundaries

Dependent elaboration can distinguish constructor and monadic spellings of
the same free tree during rewriting. This example needs only CSLib's
`Cslib.Foundations.Data.PFunctor.Free` at the current pin:

```lean
example {P : PFunctor} {α : Type}
    (F : PFunctor.FreeM P α → Type) (a : P.A)
    (next : P.B a → PFunctor.FreeM P α)
    (observe : F ((PFunctor.FreeM.lift a).bind next) → Nat)
    (value : F (PFunctor.FreeM.liftBind a next))
    (h : ∀ x, observe x = 0) : observe value = 0 := by
  change F ((PFunctor.FreeM.lift a).bind next) at value
  rw [h]
```

The direct application `exact h value` also works. Aligning the index avoids
an imported reducibility override and preserves upstream simp direction.

The dependent event boundary can be reproduced using only Mathlib's
`Mathlib.Algebra.FreeMonoid.Basic` and
`Mathlib.Data.PFunctor.Univariate.Basic`:

```lean
example {P : PFunctor} (a : P.A) (answer : P.B a)
    (observe : FreeMonoid P.Idx → Nat)
    (h : ∀ event : P.Idx, observe (FreeMonoid.of event) = 0) :
    observe (FreeMonoid.of (α := P.Idx) ⟨a, answer⟩) = 0 := by
  exact h ⟨a, answer⟩
```

Here direct application succeeds where rewriting can reject the reconstructed
Sigma/`Idx` pair at implicit transparency. The retained local `Idx` overrides
in trace and supply name the concrete generator/counting consumers and their
removal conditions. They do not require exposing the free-monoid carrier.

| Area | Next check and acceptance condition |
|---|---|
| Dependent events and request-network transport | Test an owning constructor/eliminator API against the generator reproducer; remove each override only after dependent lookup, supply, and transport consumers compile. |
| Cofree polynomials, displayed constructions, and pattern-runs-on-matter | Follow an object equality and dependent continuation through public object/lens equations; preserve type-level tensor and unit computation. |
| Reactive networks and realizability closure | Minimize actual transport/update consumers, retaining coherent representation and admissible-step data. |
| Core/CSLib dependent automation | Recheck the independent free-tree and event reproducers at a coordinated pin upgrade; treat WP/`vcgen` result-index matching as a separate question. |
| Simp lemmas over concrete polynomial abbreviations | A simp lemma whose left side carries `P.B a` in an implicit argument, as `FreeM.lift a` does, misses a goal in which `P` is a concrete `A y^ B`, `y`, `C`, `linear` or `purePower`, because simp reduces that argument to `B` before it consults its index. PolyFun's generic lift equations mark the argument `no_index`, as CSLib's `foldFreeM_lift` does, and [`ConcreteSimp.lean`](../../PolyFunTest/PFunctor/ConcreteSimp.lean) tests them against `Bool y^ Nat`. CSLib's `FreeM.liftM_lift` and `liftM_lift_bind` still miss; once a CSLib pin marks them `no_index`, add their `Bool y^ Nat` cases to that file. `FreeM.allOutputs_lift` and `FreeM.someOutput_lift` also miss, and `no_index` alone does not repair them: simp unifies their predicate `p : P.B a → Prop` before `FreeM.lift a` determines `P`, so the predicate's type is stuck. Rewrite with them on a concrete interface until a restatement fires under plain `simp` there. |
| CSLib polynomial W/M-types and resumptions | cslib#1088 adds `FreeM.toW` and `FreeM.ofW` to `Free.W`, which PolyFun does not declare, together with `M.dest_inj`, `M.corec_dest`, `W.toM`, `M.toW_toM`, and a `PFunctor.Resumption` API whose sum lists the summands in the opposite order. PolyFun declares the last five in [`M.lean`](../../PolyFun/PFunctor/M.lean), [`M/WellFounded.lean`](../../PolyFun/PFunctor/M/WellFounded.lean), and [`Resumption.lean`](../../PolyFun/PFunctor/Resumption.lean). At the pin that contains the request, adopt or rename each one so the co-import canary still elaborates. |
