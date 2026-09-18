# Upstream ownership and ongoing work

PolyFun builds on the definitions in its pinned dependencies. Read
[`lakefile.toml`](../../lakefile.toml), [`lake-manifest.json`](../../lake-manifest.json),
and [`lean-toolchain`](../../lean-toolchain) for the exact versions. A newer
upstream README can describe APIs that the pinned revision does not yet supply.

## Where a contribution belongs

| Project | Existing role | Guidance for PolyFun contributors |
|---|---|---|
| [Lean](https://github.com/leanprover/lean4) | Language, module system, basic effects, weakest-precondition infrastructure | Use core monad laws and the pinned `Std.Internal.Do` interfaces through the documented quarantine. |
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

- **Free monads:** import the CSLib definitions through the appropriate public
  module. `ToCslib/Data/PFunctor/Free/` adds laws and folds without redefining
  the carrier. PolyFun-specific decorations, paths, machines, and handlers
  remain in `PolyFun/PFunctor/`.
- **Resumable execution:** `DynComputation.Resumable` retains machine state
  and derives budget composition and handler transport from the existing
  `FreeM.liftM` laws. The pinned CSLib, Mathlib, and Batteries APIs supply no
  residual-state driver for PolyFun's `DynComputation`. Keep this extension
  beside bounded execution; revisit ownership if the returning-machine
  abstraction moves upstream. The IO adapter adds no domain policy.
- **Transition systems:** `Control.LTS.toLts` forgets the polynomial witness
  move. Generic relational simulation and finite-trace results use CSLib;
  dependent response witnesses and delay semantics remain explicit in PolyFun.
  See [bisimulation](../guides/bisimulation.md).
- **Temporal reasoning:** reuse the pinned temporal operators and prove
  application-specific fairness statements over the chosen event/ticket model.
- **Program logic:** ordered algebras and exact support connect to core's
  lattice-generic WP stack. `Std.Do` and `Std.Internal.Do` denote distinct
  interfaces in this pin; see [program logic](../guides/program-logic.md).
- **Complexity:** `ToCslib/Computability/` contains machine-relative theory;
  `PolyFunCslib` supplies optional adapters. Generic PolyFun does not acquire
  a concrete complexity backend transitively through its umbrella.
- **Module APIs:** ordinary-import consumers should use named equations.
  Downstream `import all` is not a substitute for a missing public API.

When updating dependencies, compare the pinned and proposed definitions,
remove superseded local helpers, check ordinary imports, and run the full
[validation workflow](validation.md). An upstream theorem with the same name
is useful only if its universe parameters, hypotheses, and computational
behavior match the consumer.

## Object, path, and trace interfaces

`FreeP.node`, `FreeP.encode`, and `FreeP.decode` use the owning polynomial
object API: `Obj.mk`, `fst`, `snd`, `rec`, and `ext`. Node projections and
encoding/decoding equations support ordinary imports. `FreeP.relabel` delegates
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
