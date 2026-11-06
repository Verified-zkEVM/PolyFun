# Reusable language interoperability

PolyFun supplies interfaces for syntax, interpretation, represented data and
execution. A frontend owns its language's types, primitive meanings, demand
rules and connection to the external implementation. Algorithm specifications
and cryptographic interpretations belong to their consumers.

## A checked path through the models

| Boundary | Reusable interface | Frontend obligation |
|---|---|---|
| External source to scoped syntax | `IPFunctor.ScopedSignature`, `ScopedFamily` | Validate binding, types, constraints and the supported fragment; state parser/exporter trust |
| Scoped syntax to meaning | Algebraic folds and semantic substitution; `Control.Domain.Result` for partial carriers | Give primitive and recursion equations, retaining distinctions between failure, divergence and partial values |
| Represented meaning to implementation | `Control.Semantics.CorrespondsOn`, `CertifiedMeaning` | Supply injective input/output encodings and prove agreement on the stated admissible inputs |
| Partial representations to native values | Mathlib `Relator.LiftFun`, `Control.Semantics.RelationalContract` | Cover admissible inputs and prove output left-uniqueness; irrelevant tails need not have unique representations |
| Deterministic execution | `Control.Transition`, `Executes`, `Terminates` | Define states/results and prove preservation or adequacy for the language |
| Execution to existing machines | `Transition.tree`, `toMachine`, `runChunk_toMachine` | Choose observations and preserve any effects or errors encoded by the frontend |
| Machine to resource certificate | `Realizability` and its quantitative interfaces | Supply the admissible backend, representation and cost laws |

The syntax objects and effect interfaces are polynomial constructions; the
semantic and execution boundaries have different proof obligations. Keeping
them separate lets another frontend reuse binding, folds, contract transfer and
resumption without adopting a different language's evaluation strategy.

`CorrespondsOn` works with arbitrary semantic carriers, including carriers with
unrepresented errors or bottom. `DataContract` requires a represented output.
Its equivalence to a native postcondition uses output injectivity and an explicit
admissibility premise. Composition requires the first implementation to establish
the second implementation's domain. These interfaces do not manufacture totality
or erase failures.

`RelationalContract.iff_of_liftFun` handles representation relations. The
embedding-based contract is a special case, and its transfer theorem uses this
same proof. VCVio's Foundation-list view is a concrete consumer: a finite list
observes a length and a stream prefix, while different unused tails represent
the same list. An empty list may even have a bottom stream component. Requiring
an equivalence or a unique semantic representative there would impose the
wrong definedness requirement. No additional correspondence class is needed;
function compatibility is Mathlib's `Relator.LiftFun`.

## Two consumers

[ScopedExecution.lean](../../Examples/Tutorials/ScopedExecution.lean) supplies a
strict evaluator for the arithmetic, let and bounded-loop fragment of the
existing scoped tutorial. Fragment evidence constructs a free program of unit
steps. `compile_correct` relates it to the scoped algebra for every supported
term and environment; `executes` and `execution_correct` connect its transitions
to that meaning. `sumCertificate` demonstrates all-input contract transfer.

VCVio's optional Cryptol development uses the same correspondence and transition
interfaces with lazy partial values, typed machine states and language-specific
errors. Cryptol source schemes, primitives, adequacy, Foundation provenance and
crypto specification transfer remain in VCVio. The two frontends share neither
an opcode vocabulary nor an evaluation strategy.

## Further connections

The next useful extensions are compiler rules with explicit supported-shape
evidence, observation-preserving translations between execution models, and
backend-specific resource certificates. Existing ITree/resumption bridges make
silent-step choices explicit; simulations relate distinct machine states.
Scoped representations can therefore serve as common compiler input while each
target supplies the preservation relation it actually supports.

Syntax size, transition counts, visible query counts and backend execution cost
are separate quantities. A correspondence theorem alone supplies none of the
extra laws needed to identify them. See [computation models](computation-models.md),
[execution](execution.md) and [realizability](realizability.md).

The [cross-repository tracker](https://github.com/Verified-zkEVM/VCVio/issues/879)
records the next substantial workloads for these APIs and their dependencies.
Generic PolyFun work remains fully proved while downstream source/algorithm
obligations are reported at their own boundary.

The axiom scanner's `sorryGraph` report retains direct kernel dependencies,
elaborated proposition text, and internal auxiliary nodes for the `sorryAx`
closure. Consumers can use that report to explain inherited proof obligations.
This does not change PolyFun's policy: `--check` still rejects every admission
and every nonstandard axiom, and its baseline must remain empty.
