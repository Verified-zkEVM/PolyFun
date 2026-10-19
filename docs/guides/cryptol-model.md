# Cryptol model consumer

The Cryptol development lives under `Interop/Cryptol` in
[VCVio](https://github.com/Verified-zkEVM/VCVio), with optional model, translation,
bridge, and test targets in VCVio's root Lake project. PolyFun's default build
and validation do not build it.

PolyFun owns the reusable scoped polynomial syntax, indexed algebra folds,
renaming, substitution, sort reindexing, continuous partial results, tree
interpretations, finite prefix recursion, represented-data correspondence and
deterministic transition adapters. The [interop guide](interop.md) explains the
shared pipeline and its independent strict arithmetic/let/loop consumer. See the
[indexed-polynomial guide](ipfunctor.md#binding-signatures-and-native-ir),
[interaction-tree guide](itree.md), and [upstream ownership](../development/upstream.md).
The downstream project owns Cryptol syntax choices and semantics, extraction,
export, language compatibility tests, Foundation correspondences, and VCVio
probability statements. Both the resolved source and native finite IR consume
PolyFun's scoped syntax directly. Ordered polymorphic syntax uses the
[context-changing binding families](ipfunctor.md#binders-that-change-parameter-contexts),
generic parameter traversals, and continuous heterogeneous environments.
The [independent polymorphic tutorial](../../Examples/Tutorials/ScopedFamily.lean)
exercises these APIs without a language or cryptographic dependency.

## Substitution and semantic transport

`ScopedFamily.Term.map_congr` compares parameter traversals with related states,
including different target scopes and arbitrary context/sort equality witnesses.
It complements traversal composition: a consumer proves constructor and child
coherence, then obtains whole-term identity/composition without implementing
another recursive traversal.

`ScopedDomain.Env.Pointwise` compares values at equal binding positions across
independent sort types. It is stable under context casts, domain reindexing,
fresh bindings and blocks. `fixGroup_pointwise` transports one simultaneous
least fixed point using a strict continuous map; it does not move quantifiers
through recursion or assume that a language's value substitution is strict.
These APIs use the existing Mathlib omega-CPO and PolyFun scoped carriers.

The companion VCVio development discharges the concrete Cryptol binder squares
and proves whole-term parameter identity/composition, parameter/value fusion,
value-substitution composition, and denotation preservation for every current
ordered constructor. Its tests include noninjective type maps, arbitrary
annotations, mixed binders, partial environments and recursive groups.
Language-specific constructor proofs remain downstream.

The downstream importer now checks a closed typed-AST fragment and a candidate
from the official specializer. General source preservation, open whole-module
import and polymorphic operational adequacy remain separate obligations. The
next delivery contract prioritizes complete retained definitions, usable native
interfaces and explicit unfinished proofs. PolyFun should gain reusable binding,
domain, relation or execution laws that remove concrete consumer work. The
frontend, Cryptol primitives, semantic version policy and cryptographic
conformance certificates remain in VCVio's optional development.

## Whole-module consumer contract

The coordinated Foundation-import work is tracked in
[the unified roadmap (#879)](https://github.com/Verified-zkEVM/VCVio/issues/879).
Its generic workstreams are
[P1: binding](https://github.com/Verified-zkEVM/VCVio/issues/879#p1),
[P2: semantic relations](https://github.com/Verified-zkEVM/VCVio/issues/879#p2),
[P3: execution](https://github.com/Verified-zkEVM/VCVio/issues/879#p3) and
[P4: public consumers](https://github.com/Verified-zkEVM/VCVio/issues/879#p4).
The wider computation-model audit
remains in [#309](https://github.com/Verified-zkEVM/PolyFun/issues/309).
These are planned extensions and acceptance conditions, not additional existing
API claims. The downstream [delivery contract](https://github.com/Verified-zkEVM/VCVio/blob/feat/cryptol-foundation-bridge/Interop/Cryptol/docs/tooling.md#coordinated-development-contract)
specifies language coverage, proof obligations and agent handoffs.

PolyFun's role is to make each useful computational viewpoint compositional and
usable. VCVio chooses one canonical source representation and a narrow consumer
interface. It should not expose a collection of interchangeable source ASTs or
contract structures merely because PolyFun can represent them.

| Generic work | Downstream pressure | Required evidence |
|---|---|---|
| Mixed binding and environments (P1) | Open modules, class-constrained schemas, global references and recursive polymorphic groups | Shared structural/substitution/fold laws remove repeated traversal proofs; an independent language uses the same APIs. |
| Lazy/logical relations (P2) | Suspended aggregates, higher-order utilities, stream observations and represented native values | Compositional proofs retain bottom/error/definedness distinctions and the hypotheses for fixed-point reasoning. |
| Observable execution (P3) | Imported closure execution, incremental CRC/SHA and continuing services | Simulations preserve the named observations and residual state; the same algorithm has a meaningful chunk or service theorem. |
| Independent API consumption (P4) | Whole-module proofs through ordinary imports | Public equations avoid manual casts/private unfolding; proof duplication and performance are measured on substantial workflows. |

Audit the existing `ScopedFamily`, `FoldAlgebra`, positional environments,
`DomainResult`, `ContinuousHom`, `CorrespondsOn`, `CertifiedMeaning`,
`DataContract`, `Control.Transition`, ITree and machine APIs before adding
anything. Use core/CSLib/Mathlib data, morphisms, relations and equivalences
where adequate. No new generic computation superclass, CPO class, native
contract hierarchy or parallel traversal is planned.

Open Cryptol class constraints and their dictionary/evidence meaning belong
downstream. A generic environment may be parameterized over such evidence but
must not know Cryptol primitives, module-loader rules or evaluation strategy.
Likewise, a generic logical-relation combinator must state admissibility,
continuity and strictness assumptions when fixed-point transport needs them.
Do not infer totality from finite inputs or equate a partial aggregate with
an outer failure.

The same imported workloads should exercise scoped syntax, domains, transitions,
ITrees and returning machines for different reasons. Resumptions need the
appropriate productivity bridge; arbitrary silent divergence cannot be erased.
Indexed coinductive models and continuations should be audited against actual
state-changing interfaces/compiler needs, then reused, deferred or consolidated
with a recorded reason. They need not all become mandatory stages in Cryptol's
pipeline. A weak behavior relation alone proves no timing, leakage or backend
cost result.

The first substantial language consumers are complete utility modules
(List/Sort/Imperative/Enum and upstream reference definitions), then parameterized
CRC and full SHA2. Pinned Cryptol List is a lazy stream/length representation,
so its finite native view is a relation with validity conditions, not a
recursive-nominal-type requirement. Imported recursive groups retain polymorphic
instances rather than requiring finite monomorphization.

Public APIs should support a separate consumer proving correspondence over
named native data without `import all`, carrier unfolding or a custom set of
cast lemmas. Every new abstraction should show a removed repeated proof pattern
or an unlocked theorem, preferably in both Cryptol and an independent language.
Record generated term size, elaboration/runtime, manual casts and repeated
constructor proofs alongside ordinary correctness regressions.

Generic implementations remain fully proved and pass PolyFun's zero-debt
validation. Downstream exploration may retain named unfinished source/algorithm
proofs in its own explicitly reported boundary; this does not justify admitting
generic laws. Structural import, semantic correspondence, native totality and
backend compatibility are separate evidence, even when a client has a
well-typed source term.

Work can continue on #290 with explicit downstream overrides and immutable
published pins. Reuse #289 for independent applications and #308 for actual
service composition. The unified issue owns assignments and status; these guides
own the durable contracts. Extract an upstream prerequisite when its API is
independently useful and validated, rather than merging a broad draft solely
to unblock one importer experiment.
