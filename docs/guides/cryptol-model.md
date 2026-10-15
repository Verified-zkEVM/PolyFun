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

The next downstream work is checked typed-AST import and a pinned official
reference-core correspondence, wider language semantics and polymorphic
operational adequacy, syntax-producing specialization/native compilation,
then polymorphic export and semantic round trips. PolyFun should gain only
reusable transport, binding or domain lemmas needed by those slices. A frontend,
Cryptol primitives, reference version policy and cryptographic conformance
certificates belong to VCVio's optional development.
