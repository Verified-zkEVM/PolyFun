# Cryptol model consumer

The Cryptol development lives under `Interop/Cryptol` in
[VCVio](https://github.com/Verified-zkEVM/VCVio), with optional model, translation,
bridge, and test targets in VCVio's root Lake project. PolyFun's default build
and validation do not build it.

PolyFun owns the reusable scoped polynomial syntax, indexed algebra folds,
renaming, substitution, sort reindexing, continuous partial results, tree
interpretations, and finite prefix recursion. See the
[indexed-polynomial guide](ipfunctor.md#binding-signatures-and-native-ir),
[interaction-tree guide](itree.md), and [upstream ownership](../development/upstream.md).
The downstream project owns Cryptol syntax choices and semantics, extraction,
export, language compatibility tests, Foundation correspondences, and VCVio
probability statements. Both the resolved source and native finite IR consume
PolyFun's scoped syntax directly.
