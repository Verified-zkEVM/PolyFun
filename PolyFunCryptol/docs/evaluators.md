# Cryptol semantics, interoperability targets, and upstream discrepancies

The recommended anchor is Cryptol's documented lazy language semantics, starting
from its pinned executable reference account. Compatibility with a particular
normal evaluator or SAW backend is a separate claim. Neither a known interpreter
bug nor a majority vote among backends should silently determine language meaning.
Unsettled cases need a documented choice and a versioned discrepancy entry.

The existing Lean model follows the reference account for its supported fragment.
Its internal preservation theorems do not verify the Haskell implementation or
the official frontend. The survey below changes the proposed development
priorities, not the definitions or existing theorem statements.

## What the reference implementation means

Several different artifacts are easily confused:

| Artifact | Role | What it does not establish |
|---|---|---|
| `Cryptol.Eval.Reference`, invoked by `:eval` | Literate Haskell definition of evaluation on explicitly typed Cryptol expressions | Mechanized soundness of Haskell, the frontend, or every primitive |
| `docs/Semantics.pdf` | Document generated from that same `Reference.lhs` source | An independent formal standard agreeing with every implementation |
| `Cryptol::Reference` | Cryptol definitions of selected primitives used as backend fallbacks | A separate evaluator or a complete specification of all primitives |
| Normal concrete evaluator | Efficient execution, with thunks, sharing and packed words | Unconditional agreement with intended lazy semantics |
| Foundation algorithms | Executable algorithm specifications written in Cryptol | Correctness against an external standard or a cryptographic security theorem |
| `cryptol-semantics` and SAW/Rocq | Distinct mechanization/translation efforts | One complete, current, mutually verified semantic stack |

At pinned Cryptol `61dd17b`, [Reference.lhs](https://github.com/GaloisInc/cryptol/blob/61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b/src/Cryptol/Eval/Reference.lhs)
describes a domain-theoretic semantics. A value type has a domain `M(t)`, and
expressions denote computations `E(M(t))`. `E` adds divergence and explicit errors.
Aggregates contain suspended computations; functions are continuous maps from
computations to computations. Recursive groups use least fixed points, and
polymorphic meanings range over valid type/numeric instantiations. This directly
motivates the present `DomainResult` model. It is more than a collection of test
vectors, but its executable Haskell presentation is not itself a proof.

The document explicitly excludes type inference, type functions and constraints
from its scope. The [build rule](https://github.com/GaloisInc/cryptol/blob/61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b/docs/Makefile)
generates `Semantics.pdf` from this source. Older academic accounts must also be
dated: errors only at base types and the resulting special behavior of empty
types were revised in [#619](https://github.com/GaloisInc/cryptol/issues/619),
[#866](https://github.com/GaloisInc/cryptol/pull/866) and
[#1136](https://github.com/GaloisInc/cryptol/pull/1136).

The reference account has limitations of its own. For example,
[`Cryptol::Reference`](https://github.com/GaloisInc/cryptol/blob/61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b/lib/Cryptol/Reference.cry)
defines `foldl'` using `foldl`, despite the former's intended strict accumulator;
reference `random` reports an unimplemented error. Not every panic in
`Reference.lhs` is a missing well-typed language feature: many reject violated
internal invariants. These distinctions need inspection, not automatic
translation into Lean errors.

## Reproduced versions

The [audit report](../artifacts/evaluator-audit.json) records 152 observations:
both evaluator modes at Cryptol 3.6.0
(`61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b`) and a separately built upstream
revision `51405420cb90cf9959ca4349eea0ae8b77487855`. Foundation remains pinned at
`7d0528bd998682788f4e23661f2829298f9e47db`.

The matrix checks signed integer division/remainder and zero divisors, lazy
function and aggregate demand, partial-word comparison, updates, shifts,
empty and infinite sequences, comprehensions, folds, productive recursion and
Foundation theta. Expected disagreements are distinct outcomes. An external
timeout fails validation and is never classified as semantic divergence.

Run `test_evaluators.py --cryptol … --upstream-cryptol … --foundation … --report …`,
or set `CRYPTOL_UPSTREAM_BINARY` alongside the usual external-validation inputs.
The validation driver compares the newly generated report to the committed one.
Revision checks reject an unrelated binary; a changed evaluator outcome requires
an explicit audit update.

## Known upstream work

| Observation | Upstream evidence | Disposition |
|---|---|---|
| Negative `Integer` division and remainder differ between normal and reference modes | [Cryptol #2060](https://github.com/GaloisInc/cryptol/issues/2060), open; [#2061 closing discussion](https://github.com/GaloisInc/cryptol/pull/2061#issuecomment-4670449512) | Exact known issue. The proposed reference change was closed unmerged; the discussion favors moving other backends to `quot/rem`. Both audited binaries still disagree. |
| Concrete/symbolic integer rounding has changed before | [#662](https://github.com/GaloisInc/cryptol/issues/662) | Historical context, not evidence that the current mismatch is fixed. |
| Partial packed-word comparison and aggregate demand differ | [#408](https://github.com/GaloisInc/cryptol/issues/408), [#406](https://github.com/GaloisInc/cryptol/issues/406), [#1925](https://github.com/GaloisInc/cryptol/issues/1925) | Related laziness/strictness work. The exact checked observations still differ; these links do not establish that each example has a matching open issue. |
| Negative update index is ignored by reference evaluation and rejected by normal evaluation | [#415](https://github.com/GaloisInc/cryptol/issues/415) | Related out-of-bounds update discussion, not an exact duplicate claim. Keep the regression and seek upstream classification before opening a new issue. |
| Error and demand behavior | [#619](https://github.com/GaloisInc/cryptol/issues/619), [#866](https://github.com/GaloisInc/cryptol/issues/866), [#1136](https://github.com/GaloisInc/cryptol/issues/1136) | Existing design history. Preserve value/error/bottom distinctions and test individual observations. |

The audit reviewed the issue tracker and the closing discussion, rather than
inferring intended semantics solely from one backend's code. This is a versioned
engineering decision; it is not a proof of the Haskell implementation or a claim
that every difference has an upstream resolution.

## Foundation theta

The original `StepMappings.cry` uses `(x-1)%5`. At `x=0`, reference remainder
produces `-1`; forcing that lane fails. Production remainder produces `4` and the
same zero-state observation succeeds. This is an application-level consequence
of #2060, not a newly discovered integer arithmetic bug.

The audit constructs a separate temporary module replacing this one expression
with `(x+4)%5`. The original checkout and imported artifacts are unchanged.
Both evaluator modes accept the portable variant at widths 1, 8 and 64.
`KeccakCodec.theta_predecessor` proves the index identity for every `Fin 5`;
`theta_predecessor_range` proves its bounds. These component facts and probes do
not claim full Keccak correspondence or validate a change to upstream Foundation.

A useful upstream follow-up is to add this Foundation consequence to #2060's
discussion and propose the portable indexing expression separately to Foundation.
No upstream issue, comment or patch is published by this development.

## Survey scope and issue families

Surveyed on 2026-10-19: the pinned Cryptol sources and Foundation corpus; all
19 issue listings under Cryptol's `semantics` label; 174 open/closed issue matches
for `lazy OR strict OR semantics OR reference OR soundness OR unsound`; relevant
issue bodies, closing discussions and linked PRs; the Coq semantics project's
tour and eight open issues; current SAW/Rocq documentation and relevant SAW
issues. This is a systematic survey of relevant families, not a claim that every
issue in every repository was read or that an issue's closure proves a fix is
present in our pinned executable. The existing 152-observation audit was not
rerun or extended for this research-only review.

| Family | Evidence and status at survey time | Consequence for this development |
|---|---|---|
| Completeness of formalization | [Cryptol #652](https://github.com/GaloisInc/cryptol/issues/652) remains open; it consolidates old operational, denotational and typing formalization tickets. [#44](https://github.com/GaloisInc/cryptol/issues/44) remains open for interpreter verification. | Do not describe a complete, mechanized upstream semantics as available to import. Internal Lean proofs and external correspondence are different obligations. |
| Integer arithmetic | [#2060's latest discussion](https://github.com/GaloisInc/cryptol/issues/2060#issuecomment-4670587348) favors changing concrete/symbolic backends and SAW to truncation toward zero, preserving reference behavior. [#662](https://github.com/GaloisInc/cryptol/issues/662) and [SAW #2415](https://github.com/GaloisInc/saw-script/issues/2415) document earlier rounding disagreements. | Total inputs do not eliminate backend differences. Keep explicit rounding contracts and the original Foundation source. |
| Comparisons and packed sequences | [#398's final conclusion](https://github.com/GaloisInc/cryptol/issues/398#issuecomment-770077142) chooses lazy comparisons; [#1925](https://github.com/GaloisInc/cryptol/issues/1925), closed, treats excessive normal-evaluator strictness as a bug. [#408](https://github.com/GaloisInc/cryptol/issues/408) concerns packed-bit demand. | Do not copy packed-word strictness into canonical source meaning simply because it is efficient. A native word view needs a representation/definedness theorem. |
| Error domains and updates | [#619](https://github.com/GaloisInc/cryptol/issues/619), [#422](https://github.com/GaloisInc/cryptol/issues/422) and [#419](https://github.com/GaloisInc/cryptol/issues/419) concern revised outer errors; [#1360](https://github.com/GaloisInc/cryptol/issues/1360) remains open about update demand. [#415](https://github.com/GaloisInc/cryptol/issues/415) identifies reference out-of-bounds behavior as needing correction. | A reference implementation can have bugs too. Distinguish an erroneous aggregate from an aggregate containing erroneous fields, and classify each update rule. |
| Runtime lifecycle versus meaning | [#1030](https://github.com/GaloisInc/cryptol/issues/1030) concerns interrupted thunks subsequently reported as loops. | A timeout or interrupted process is not a semantic divergence proof. Runtime compatibility need not reproduce every REPL lifecycle detail. |
| Reference primitive coverage | [#922](https://github.com/GaloisInc/cryptol/issues/922) and [#1905](https://github.com/GaloisInc/cryptol/issues/1905) remain open; [#2070](https://github.com/GaloisInc/cryptol/issues/2070), closed, concerns loading the fallback module. | Resolve official fallback definitions through the loader and retain their dependency graph, instead of rebuilding every algorithmic primitive in Lean. |
| Floating-point and modular operations | Closed [Cryptol #2044](https://github.com/GaloisInc/cryptol/issues/2044) reports a rounding bug shared by concrete and reference evaluators; open [SAW #1912](https://github.com/GaloisInc/saw-script/issues/1912) tracks missing modular field operations. | Backend agreement is not a specification. Separate base-type support from specific primitive semantics and implementation support. |
| SAW recursion and coercions | Open [#2088](https://github.com/GaloisInc/saw-script/issues/2088), [#2089](https://github.com/GaloisInc/saw-script/issues/2089), [#3205](https://github.com/GaloisInc/saw-script/issues/3205); [#1241](https://github.com/GaloisInc/saw-script/issues/1241) closed as superseded. | Reusing SAW does not remove recursion or proof obligations. Do not import an unrestricted fixed-point axiom into Lean; represent partial recursion in the object semantics. Track solver-justified type equalities explicitly. |
| Symbolic errors and safety | Open [SAW #269](https://github.com/GaloisInc/saw-script/issues/269) records historical inconsistencies concerning undefined/error terms. Its examples are historical reports, not freshly reproduced failures of current SAW. | A solver result is evidence for its encoded proposition and assumptions, not automatically error-sensitive source equivalence. |
| Foreign code | [Cryptol #1554](https://github.com/GaloisInc/cryptol/issues/1554), closed, explains the expectation of pure foreign functions. | Import a Cryptol fallback where supplied; otherwise expose an explicit implementation parameter/contract. Keep stateful external behavior and probabilistic sampling in the VCVio handler layer. |

The normal/reference split therefore has no one-line resolution. Some
differences are implementation bugs, some are deliberate reference abstractions,
some reflect revised language design, and some remain unresolved. Versioned
language equations plus backend-specific obligations are a better interface than
either an unconditional normal/reference equality theorem or a new configurable
language for every backend.

## Literature and implementation ancestry

The relevant literature concerns three separate tasks: giving a language meaning,
transporting definitions into a prover, and making those definitions usable for
cryptographic reasoning. An algorithm-equivalence paper is not evidence of a
complete language formalization.

| Work | What it contributes | Lesson for VCVio / PolyFun |
|---|---|---|
| Pike, Shields, Matthews, [A Verifying Core for a Cryptographic Language Compiler](https://leepike.github.io/pub_pages/acl2.html), ACL2 2006 | Per-compilation proofs for core transformations of micro-Cryptol, including stream termination arguments; demonstrated on TEA, RC6 and AES. Its verified boundary begins after higher-order constructs are eliminated. | Translation validation and stream-to-executable conversion have direct Cryptol ancestry. Preserve the exact boundary of a claim. |
| Erkok and Matthews, [Pragmatic Equivalence and Safety Checking in Cryptol](https://doi.org/10.1145/1481848.1481860), PLPV 2009 | Automated equivalence/safety checking for a tractable subset and an Isabelle/HOL route for manual proofs. | Import, safety, and equivalence need distinct success criteria. Full automated verification of every imported definition is not the coverage target. |
| Dockins et al., [Constructing Semantic Models of Programs with the Software Analysis Workbench](https://saw.galois.com/files/saw-vstte-final.pdf), VSTTE 2016 | Shared semantic terms and symbolic execution support implementation/specification comparison. | Reuse existing frontend and transformation tooling; preserve sharing instead of repeatedly expanding globals. |
| Mullen's [Cryptol Coq semantics tour](https://github.com/GaloisInc/cryptol-semantics/blob/master/TOUR.md), 2017 | Lazy and eager relations, external values for specifications, HMAC/OTP connections to FCF, and unfinished SHA256 work. The tour calls eager-to-lazy correspondence an attempted proof and describes incomplete coverage. | Direct Cryptol-to-game-proof ancestry already exists. A convenient proof view should be connected by a theorem, rather than becoming a second handwritten algorithm. |
| Current [SAW/Rocq extraction](https://github.com/GaloisInc/saw-script/blob/master/doc/saw-user-manual/extraction-to-rocq.md) | Whole-module and transitive-dependency export, primitive parameters, generated support libraries. Documents general-recursion rejection, coercion proof difficulties, and an error axiom restricted to inhabited types. | This is a serious reuse candidate and useful design precedent, but routing through it does not by itself solve full lazy import into Lean. |
| Allais et al., [A Type and Scope Safe Universe of Syntaxes with Binding](https://arxiv.org/abs/2001.11001), ICFP/JFP | Generic binding-aware traversals and their proofs. | PolyFun's scoped polynomial family should remove repeated binding proofs across open types, recursive groups and import transformations. Merely presenting another AST as a polynomial is insufficient. |
| Xia et al., [Interaction Trees](https://arxiv.org/abs/1906.00046), POPL 2020 | Recursive, effectful behavior with handlers and weak bisimulation; executable interpreters and termination-sensitive compiler correctness. | Use ITrees where unbounded execution or handler composition needs them. Lazy closures/thunks still require language-specific modeling. |
| Ringer et al., [Proof Repair across Type Equivalences](https://arxiv.org/abs/2010.00774), PLDI 2021, with the [Galois case study](https://www.galois.com/articles/proof-repair-and-code-generation) | Transports programs/proofs between generated and human-facing representations, including a Cryptol/SAW consumer. The case study identifies lost record labels and manual correspondence work as major usability problems. | Generate named native views and transport facts as part of import; do not make every consumer reconstruct records and bridges. |
| Launchbury's lazy semantics and Breitner's [mechanized correction](https://arxiv.org/abs/1405.3099), 2014 | Heap-based sharing can be related to denotational meaning, but the correctness proof requires care. | A sharing machine is justified by actual execution costs. Sharing preservation and extensional correctness are different obligations. |

The [AWS-LC verification repository](https://github.com/awslabs/aws-lc-verification)
also demonstrates using Cryptol specifications with SAW and Coq property proofs;
its README distinguishes that maintained work from newer HOL Light/CBMC efforts.
CryptHOL and EasyCrypt are relevant ancestors for the downstream game-based
proofs, while Cryptol/FCF and SAW/Rocq are closer ancestors for this importer.

Potential differentiation is the combination of broad current Cryptol import,
sound partial recursion, usable native Lean views, generic polynomial machinery,
and direct VCVio replacement theorems. Neither translation validation nor linking
Cryptol specifications to cryptographic proofs is new. No novelty claim about
complete verified interop is justified by the present draft.

## Comparison contracts and usable imports

Use one versioned source meaning. The initial definition can follow the literate
reference account, with each known exception explicitly resolved or left as an
open obligation. A backend bridge states its actual fragment and preconditions.
Do not define source meaning by taking whichever backend returns a convenient
answer. In particular, the Keccak remainder mismatch cannot be repaired by a
proof of a false equality.

For a consumer with an ordinary data function `impl`, the useful theorem is of
the following form (schematic, reusing the current correspondence API):

```text
forall x, pre x ->
  denote imported (encode x) = successful (encode (impl x))
```

It asserts termination and the represented output, rather than vacuous partial
correctness when the source diverges. For streams, ask for the requested finite
observations and productivity; for higher-order values, use a logical relation
on represented arguments. Equality of all partial functions is a stronger claim
than many consumers need. Conversely, total external inputs alone do not imply
that strict and lazy backends agree: a program can build partial intermediates,
and negative integer division disagrees even without partial values.

Function equality suffices to replace deterministic components in a game once
the input representation and preconditions are established. Preserving execution
cost, leakage, state, or probabilistic behavior requires the corresponding
observation as well. A pure source algorithm should not acquire an oracle effect
merely because it was imported; VCVio supplies the surrounding randomness and
services. In particular, Cryptol's seeded `random` is not a claim about a true
random sampler.

The practical target is broad import with actual retained bodies and a useful
API. Keep separate counts for preserved definitions, available semantics,
ordinary native interfaces, and proved correspondences; the
[Foundation status](compatibility.md) reports the first of these per module
instance. Use parameters/contracts for unspecified foreign or primitive
implementations. Never handle an unsupported case by silently returning zero,
bottom, or a language error. This library admits no proofs: the zero-debt axiom
gate covers it, and an unfinished correspondence stays an explicit hypothesis of
the theorem that needs it.
