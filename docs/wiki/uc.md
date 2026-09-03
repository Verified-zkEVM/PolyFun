# UC Semantic Contract

This page is the traceability ledger for PolyFun's structural UC layer. Lean
source remains authoritative. The external comparison target is Farshim,
Karvonen, Knispel, Kohlweiss, and Tyagi, *UC, Categorically: Rigorous
Diagrammatic Proofs* (ePrint 2026/1605; arXiv:2608.04521).

## Scope And Dependency Boundary

PolyFun owns typed boundaries, open systems, structural composition,
contextual equivalence, corruption-event vocabularies, and classes of allowed
systems. It does not define probability, distinguishing advantage,
negligibility, polynomial time, or cryptographic security games. Those are
VCVio instantiations.

The current comparison target is the paper's static/simple UC fragment.
Dynamic party or session creation, adaptive topology, and a full translation
to Canetti ITMs are not claimed by the present layer.

## Three Relations That Must Remain Distinct

1. `OpenProcessActivationEquiv` compares coarse activation structure. It
   hides internal scheduler steps and forgets packet/action identity and
   sampler effects.
2. Boundary or execution equivalence preserves whatever a chosen admissible
   observer exposes. A downstream semantics must prove its own invariance
   under scheduler reassociation and structural factorization.
3. Asymptotic computational indistinguishability relates security-parameter
   families when their distinguishing distance is negligible.

There is no general implication from (1) to (2), or from (2) to a particular
computational execution, without a named adequacy theorem. In particular,
the activation-equivalence factorization theorems in
`OpenProcessFactorization.lean` are not UC security observations.

## Paper-To-Code Ledger

| Paper surface | PolyFun surface | Status |
| --- | --- | --- |
| symmetric monoidal category `C` of interactive systems | `OpenTheory`, with `par`, `wire`, and a granular lawfulness ladder | Candidate model; the free syntax models satisfy the strict laws, while `openTheory` is only `IsLawful` |
| backdoor category `C_bd` | adversarial ports can be represented by ordinary typed boundary components | Representation strategy only; no equivalence with the paper's backdoor construction or quotient is proved |
| nested `D_real ⊆ D_bd` | ordered `SubTheory` values | Structural carrier plus `realizableSubTheory` / `generatedRealizableSubTheory`; corruption and concrete efficiency still require explicit instances |
| corruption restriction defining `D_real` | `CorruptionModel`, `MomentaryCorruption` | Vocabulary only; no bridge to `SubTheory.mem` |
| resources/states | open objects closed against contexts | Conceptual correspondence; no translation theorem to the paper's state category |
| Definition III.3 equivalence closed by composition | `Observation` plus `RespectsPlugComm` and `RespectsFactorization` | Structural interface implemented; in-repo constructors are equality, coarse activation equivalence, and conditional sampled-path equivalence. A packet/action-aware or execution-distribution security observation remains open |
| Definition III.4 secure emulation | `UCSecure`, `UCSecureWithin`, `SecurelyEmulates`, `SecurelyEmulatesWithin` | Context-transformer formulation implemented; no equivalence with the paper's resource/backdoor category or structural simulator morphisms is proved. `Emulates` is the stronger symmetric special case with the identity transformer |
| Theorems III.11--III.12 composition | `Emulates{,Within}.{par,wire,plug}_compose` | Composition is proved only for the stronger symmetric `Emulates` relation. Transporting an existential simulator needs a structural simulator representation and remains open |
| Theorem III.7 and Lemma IV.3 dummy/mux | no generic dummy/mux theorem | Open. Cancelling a strict identity wire is only a compact-closed equality and is not dummy-adversary completeness; a concrete mux/demux and structural secure-emulation layer are still missing |
| Theorem III.14 global subroutines | `OpenTheory.withGlobal`, `SecurelyEmulatesWithGlobal`, `EmulatesWithGlobal{,Within}` | The definition-level context-transformer counterpart is present. Outer composition is proved only for the stronger symmetric `EmulatesWithGlobal` premise, so the secure UCGS theorem remains open |
| Section IV-C efficient networks | `OpenProcess.StructuralBoundary`, `IsRealizabilityClosed` (four lens certificates), and realizability sub-theories | Structural bridge implemented with composite closure derived generically through the product-state combinator; concrete PPT certificates and network-collapse theorems remain open |
| Theorem IV.6 ITM translation | generic `Party`; no identity frontend | Open; identities are a translation surface, not part of core `OpenTheory` semantics, so no `(sid, pid)` addressing is built in |
| Appendix A emulation preorder and Grothendieck SMC | `SecurelyEmulates`, `securelyEmulatesPreorder`, `SecurelyEmulatesWithin` | A preorder is proved for PolyFun's context-transformer judgment, not the paper's resource preorder. Structural simulator morphisms, `par`/`wire` monotonicity, the resource translation, and Grothendieck packaging remain open |

`Leakage` is deliberately absent from the `C_bd` row: snapshot leakage and an
explicit adversarial output interface are not interchangeable constructions.

## Family Construction

`OpenTheory.pi` packages `T : ι → OpenTheory` pointwise. It lets a downstream
cryptographic development put one equivalence relation on closed-system
families while keeping the index semantically opaque in PolyFun. Every tier of
the strict lawfulness hierarchy lifts pointwise. `SubTheory.pi` lifts
pointwise membership, but polynomial-time membership will normally be a
custom family-level predicate because one witness and one bound must control
all security parameters.

## Long-Term Behavior Carrier

The family construction does not choose between process presentations and an
extensional behavior carrier. VCVio's long-term design proposes mapping open
processes into cofree behavior and defining a lawful `OpenTheory` there, so
coherence is proved once by finality instead of carried as activation
equivalences through every client. `OpenTheory.pi`, `Observation`, and
`EmulatesWithin` are intentionally parametric in that choice: the same
asymptotic observation bridge should consume the behavior theory when it
exists.

This is not a license to identify activation equivalence with distributional
equivalence. The behavior map needs a named adequacy theorem into VCVio's
evaluation semantics, and sampling-order transformations that preserve
distributions may still be coarser than equality of cofree behaviors.

## Equation Surfaces Across The VCVio Seam

Cross-repository proofs should end in named structural or semantic laws. If a
chain of rewrites still needs a final `rfl`, reduction is supplying part of the
contract without naming it. Add the missing equation to the layer that owns
the representation, then consume that equation downstream. Reducer-stable
constructors explicitly documented as such are the exception.

This matters especially for bundled monad instances, dependent function
updates, pointwise theory families, and the passage from a closed structural
system to its observed distribution. The contract should survive changes in
module exposure and instance elaboration without asking VCVio to unfold
PolyFun internals.

## Instantiation Gates

The process model supports a computational UC claim only after all of the
following have named proofs. The scheduler obstruction and the conditional
structural implications are now named PolyFun lemmas over the abstract
relation family `MonadRelFamily`
(`OpenProcessSamplerEquiv`, `OpenProcessSamplerFactorization`,
`SamplerObservation`); what remains downstream per gate is stated explicitly:

1. **Scheduler transport.** Reassociation does *not* preserve per-step
   scheduling distributions (the source and factored composites select
   `(first, second, context)` with genuinely different coin encodings —
   `sourceSchedule` vs `leftSchedule`/`rightSchedule`), so the sampler-aware
   coherence laws `openTheory_plug_{comm,par_left,par_right,wire_left,
   wire_right}_sampler_equiv` are **conditional** on the transport facts
   `R.rel (sourceDraw σ) (leftDraw σ)`, `R.rel (sourceDraw σ) (rightDraw σ)`,
   and `R`-fairness `R.rel σ (schedulerFlip <$> σ)`. Downstream either proves
   these for its relation family or carries them as standing hypotheses;
   `MonadRelFamily.top` discharges them trivially at the cost of forgetting
   sampler effects. `MonadRelFamily.eq` does not generally discharge them;
   even a deterministic identity-monad scheduler cannot satisfy both
   reassociation facts. Equality of distributional denotations therefore
   needs redesigned scheduler semantics or a deliberately coarser relation.
   `PNat` frontier masses, `BinaryScheduler.IsFlat`, and `scheduledOpenTheory`
   provide the generic redesign boundary: compositions carry the total mass of
   their atomic frontier, binary nodes receive both subtree masses, and a
   downstream scheduler proves that all hierarchical three-way draws denote
   one flat choice. Probability and the concrete proportional scheduler remain
   VCVio responsibilities. `samplePath_interleave_assoc_left` and
   `samplePath_interleave_assoc_right` lift the resulting coherence law through
   arbitrary component samplers along the existing structural path
   reassociations.
2. **Initial-state correspondence.** The totality fields of
   `OpenProcessSamplerEquiv` expose the regrouping bijection on states, so
   corresponding initial states are chosen definitionally.
3. **Observer adequacy.** The `hInv` premise of
   `Observation.respectsFactorization_of_samplerInvariant`: the downstream
   observation must be invariant under sampler equivalence at its relation
   family. This is the downstream adequacy theorem and is not provable in
   PolyFun by design.
4. **Packet and action adequacy.** `IsSamplerBisimulation` preserves silence
   and external boundary traces for open processes, but `Observation` relates
   closed processes, where those boundary traces are empty. Any claim about
   internal packet/action identity must be proved as part of the downstream
   `hInv` adequacy theorem.
5. **`RespectsFactorization`.** Supplied generically by
   `Observation.respectsFactorization_of_samplerInvariant` from gates 1 and 3;
   `Observation.sampler` is the canonical sampled-path observation obtained
   this way, and `Observation.activation` the unconditional monad-free
   coarsening. Neither is itself a cryptographic security observation.

Efficiency is a separate gate. `StepClass` membership constrains which step
functions are admissible but carries no quantitative total-cost bound.
Allowed PPT contexts require a family-level machine witness, canonical or
provably translatable boundary encodings, state-size accounting, and closure
under the structural compositions consumed by `SubTheory`.

For returning computations, the quantitative successor uses the canonical
partial `update?`, not the junk-state convention `updateFlat`, so sequential
bind remains expressible. General dynamical systems instead carry an admissible
partial extension with an enabled-step correctness law; this avoids assuming
decidable equality on decorated type-tree positions. State growth must either be charged
additively or be restricted by an explicit cap whose completeness cost is
documented. Boundary encodings additionally need polynomial translation
invariance and a word-level coding retraction; injectivity alone is not a
complexity-invariant interface. The generic certificates are
`StepClass.PolyTranslatable`, `Boundary.PolyTranslatable`, and
`StepClass.PolyCodable`; a VCVio complexity class must instantiate their
admissibility fields quantitatively.

The coordinated milestone order and repository ownership are maintained in
[`uc-complexity-roadmap.md`](../reading/uc-complexity-roadmap.md).

## Related-Model Lessons

- EasyUC (CSV19) made general structural induction over EasyCrypt modules
  unavailable and required extensive routing loops; its later DSL uses types
  to reject malformed addresses and coroutine violations. Boundaries and
  control transfer therefore remain explicit data here.
- IITM (KTR20) isolates dummy forwarding and replacement of a machine network by one
  efficient machine as real model properties. PolyFun does not assume either
  silently.
- SSProve (HARM+23) demonstrates the value of proving package algebra once;
  Nominal SSProve (LS25-N) demonstrates the modularity cost of global, non-renamable state
  names. PolyFun consequently keeps machine identities out of the structural
  core: `Party` is an abstract type and no addressing scheme is built in.
- Robust-compilation accounts (PKWC24) derive UC composition and dummy results from
  explicit interface axioms. PolyFun follows the same audit discipline:
  abstractions are added when a theorem consumes them, and failed axioms get
  regression counterexamples rather than permissive defaults.
