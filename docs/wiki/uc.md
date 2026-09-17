# UC Semantic Contract

This page is the traceability ledger for PolyFun's structural UC layer. Lean
source remains authoritative. The external comparison target is Farshim,
Karvonen, Knispel, Kohlweiss, and Wadler, *UC, Categorically: Rigorous
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
| symmetric monoidal category `C` of interactive systems | `OpenTheory`, with `par`, `wire`, and a granular lawfulness ladder | Candidate model of the stated boundary equations; no Mathlib categorical equivalence is asserted. The free syntax models satisfy the strict laws, while `openTheory` is only `IsLawful` strictly and satisfies the monoidal, traced, and compact-closed laws up to `OpenProcessActivationEquiv`. `HasPlugFactorization` isolates the five factorization equalities the composition theorems consume without requiring unit or identity-wire operations. No strict or sampler-aware factorization instance for the process model follows from activation equivalence. The quotient by activation equivalence satisfies the strict `HasPlugWireFactor` class; this is equality of coarse activation classes, with no additional observation adequacy claim. The sampler-coherence layer proves `par_assoc`, `par_comm`, `wire_comm`, and the plug laws under explicit scheduler-transport hypotheses |
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

## Corruption Bookkeeping And Observation

`MomentaryCorruption` uses an abstract identity type `M : Type`; pair identities
are supplied as `M := Sid × Pid`. Decidable equality is needed by the updates
and canonical reaction, while the alphabet, state, and process types do not
require it.

`compromise m` marks the current epoch and sets a current corruption flag.
`refresh m` clears that flag and advances the counter, preserving every recorded
compromise flag. Arbitrary `State M` values may already mark future epochs;
properties of event histories need an invariant from `State.init`.

`EnvOpenProcess` pairs a process with a reaction on a separate state. Its
consumer connects those reactions to execution. `CorruptionModel.Process`
fixes the event and state types, while each value still supplies its own
reaction; `OpenProcess.withMomentaryCorruption` supplies the canonical one.

`SnapshotLeakable` provides only a per-party projection. Consumers choose when
to evaluate it and prove any relationship between observations, compromise
flags, or simulator behavior. Neither it nor the bookkeeping updates establish
leakage adequacy, key refresh, or post-compromise security. These are explicit
downstream obligations in a concrete semantics, as illustrated by
[CJSV22](../../REFERENCES.md#cjsv22--canetti-jain-swanberg-varia-end-to-end-secure-messaging).

Ordinary-import examples in
[`MomentaryCorruption.lean`](../../PolyFunTest/Interaction/UC/MomentaryCorruption.lean)
check identity renaming, empty and pair identities, and the bookkeeping and
projection contracts.

## Family Construction

`OpenTheory.pi` packages `T : ι → OpenTheory` pointwise. It lets a downstream
cryptographic development put one equivalence relation on closed-system
families while keeping the index semantically opaque in PolyFun. Every tier of
the strict lawfulness hierarchy lifts pointwise. `SubTheory.pi` lifts
pointwise membership, but polynomial-time membership will normally be a
custom family-level predicate because one witness and one bound must control
all security parameters.

## Quotient Theories

`OpenTheory.quotient T E` quotients a theory by a congruence
`E : OpenTheory.Congruence T` (a setoid on each boundary's objects preserved by
the operations). A theory whose coherence laws hold only up to `E` satisfies the
laws modulo `E` (`IsLawfulMod E`, …, `HasPlugWireFactorMod E`,
`HasPlugFactorizationMod E`), and each of those lifts to the strict class on
the quotient; a strict theory satisfies every law modulo any congruence. The
free syntax model is exactly this construction: `Expr.theory` is the quotient
of `Raw.theory` by `Raw.congruence`, whose laws modulo the congruence are the
constructors of `Raw.Equiv`. Its `Expr` facade keeps the reducible carrier,
map/par/wire operations, and named law instances. `Expr.theory_plug` identifies
the lifted plug with the derived `Expr.plug` operation propositionally.

Observations cross the quotient by `Observation.comap` and
`Observation.descend`; equality of classes pulls back to the congruence at the
empty boundary (`Observation.comap_eq_rel`), and `Emulates.quotient_iff`
identifies emulation of classes with emulation of representatives. This does
not identify contextual emulation with equality of classes: closing contexts
may forget distinctions. `Observation.descend` requires the congruence to
imply the observation; equality of representatives generally cannot descend
through a nontrivial congruence. Because `RespectsFactorization` pulls back
along `comap`, a theory whose laws hold
modulo `E` gets the whole `Emulates` composition suite at any observation that
factors through its quotient, without carrying coherence hypotheses through
every client. `OpenProcessQuotient` does this for the process models: the
activation quotient `openTheory ⧸ activationCongruence` is a strict
`HasPlugWireFactor` theory, the sampler quotient satisfies
`HasPlugFactorization` under the three scheduler-transport facts, and the
mass-aware sampler quotient (whose congruence also fixes scheduler mass)
satisfies it under `BinaryScheduler.IsCoherent`. Both sampler congruences
require a lawful monad and a bind-congruent relation family (`R.IsBindCongr`).
`Observation.activation` and `Observation.sampler` are the pull-backs of
equality on the respective quotients. On the scheduled quotient, equality also retains mass; its pull-back
is `Observation.ofCongruence`, while `Observation.scheduledSampler` forgets
mass and can relate distinct classes. These quotients add no probabilistic
or cryptographic adequacy claim.

## Reactive Execution And Exact Behavior

[`ReactiveProcess`](../../PolyFun/Interaction/UC/ReactiveProcess.lean) expresses local effects,
receiving, sending, local work, and yielding as one polynomial. Receiving has typed incoming
packets as directions, so actual input selects the continuation. `Process` is a
`DynComputation`; `Behavior` is a `Resumption`. `boundaryLens` reuses the established
input/output variance, and `denote_mapBoundary` identifies its resumption semantics.

[`ReactiveNetwork`](../../PolyFun/Interaction/UC/ReactiveNetwork.lean) assigns stable identities
separate effect and packet interfaces, routes sends into typed mailboxes or the external
boundary, and threads one shared service state. Its token and FIFO runners retain residual
machines, pending traffic, terminal abort/return outcomes, the control holder, and elapsed
activations. Every tick, yield, delivery, or blocked activation consumes fuel. An atomic
handler's internal cost remains a separate obligation. External input enters through an
explicit ingress map; the security layer must constrain who may inject which input.

[`Transport`](../../PolyFun/Interaction/UC/ReactiveNetwork/Transport.lean) proves that a
bijection of identities transports actual execution under both policies. The dependent
packets, initialization, schedules, token holder, and effects move together. This supplies
renaming and regrouping of an existing flat diagram. `runToken_reindex_cast` and
`runFIFO_reindex_cast` consume a proved graph equality to transport complete residual
configurations through factorization. These results do not resample a scheduler.

[`Diagram`](../../PolyFun/Interaction/UC/ReactiveNetwork/Diagram.lean) separates typed
components and routes from selection of the global environment. Its `map`, `par`, `wire`,
and derived `plug` preserve component machines. The
[factorization laws](../../PolyFun/Interaction/UC/ReactiveNetwork/Factorization.lean) and
[right-component laws](../../PolyFun/Interaction/UC/ReactiveNetwork/Factorization/Right.lean)
prove plug symmetry, boundary-map transport, and all four parallel/wired closure
factorizations as graph equalities after explicit component bijections. The `Network`
versions retain the environment selected in the closing context. These are direct routing
theorems, independent of the legacy activation quotient and its scheduler hypotheses.

[`Assembly`](../../PolyFun/Interaction/UC/ReactiveNetwork/Assembly.lean) bundles a finite
diagram and compiles `OpenSyntax.Raw` using its existing universal interpretation.
`idWire` is a persistent receive/send forwarding machine. The
[assembly regressions](../../PolyFunTest/Interaction/UC/ReactiveAssembly.lean) distinguish
its charged eight-step echo from a direct four-step exchange. No timed snake equation
is assumed. The [factorization consumer](../../PolyFunTest/Interaction/UC/ReactiveFactorization.lean)
transports every token prefix and arbitrary FIFO schedules for a context communicating with
two separate machines. The echo tests refute retaining the old schedule after node relabeling.

[`HandledDiagram`](../../PolyFun/Interaction/UC/ReactiveNetwork/HandledDiagram.lean) and
[`HandledAssembly`](../../PolyFun/Interaction/UC/ReactiveNetwork/HandledAssembly.lean) carry
each component's actual polynomial-operation interpreter as intrinsic data. Raw compilation,
parallel composition, wiring, and all four closure factorizations preserve those interpreters.
The public token and FIFO observation equations use the actual runners; FIFO schedules follow
the component bijections. `atom_plug_atom` normalizes direct two-machine communication without
adding relay nodes. The [handler tests](../../PolyFunTest/Interaction/UC/ReactiveHandlers.lean)
show that identical unhandled diagrams can return different values and distinguish a failed
interpreter from a successfully executed unfinished prefix. The explicit monad determines
ambient capabilities: a stateless sampler grants no shared-state access, whereas choosing a
shared-state monad grants that capability. Interpreter work still needs separate resource bounds.

[`Behavior`](../../PolyFun/Interaction/UC/ReactiveNetwork/Behavior.lean) proves exact adequacy:
`runFIFO_behavior` and `runToken_behavior` commute execution with the map from private states
to cofree behavior, in any lawful effect monad. Initialization and terminal observations
also commute. This hides **state representation**, while retaining every effect operation,
packet, delay, and fuel unit. It is not a theorem identifying arbitrary effectful handlers
with pure cofree matter, and it does not make the behavior network into a lawful
monoidal/traced `OpenTheory` automatically.

[`Serial`](../../PolyFun/Interaction/UC/ReactiveNetwork/Serial.lean) gives a deliberately
restricted policy comparison: from an empty pending queue, `runSerial_eq_runToken` identifies
every finite serial FIFO prefix with the corresponding token prefix, retaining one extra
delivery activation per round in the complete residual state. The proof works in any lawful
monad, including failure, without assuming effect normalization. Arbitrary FIFO schedules can
behave differently. The
[echo regressions](../../PolyFunTest/Interaction/UC/ReactiveNetwork.lean) exercise actual
input-dependent output, missing delivery, short prefixes, and explicit abort.

The legacy `OpenProcess` model has activation/output episodes but no intrinsic reaction to
incoming packets. It cannot be adapted into a general reactive process without supplying
that behavior. Its activation and sampler quotients retain their documented scope; neither
is upgraded to this reactive semantics by a definitional alias.

[`Budget`](../../PolyFun/Interaction/UC/ReactiveNetwork/Budget.lean) proves exact elapsed counts
for every successful token/FIFO prefix. Its `TokenBudgetCertificate` combines an invariant,
a decreasing global rank while the environment is unfinished, and explicit nonempty progress.
`runToken_terminal` proves that every successful result after sufficient fuel has a terminal
environment; `runToken_nonempty` rules out obtaining that claim solely through an interpreter
with no possible result. Progress does not assert that all effect branches return. Atomic
interpreter work and runtime implementation costs still require their own witnesses.
The [budget tests](../../PolyFunTest/Interaction/UC/ReactiveBudget.lean) admit a countdown,
reject an everywhere-failing interpreter, and execute arbitrarily many productive ping-pong
rounds between two actors with two-operation local reactions. That feedback network cannot
have a global certificate, despite its bounded local reactions.

The probability-independent
[`RequestNetwork`](../../PolyFun/Interaction/UC/RequestNetwork.lean) is a separate finite
request/reply specialization: well-founded clients, one outstanding ticket per client, and
an atomic shared handler. Its [serial theorem](../../PolyFun/Interaction/UC/RequestNetwork/Serial.lean)
preserves result, service state, and transcript for every bounded adaptive client. Trace
erasure is an application of the universal fold's naturality through `WriterT.eraseHom`.
VCVio specializes this API to `OracleSpec`; this extraction alone is not a reactive-network
embedding theorem.

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

The program-logic seam follows the same rule. VCVio's quantitative carrier is an
`MAlgOrdered (OracleComp spec) ℝ≥0∞`, and everything it needs on core's
weakest-precondition stack is a named PolyFun export rather than an unfolding:
`MAlgOrdered.toWPMonad` (with `wp` agreeing by `rfl`), the probabilistic carrier
`Set.Iic 1` through `MAlgOrdered.restrictIic` (with `wp_restrictIic_val` and
`restrictIic_triple_iff` as the contract), `WriterT.instWPMonad` for its
logging stacks (`WriterT.wp_apply_eq`), and the transports of
`PolyFun/Control/Monad/Hom/WP.lean` for handler-relative interpretations. See
[`program-logic.md`](program-logic.md).

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
   VCVio responsibilities. For the mass-aware theory `scheduledOpenTheory`,
   `BinaryScheduler.IsCoherent` is the whole obligation:
   `scheduledOpenTheory_plug_{comm,par_left,par_right,wire_left,wire_right}_sampler_equiv`
   and `Observation.respectsFactorization_scheduledSampler` take coherence and
   nothing else. Both theories' laws are instances of the sampler-level shapes
   in `OpenProcessSamplerCoherence`, whose only transport hypothesis is that
   the two nested scheduler draws of a regrouping are `R`-related; sampler
   equivalence is moreover a congruence for the shared-sampler `openTheory`
   operations. Its binary operations require right-continuation congruence
   (`MonadRelFamily.IsBindCongr`); boundary mapping does not. These are laws
   for a fixed scheduler draw. The scheduled observation compares underlying
   processes and does not require equal masses; substitution under a
   mass-sensitive scheduler needs matching masses or an additional transport
   proof. `SamplerCoherenceExamples` instantiates coherence at exact equality
   in Mathlib's `SetM`, where every branch is possible. No identity-monad
   scheduler satisfies exact coherence, as `not_isCoherent_eq_id` shows.
2. **Initial-state correspondence.** The totality fields of
   `OpenProcessSamplerEquiv` guarantee related states in both directions; they
   do not specify a chosen initial state. The regrouping proofs use component
   permutations, which a downstream pointed model can use to establish its
   initial-state correspondence.
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
