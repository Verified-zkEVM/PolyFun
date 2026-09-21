# Realizability By Admissible State Machines

`PolyFun/Realizability/` answers the question "can this program be run by a
machine whose transition functions satisfy a given predicate?" — generically in
the predicate. It connects a behavioral specification to constraints on its
implementation:

| Question | Where it is answered |
| --- | --- |
| *What* interaction does the program perform? | `PFunctor.FreeM p β` |
| *How* does a machine perform it? | `PFunctor.DynSystem.DynComputation p α β` |
| Do the two agree (and within what budget)? | `Implements` / `ImplementsWithin` |
| Is the machine's *machinery* allowed? | **this subtree** |
| What exact backend work does its interaction prefix use? | `QuantitativeRealization` |

Instances include finite-state realizability and machines with computable
transitions. Cryptographic polynomial-time adversaries additionally require
quantitative run bounds, fixed encodings, and backend adequacy. These are
explicit certificates and downstream interpretation obligations.

## Where to start

| Task | Entry point |
|---|---|
| Define represented types and allowed functions | [StepClass](../../PolyFun/Realizability/StepClass.lean) |
| State a program realization with a fixed boundary | [Basic](../../PolyFun/Realizability/Basic.lean), [first-order maps](../../PolyFun/Realizability/Machine.lean) |
| Realize a non-returning dynamical system | [DynSystem](../../PolyFun/Realizability/DynSystem.lean) |
| Compose qualitative realizations | [Closure](../../PolyFun/Realizability/Closure.lean), [DynSystemClosure](../../PolyFun/Realizability/DynSystemClosure.lean) |
| Use finite, computable, or word-function instances | [Instances](../../PolyFun/Realizability/Instances.lean) |
| Change an encoding without changing admissibility | [Representation](../../PolyFun/Realizability/Representation.lean) |
| Retain executable evidence and exact local costs | [Quantitative](../../PolyFun/Realizability/Quantitative.lean), [prefixes](../../PolyFun/Realizability/Quantitative/Prefix.lean) |
| Prove resource bounds and bounded iteration | [Resource](../../PolyFun/Realizability/Quantitative/Resource.lean), [Iteration](../../PolyFun/Realizability/Quantitative/Iteration.lean) |

`Machine.lean` and `StepClass.lean` are independent; `Basic.lean` joins them.
`DynSystem.lean` is the non-returning substrate used by the UC bridge; it is
also re-exported by `Basic.lean`.

`QuantitativeRealization.runPrefix` returns the actual reached state and transition resource
log. `runPrefix_trace` supplies its syntactic trace witness; `observedCost` adds initialization
and the final observation exactly once. A prefix that has not returned consumes its full query
budget (`runPrefix_queries`). Probability laws and expected-potential reasoning for these
prefixes live downstream in VCVio, outside PolyFun's generic layer.

## `StepClass`: A Class Of Admissible Functions

```lean
structure PFunctor.StepClass where
  Str : Type u → Type v
  Hom : {A B : Type u} → Str A → Str B → (A → B) → Prop
  id_mem : ∀ {A} (a : Str A), Hom a a id
  comp_mem : Hom a b f → Hom b d g → Hom a d (g ∘ f)
```

A category of represented types and admissible functions. Its objects carry
both an underlying type and a selected `Str` value. It is a wide subcategory
of the category of these represented types with arbitrary functions, with a
faithful forgetful functor to `Type u`; it is not in general a wide subcategory
of `Type u` itself. For example, the finite-state class has no representation
of `Nat`. Two deliberate choices:

- **`Str` is data, not a proposition.** A resource bound only makes sense
  relative to a chosen representation: "`f` runs in polynomial time" is a
  statement about encoded inputs, not about the bare function.
- **`Hom` is a proposition.** The qualitative realizability layer only asks
  *whether* a step map is admissible. `QuantitativeStepClass` is a companion
  refinement whose `Type`-valued `Realizer` retains executable evidence and
  exact backend-relative cost while erasing back to `Hom`.

`StepClass.Hom.congr` transports admissibility along pointwise equality of
functions. It is the workhorse of the closure theory: a step map of a derived
machine is almost never *syntactically* the admissible combination one builds by
hand.

## Four mixins, and what each one buys

| Mixin | Required by | Content |
| --- | --- | --- |
| `HasProd` | the core | the flattened transition has a product domain |
| `HasSum` | the core | the one-step readout lands in a sum |
| `HasOption` | the core | the flattened transition is *partial* |
| `IsDistributive` | `seqComp` only | case analysis in a context |
| `HasULiftProd` | interleaving closure only | `ULift` regrouping of product states |

They are kept out of `StepClass` so that a cost-bearing successor can require
different structure, and split so that each theorem asks for exactly what it
consumes.

`HasOption` carries both ends of the optional interface: `none_mem` (the
constantly-absent transition of a returned machine) and `some_mem` (wrapping a
present value), and from `some_mem` with `obindCtx_mem` the derived
`HasOption.omapCtx_mem` gives the *strength* of `Option` — acting on the
present branch while retaining a context — which product-state machines need
to step one component while freezing the other.  `HasULiftProd` is the one
representation-level mixin: `Str (ULift A × ULift B)` and
`Str (ULift (A × B))` represent different types, and no `Hom`-level axiom can
convert representation data between types, so the regrouping used by
universe-normalized composite states is its own obligation.

### Binary distributivity on represented types

`HasProd` and `HasSum` select binary products and coproducts of represented
types. `IsDistributive` makes the canonical binary distributivity map an
isomorphism: its field supplies one direction, and `codistrib_mem` derives
the other from products and sums. Mathlib's
`CategoryTheory.IsCartesianDistributive` uses the cogap orientation; the local
`distrib_mem` field states admissibility of its inverse.

Only binary structure is required. No terminal or initial representation is
assumed, so this is not a claim of all finite products/coproducts or an instance
of Mathlib's categorical class. `StepClass.Distributive` additionally bundles
optional values for the closure theory. The definitions keep chosen encodings
explicit because quantitative costs depend on them.

The ordinary-import countermodel in
`PolyFunTest/Realizability/RepresentationBoundary.lean` represents types with
two distinct points. It has all the `Distributive` mixins and represents `Bool`,
but represents neither `Unit` nor `Empty`. Thus the missing nullary structure
cannot be inferred from the bundled assumptions.

A categorical adapter should use represented types as objects, not a
`MorphismProperty (Type u)` that forgets the representation arguments. Add such
an adapter when a consumer needs categorical theorems, supplying the missing
nullary structure where required; the current machine closure proofs use the
smaller concrete interface.

Distributivity is a real axiom, not a theorem: every bicartesian *closed* category
is automatically distributive because `X × (−)` is a left adjoint, but the
motivating classes have no exponentials.

### A note on the complexity-theory tradition

The complexity-native presentation of a class of functions is a **function
algebra** (Cobham 1965; Bellantoni–Cook 1992; Clote's handbook survey). Those are
*single-sorted*, so branching enters as a *base function* (`caseBit`,
Bellantoni–Cook's `C`) and distributivity is invisible. Making the axiom visible
is a consequence of being multi-sorted and representation-indexed. The closest
existing statement that a complexity class *is* a distributive category is
Cockett–Díaz-Boïls–Gallagher–Hrubeš (ENTCS 286, 2012), which exhibits PTIME and
LOGSPACE that way.

## The First-Order Step Maps

There are two related first-order boundaries.

For an arbitrary `DynSystem`, `DynSystem.Realization` constrains `expose` and a
chosen partial extension

```lean
update? : State × p.Idx → Option State
```

with a law saying that it returns the system's actual next state on every
enabled direction. Its behavior on mismatched tags is deliberately
unconstrained. This formulation does not require decidable equality on
positions, which is essential for `ProcessOver`: its positions are decorated
type trees containing types and functions. `DynSystem.ulift` first normalizes
the state, position, and direction universes into the one universe represented
by `StepClass`.

For a returning `DynComputation`, the stronger canonical maps below remain the
cost boundary used by free-program closure.

`DynComputation`'s dynamics live in `view : State → β ⊕ p.Obj State`, whose
second component stores a *function-valued* continuation and is *dependent* on
the exposed position. Neither shape can be constrained by a predicate on plain
functions, so `Machine.lean` re-presents the same dynamics first-order:

```lean
def head (M : DynComputation p α β) : M.State → β ⊕ p.A :=
  M.toDynSystem.expose

def update? [DecidableEq p.A] (M : DynComputation p α β) :
    M.State × p.Idx → Option M.State
```

`head` is not a new definition — it is *definitionally* the position map of the
machine's underlying lens. The public transport laws record the following
equalities; bare definitional checks in the owner module additionally guard their
implementation:

| Operation | Effect on `head` | Holds by |
| --- | --- | --- |
| `setInit g` | unchanged | `rfl` |
| `mapResult f` | `Sum.map f id ∘ head` | `rfl` |
| `wrap lens` | `Sum.map id lens.toFunA ∘ head` | `rfl` |

**`head`, not an `output` / `expose` pair.** Splitting the readout into
`output : State → Option β` and `expose : State → p.A` forces a `default`
convention at resolved states, and that convention breaks compositionality:
`(M.wrap lens).expose` is *not* `lens.toFunA ∘ M.expose`, because the two
disagree exactly at resolved states. `head` has no such wart. `output`, `expose`,
and `stepD` remain available as derived compatibility and execution accessors;
they are not the canonical cost boundary.

**`update?` is partial, and that is load-bearing.** `none` means the pair is not a
step the machine can take: the state has already returned, or the answer is tagged
with a position the machine is not exposing. The total compatibility variant
`updateFlat`, derived as `(update? step).getD step.1`, does **not** compose across
a state coproduct with a handoff:

| answer tag | composite `updateFlat` | `Sum.inr (M₂.updateFlat (M₂.init v, i))` |
| --- | --- | --- |
| matches `M₂`'s exposed position | `Sum.inr (next₂ d)` | `Sum.inr (next₂ d)` ✓ |
| does not match | `Sum.inl s₁` | `Sum.inr (M₂.init v)` ✗ |

Reconciling those junk values would require the class to contain a decidable
equality test on interface positions — provably not derivable from products,
coproducts, and distributivity, since in the free distributive category on one
object `Hom(X × X, 1 ⊕ 1)` contains only the two constants, and `StepClass` has no
terminal object. With `none` both rows agree, the both-resolved case is subsumed
(`M₂.update?` is `none` at a resolved state), and `update?_seqComp_inl` becomes an
equation *unconditional in the answer index*. That is the whole reason for the
partiality; the only cost is `DecidableEq p.A`.

**The presentation is faithful.** `ofStep_step_eq_of_flat_eq`: a step function is
determined by the `head` and `update?` it induces. So constraining those two maps
plus `init` constrains the machine, not a lossy projection of it.

**Spell the step maps with combinators, never `match`.** `Sum.elim`,
`Option.getLeft?`, `Sigma.fst`, and `dite` all reduce by congruence over the
shared `view`. An auto-generated matcher instead abstracts the computation and
blocks unification across distinct input types. Owner-module definitional
canaries pin the intended representation sharing; downstream proofs should use
the corresponding public equations rather than depend on reducer alignment.

## The Boundary Is A Parameter, Never An Existential

```lean
structure Boundary (C : StepClass) (p : PFunctor) (α β : Type u) where
  input : C.Str α
  out : C.Str β
  pos : C.Str p.A
  idx : C.Str p.Idx
```

A `Boundary` is always a *parameter* of a realizability statement. Existentially
choosing its representations can hide computation in an encoding and weaken
the intended resource restriction. Pin the boundary or supply the explicit
translation certificates discussed below. A realization chooses its internal
state representation subject to the step-map admissibility requirements.

`pos` and `idx` are supplied independently. Nothing derives one from the other,
since a step class is not assumed to represent dependent sums.

## The Predicates

```lean
def IsRealizableBy (C) (bd) (program : α → FreeM p β) : Prop :=
  ∃ R : Realization C bd, R.machine.Implements program

def IsRealizableWithin (C) (bd) (program : α → FreeM p β) (k : ℕ) : Prop :=
  ∃ R : Realization C bd, R.machine.ImplementsWithin program k
```

A `Realization` bundles a machine, a representation of its hidden state, and
three admissibility proofs — for `init`, `head`, and partial `update?`. Constraining
`init` is what forbids smuggling precomputed advice into the initial state.

`IsRealizableWithin.isTotalRollBound` extracts a bound on the *program*'s query
depth from the machine, and `IsRealizableWithin.isRealizableBy` drops the budget.

## Quantitative Realizability

`QuantitativeStepClass C` retains executable evidence without declaring a
complexity class:

```lean
structure QuantitativeStepClass (C : StepClass) where
  Realizer : C.Str A → C.Str B → (A → B) → Type w
  size : C.Str A → A → ℕ
  cost : Realizer a b f → A → ℕ
  admissible : Realizer a b f → C.Hom a b f

class QuantitativeStepClass.HasCategory (Q) where
  identity : Realizer a a id
  compose : Realizer a b f → Realizer b d g → Realizer a d (g ∘ f)
  composeOverhead : … → A → ℕ
  cost_compose_le : cost (compose rf rg) x ≤
    cost rf x + cost rg (f x) + composeOverhead rf rg x

class QuantitativeStepClass.HasExactCategory (Q) : Prop where
  cost_compose_eq : cost (compose rf rg) x =
    cost rf x + cost rg (f x) + composeOverhead rf rg x
```

The semantic function indexes its code, so correctness is intrinsic. Categorical
wiring is optional: the generic closure API needs only a sound upper bound, while
operational backends can retain their exact equation through `HasExactCategory`
or the `ExactCategory` adapter. The cost remains relative to the chosen backend;
an adequacy theorem must still connect that backend to a conventional Turing/RAM
model before a downstream library calls the resulting bound polynomial time.

`QuantitativeRealization` gives `init`, `head`, and enabled partial `update?`
actual realizers. Its dependent `ExecutionTrace` records every typed
query-answer edge. `executionCost` charges initialization once, every source
readout and enabled update, the final readout, encoded boundary traffic, and
peak state/readout sizes. `ExecutionTrace.Conforms allows` records that every
answer in a prefix obeys a dependent relation. `RunsWithinUnder allows` combines
a bound over conforming prefixes with `ResolvesInUnder` on allowed branches and
`TraceProgressUnder` at every conformingly reachable state. The progress conjunct
is separate because universal resolution is vacuous when the relation allows no
answer. `RunsWithin` is the all-answers specialization. Filtered `queryCount` and
`interfaceTraffic` are bounded for both restricted and unrestricted runs, so
per-interface accounting cannot exceed the globally charged run.

`Quantitative/Closure.lean` mirrors the four qualitative structural mixins with
executable product, sum, option, and distributivity code. It constructs
immediate-return, precomposed, result-mapped, and sequentially composed
realizations, plus interface transport from executable lens maps. Its `seqComp`
result is intentionally only
`IsQuantitativelyRealizableBy`: a backend may prove bounded or polynomial
closure after supplying bounds for its structural realizers and size encodings,
but the generic layer does not assume those bounds.

`Quantitative/BoundedClosure.lean` provides `RankedRunCertificate`, whose
natural-valued potential decreases on every allowed response and whose explicit
progress field prevents an empty allowed-answer relation from proving
termination vacuously. `RankedRunCertificate.runsWithinUnder` deliberately
keeps its pathwise backend-cost premise separate from termination. Input
precomposition transports traces in both directions and derives its additional
work from `cost_compose_le`. Result postcomposition also transports source and
target traces, but its bounded theorem consumes a `MapResultCostCertificate`:
the assembled head code and changed output encoding must be compared pathwise
with source execution plus an explicit overhead.

Bounded `seqComp` splits every composite trace into exact first- and second-phase
source traces, including the no-silent-step handoff where the first second-phase
query moves directly from a left state to a right state. A
`SeqCompHandoffBound` makes the second-phase premise uniform over every
conformingly reachable intermediate return value, while a
`SeqCompCostCertificate` accounts for the backend's structural composition
overhead. Together they yield the generic bounded sequential-composition
theorem without pretending that arbitrary unreachable values have small
encodings.

`Quantitative/Polynomial.lean` supplies `FirstOrderPolynomial` and
`PolyRealizer`, which retains one executable realizer plus work and encoded
output-size polynomials. `PolynomialCategory` proves identity and composition,
including an explicit polynomial for `composeOverhead`. `PolynomialModel` is an
ordinary value collecting that category with a `StructuralKernel` and
`PolynomialStructuralClosure`; it is deliberately not a global instance.
Structural product, sum, and option encodings carry construction and payload
recovery bounds in both directions.

`Quantitative/Resource.lean` adds the generic open-system resource boundary. A
`ResponseResourceContract` pins how interface positions are labelled and which
response environments are admissible; every admitted response is bounded by a
monotone size modulus. `ExecutionCostPolynomial` places a second-order
polynomial over each `ExecutionCost` component. The central split is deliberate:
`PolynomialRunBound` bounds one selected realization without mentioning syntax,
while `PolynomialProgramWitness` separately records `FreeM` implementation and
returned-output recovery. Pure programs, ranked local potentials, and sequential
composition have constructors that discharge the shared run-bound interface.
These are backend-relative contracts, not a declaration of any complexity class.

`QuantitativeWordClass` lifts code, size, and cost from a word-function backend
through `WordClass` representations. Separate category adapters lift either a
sound composition bound or the optional exact equation. As with the qualitative
adapter, clients must pin decodable representations rather than existentially
select arbitrary injections.

### Description measures and the counting separation

`Quantitative/Description.lean` adds the third measure a complexity backend
needs. A `DescriptionMeasure` gives every realizer a description size and, at
each size bound and each pair of representations, a finite type of canonical
descriptions, with the law that two realizers with the same description compute
the same function whenever the codomain representation is *faithful*.
Faithfulness is a parameter of the measure (injectivity, for raw string
encodings), never a field of the representation. `RealizableLE a b d` is the set
of functions with a realizer of description size at most `d`; against a faithful
codomain it is covered by a finite set no larger than the number of canonical
descriptions.

`Quantitative/Counting.lean` turns the cover into the nonuniform separation: if
every polynomial is eventually below a threshold and the description count at
that threshold is eventually below `2 ^ |D n|`, some Boolean predicate family has
no polynomially description-bounded realizer family
(`exists_not_realizableLE_poly`; `exists_not_realizableLE_poly_of_card_lt` fixes
the standard threshold `2 ^ (n / 4)`). Nothing about cost, time, or categorical
structure enters; the growth lemmas live in
`ToCslib/Algebra/PolynomialGrowth.lean`. The regression tests in
`PolyFunTest/Realizability/QuantitativeDescription.lean` record the two vacuity
canaries: the cost-free backend admits no measure against a trivial faithfulness
predicate, and admits a trivial one, under which everything is realizable at
size zero, against an unsatisfiable predicate. The theorem's content is therefore
entirely the backend's description count and the faithfulness of the pinned
boundary.

### Polynomial backends and families

`Quantitative/Family.lean` is where a description measure meets running time. A
`PolynomialBackend` asks the backend for a canonical polynomial certificate
`timeOf` on every realizer, an output-size envelope and a composition overhead
expressed through those certificates, and subadditive description size, with
every law in the shifted form `p.eval k ≤ P.eval (n + k)`. Canonical certificates
are necessary, not a convenience: `timeOf_compose_le` charges the second
machine's polynomial at the first machine's output envelope, a hypothetical
length that a per-use certificate such as `PolyRealizer` (bounds at actual
inputs only) does not control, so families of `PolyRealizer`s cannot compose
there. The separate `overhead` slot covers cost beyond that; on the single-tape
backend it is `0`, since `EncPolyTime.comp_time_eval` makes the two-term bound
an equality.

A `FamRealizer` is one realizer per security parameter `n` with a uniform time
bound in `n + k` (`k` the encoded input size) and a uniform description bound in
`n` (the advice bound). The `n + k` form is the formal content of the `1^n`
convention at this layer. Families have an identity, compose (the parameter is
folded into the envelope's argument, so the composite is one substitution looser
than the backend's own), and arise from `FiniteTables`, the advice primitive:
every function out of a polynomially small finite domain with a faithful input
representation has a realizer whose description is the size of its table. The
single-tape backend's `EncPolyTimeFam` is this structure field for field
(`EncPolyTimeFam.toFam`, `ofFam`), with `Backend.polynomialBackend` supplying
the certificates and `Backend.finiteTables` the finite-table machine.

### Three notions of polynomial time

Three certificates in and around the library all deserve the name "polynomial
time". They differ in what is uniform and in what the polynomial is a function
of.

| | Certificate | Uniform in | Polynomial in | Advice |
|---|---|---|---|---|
| (A) | `PPoly.IsPPolyBy` in `ComplexityBackends/CslibSingleTape/PPoly.lean` | nothing: one machine per parameter `n` | the parameter `n` | polynomially bounded description sizes |
| (B) | `PolynomialProgramWitness` in `Quantitative/Resource.lean` | the input | the encoded input size and the response moduli, as a second-order polynomial | none |
| (C) | a uniform packed certificate, VCVio's `SecurityFamily.IsOraclePPTBy` | the input and the parameter, packed with the parameter in unary | the packed input size | none |

(A) is nonuniform: the certificate is a family of machines indexed by `n` with
polynomially bounded descriptions, and its bound is a polynomial in `n` alone.
(B) is uniform in the input: one realization, one contract on the response
environment, and one second-order polynomial that may consult the response
moduli. (C) is the cryptographic notion; it is in flight downstream, and
PolyFun does not define it.

`ComplexityBackends/CslibSingleTape/ProgramWitness.lean` is the bridge
(A) ⇒ (B) at each `n`. `Witness.toPolynomialProgramWitness` turns a P/poly
certificate into a program witness at parameter `n` whose second-order
polynomial is the constant `runBoundCost`, under the total-answer contract
`totalContract` and with tag-bit output recovery. The only extra hypothesis is
that every position admits an answer, which the progress conjunct of
`RunsWithinUnder` needs. Neither reverse direction is in the library: a witness
at every `n` carries no description bound, and (C) needs the unary parameter
inside the packed encoding.

## Representation Invariance And Codability

`StepClass.PolyTranslatable a b` contains admissibility proofs for the identity
in both directions between two representations of the same type. Its `hom_iff`
theorem makes admissibility invariant under translated source and target
representations. Products, sums, and optional-value representations inherit the
certificate componentwise.

`DynComputation.Boundary.PolyTranslatable` applies that condition to the input,
result, position, and tagged-answer representations. The theorems
`isRealizableBy_iff_of_boundary_polyTranslatable` and
`isRealizableWithin_iff_of_boundary_polyTranslatable` transport one machine
witness in both directions without changing its hidden-state representation or
query budget. This is the explicit invariance theorem needed before replacing a
pinned cryptographic boundary encoding.

`DynSystem.Boundary.PolyTranslatable` is the non-returning counterpart for the
position and flattened-index representations used by open processes. Its
`isRealizableBy_iff_of_boundary_polyTranslatable` theorem transports the chosen
partial update extension and its enabled-step law unchanged. Since
`OpenProcess.StructuralBoundary` is this boundary at a canonical universe lift,
the same theorem supplies representation invariance for the UC bridge.

`StepClass.PolyCodable word rep` is stronger than an injective bit encoding. It
contains a semantic `CodeRetract` with `decode (encode value) = some value`, an
admissibility proof for the encoder, and an admissibility proof for the partial
decoder. Consequently the encoder is injective, but an injective function whose
range cannot be decoded in the ambient class does not qualify. `CodeRetract`
constructors build product, sum, option, and dependent-sigma codes from explicit
word pairing/tagging codecs; admissibility remains a separate proof so a
concrete complexity library must expose the operations it actually closes.

## Universe Discipline

`StepClass.Str` speaks about types in a single universe. The returning-program
predicates are stated at `p : PFunctor.{u, u}` with `α β : Type u`, hence
`State : Type u`. Then `p.A`, `p.Idx`, `β ⊕ p.A`, and `State × p.Idx` all live in
`Type u`. The underlying `DynComputation` API stays fully universe-polymorphic;
only this layer is pinned.

Arbitrary dynamical systems use `DynSystem.ulift` instead. In particular,
`OpenProcess.StructuralBoundary` lifts residual states, decorated step
positions, and paths to `max u v (w + 1)` before applying a step class. The lift
is explicit in the boundary type and therefore cannot conceal a representation
change. `StepOver.mapContextLens` identifies context mapping with polynomial
wrapping, `Lens.uliftMap` carries that lens through normalization, and
`OpenProcess.IsStructurallyRealizableBy.mapBoundary` reduces boundary-map
closure to one explicit `Lens.IsDynAdmissible` certificate.

## Instantiating With An External Complexity Class

Complexity classes in the wild are presented on one concrete function type —
`Complexity.FP : Set (List Bool → List Bool)` in complexitylib,
`Cslib.Turing.PolyTimeComputable` on `List Symbol → List Symbol` in cslib — with
no encoding-generic predicate. `StepClass.ofWordClass` is the bridge:

```lean
def ofWordClass (W : Type u) (Q : (W → W) → Prop) (hid : Q id)
    (hcomp : ∀ {f g}, Q f → Q g → Q (g ∘ f)) : StepClass.{u, u} where
  Str A := { encode : A → W // Function.Injective encode }
  Hom eA eB f := ∃ q, Q q ∧ ∀ x, q (eA.1 x) = eB.1 (f x)
```

Injectivity is deliberately the only demand of this low-level bridge, exactly as
for a raw bit encoding. A cryptographic boundary must additionally pin a
`PolyCodable` certificate (or an equivalent canonical-code theorem); existential
choice of this raw representation would permit an injective encoding with no
admissible decoder.

Products and sums are *not* automatic. They need a pairing codec and a tagging
scheme whose operations the word class admits, supplied as `WordPairing` and
`WordTagging` and consumed by `ofWordClass.hasProd` / `ofWordClass.hasSum`. As of
this writing complexitylib has the ingredients (`Complexity.pair`, `unpair?`,
`delimit`) but has not exposed them as a class-level closure result, and cslib's
`PolyTimeComputable` has `id` and `comp` but no pairing or projection machines at
all. The `CslibSingleTape` backend supplies encoded machine families and finite-table
constructors and uses those concrete certificates directly; it does not claim a
complete `ofWordClass` structural instance.

`StepClass.computable` — Mathlib's `Primcodable` representations and `Computable`
functions — is the in-repo instance that works today and exercises every mixin.

## The Optional `ComplexityBackends` Library

Concrete machine models live in the optional `ComplexityBackends` library, one
self-contained subdirectory per backend, outside the generic `PolyFun` umbrella.
The `CslibSingleTape` backend grounds the quantitative layer in cslib's
single-tape Turing machines. Its machine half imports only cslib, Mathlib, and
`ToCslib`:

- `ComplexityBackends/CslibSingleTape/PolyTime.lean` supplies encoded single-tape
  witnesses `EncPolyTime` with a running-time polynomial and a description size.
- `ComplexityBackends/CslibSingleTape/BitEncoding.lean` packages injective encoding
  families and uniform polynomial time and description bounds; its `EncPolyTimeFam`
  is the generic `FamRealizer` over this backend.
- `ComplexityBackends/CslibSingleTape/BasicMachines.lean` and
  `ComplexityBackends/CslibSingleTape/Snoc.lean` build the constant, finite-table,
  and append-bit machines behind `EncPolyTime.const`, `EncPolyTime.ofFintype`,
  and `EncPolyTime.appendBit`.
- `ComplexityBackends/CslibSingleTape/Counting.lean` supplies the
  machine-theoretic half of the counting separation: canonical `d`-state tables,
  state relabeling (`exists_tmTable_of_card_le`), determinism of runs
  (`Outputs_unique`), and the table count at the threshold size
  (`eventually_count_lt`).

Its adapter half connects this theory to PolyFun:

- `ComplexityBackends/CslibSingleTape/Description.lean` instantiates
  `DescriptionMeasure` with the state count as description size and the tables
  as canonical descriptions, faithfulness being injectivity of the codomain
  encoding, and states the counting separation at the canonical bitvector and
  optional-Boolean encodings (`Backend.exists_not_realizableLE_poly`). No uniform
  running-time bound across input lengths is involved.
- `ComplexityBackends/CslibSingleTape/Family.lean` supplies the canonical polynomial
  certificates (`Backend.polynomialBackend`: certified time, envelope `1 + X + p`,
  overhead `q.comp (1 + X + p)`), the finite-table primitive (`Backend.finiteTables`),
  and the round trip between `EncPolyTimeFam` and the generic families.

- `ComplexityBackends/CslibSingleTape/ProgramWitness.lean` bridges the
  nonuniform certificate to the generic program witness: at each parameter
  `n`, `Witness.toPolynomialProgramWitness` produces a
  `PolynomialProgramWitness` whose second-order polynomial is the constant
  `runBoundCost`, under the total-answer contract `totalContract`. See
  [three notions of polynomial time](#three-notions-of-polynomial-time).

- `ComplexityBackends/CslibSingleTape/Adequacy.lean` proves per-step adequacy.
  `Backend.cost_adequate` exhibits a halting run of the certified machine
  within `Backend.quantitative.cost`; `Backend.run_length_unique` and
  `Backend.run_length_le_cost` show that every run from the encoded input to
  the encoded output has that one length, so the envelope can only be
  overstated.

- `ComplexityBackends/CslibSingleTape/Backend.lean` interprets `EncPolyTime` as
  quantitative executable evidence. Its qualitative admissibility predicate is
  unconstrained; every quantitative map still carries a concrete machine certificate.
- `ComplexityBackends/CslibSingleTape/PPoly.lean` pins the input, output, position,
  and dependent-answer encodings. `IsPPolyBy` carries initialization, combined head
  observation, and partial-update machine families, polynomial state-length and
  round bounds, bounded semantic implementation, and `FreeM.ProgramProgress` at
  every reachable query (the liveness predicate in `PolyFun/PFunctor/Bound.lean`).
  `Witness.executionWork_le_totalTime` bounds every finite execution prefix by
  `initTime + (rounds + 1) * headTime + rounds * updateTime`, using the generic
  trace length and additive cost lemmas in `Quantitative.lean`.
- `ComplexityBackends/CslibSingleTape/Nontriviality.lean` extracts, from a pure
  Boolean certificate, one composed machine per parameter (initialization
  followed by decoded observation) whose state count is polynomially bounded, and
  applies the counting separation.

The work charge is each machine witness's certified time envelope. It excludes
external answer computation and does not count the exact steps of a linked
whole-program machine. No equivalence with the circuit characterization of
P/poly is asserted. Encodings are fixed by the caller; arbitrary changes of
encoding have no automatic complexity-preservation theorem. Precomposition and
result mapping require supplied code families.

The ordinary-import examples in
`PolyFunTest/ComplexityBackends/CslibSingleTape/PPoly.lean` cover pure returns,
real Boolean queries, distinct answers, mismatched update tags, nontrivial
input/result maps, and rejection of an empty-answer query.
`PolyFunTest/ComplexityBackends/CslibSingleTape/Basic.lean` consumes the machine
substrate independently of PolyFun, and
`PolyFunTest/ComplexityBackends/CslibSingleTape/Description.lean` holds the
adversarial canaries described below. `PolyFunTest/ModuleAPI/Realizability.lean`
and `PolyFunTest/ModuleAPI/ComplexityBackends.lean` reach both layers through
ordinary imports. The generated `PolyFun` umbrella imports no backend, and
`scripts/check-modules.sh` rejects any such import.

## What A Certificate Cannot Fake

The quantitative layer is only as honest as the facts that pin it. What a
dishonest prover cannot do, and where the definitions leave the burden with the
caller:

- **Understate cost.** `Backend.quantitative.cost` is the certified polynomial at
  the encoded input length. `Backend.cost_adequate` exhibits a halting run of
  the underlying machine within that bound, and `Backend.run_length_le_cost`
  shows that every run reaching the encoded output stays within it; a prover
  can only overstate.
- **Certify a hard family.** `exists_not_isPPolyBy_pure` exhibits a family with
  no witness at the pinned coin boundary, and the counting separation behind it
  is generic in the description measure.
- **Smuggle advice.** Description sizes are polynomially bounded by
  `EncPolyTimeFam.size_le`, finite tables cost one state per encoded input bit,
  and the description size is a projection of the witness, never chosen.
- **Terminate vacuously.** `RunsWithinUnder` carries a progress conjunct, and
  `rounds` is enforced through `ImplementsWithin`.
- **Move a certificate.** `recode` and `copy` preserve size and time.
- **Install a bogus measure.** A description measure with size zero exists only
  under an unsatisfiable faithfulness predicate, and the separation demands
  faithfulness at every boundary it separates.

Left to the pinned boundary, and exercised by the canaries in
`PolyFunTest/ComplexityBackends/CslibSingleTape/Description.lean`:

- `EncPolyTime` is trivially inhabited against a non-injective codomain encoding
  (the erasing machine), so faithfulness is always a hypothesis.
- An injective, polynomially wide `BitEncFam` may still cache the function in its
  encoding; only the canonical constructors are trustworthy, and a boundary is a
  parameter assembled from them, never an existential.
- The qualitative class `Hom := True` admits every function; the quantitative
  layer is load-bearing.

Still open: a whole-program linking theorem (below), completeness relative to a
standard model (reductions may be uncertifiable, never unsound), and the
`Type 0` pin of the single-tape description measure.

## Known Gaps

The operational dispatcher in `PFunctor/Free/HandlerMachine.lean` has executable phases,
resumable finite prefixes and a completion bound derived from caller and handler query bounds.
It counts administrative transitions explicitly. It is not a quantitative realizer: backend
code for the host operations, bounded administrative normalization, encoded state sizes and
actual work costs still require executable certificates. In particular, a syntactic query bound
alone does not establish strict PPT.

- **No whole-program machine-adequacy theorem.** The `CslibSingleTape` backend
  certifies the local step maps with cslib machines and bounds their additive
  time envelopes. `Backend.cost_adequate` is the per-step half: each certified
  step map has an actual halting run within its envelope, and by determinism
  every run reaching the encoded output has that length. A compiler and linking theorem for the
  complete interactive machine, in the sense of the reactive polynomial runtime
  of `HUM13`, and a circuit characterization remain separate obligations.
- **Open-process closure is a certificate obligation.**
  `OpenProcess.IsRealizabilityClosed` consists of four first-order lens
  admissibility certificates at the pinned boundary family
  (`structuralMapLens` plus the three `structuralInterleaveLens`
  instantiations); the composite closure theorems `par_mem` / `wire_mem` /
  `plug_mem` follow generically through the product-state combinator
  `DynSystem.IsRealizableBy.ulift_wrapChoiceProd` in `DynSystemClosure.lean`.
  Only the unconstrained canary instantiates the certificates in-tree; a
  concrete machine class must prove its own. `generatedRealizableSubTheory`
  records a composition derivation until that happens, and coincides with the
   direct view under the contract
   (`generatedRealizableSubTheory_eq_realizableSubTheory`).
- **`ImplementsWithin` is pinned to a uniform `ℕ` budget.** `FreeM.IsRollBound`
  is already generic in the budget type; `ImplementsWithin` is not.
- **Terminal and initial representations are not required.** The closure API
  uses binary distributivity. Admissibility of equality tests is a separate
  obligation, not a consequence of the presence or absence of nullary structure.
- **Constant maps are not assumed admissible**, with one exception: `HasOption`
  asserts `none_mem`, because a machine that has returned takes no step and so has
  a constantly-`none` transition. (`some_mem` is not a constant: it wraps its
  argument.) Everything else — `isRealizableBy_pure`, for instance — takes
  constant-admissibility as a per-theorem hypothesis. The worked example
  `PolyFunTest/Realizability/MapsToExamples.lean` builds the honest
  set-preserving class (`Str := Set`, `Hom := Set.MapsTo`) with all mixins and
  a negative admissibility example, confirming the framework restricts
  something.
- **The raw structural UC boundary is never finite or computable.**
  `OpenProcess.StructuralPFunctor` positions are (lifts of) `Σ tree : TypeTree,
  Decoration Γ tree`, and `TypeTree.node` quantifies over a whole type
  universe, so no `Fintype` or `Primcodable` representation of the full pinned
  `StructuralBoundary` exists. Honest quantitative UC instances therefore need
  codable *sub-interface* boundaries — a lens onto a countable interface plus
  `mapAdmissible` transport — which requires a
  concrete interface and admissibility proof from the consumer.
- **`Lens.IsAdmissible` has no `.id` and no `.comp`.** This is not an oversight:
  `pullHeadIdx` compares the incoming answer's tag against the position the lens
  exposes, so even the identity lens's pullback performs an equality test on
  positions. Admissibility of a lens is a genuine hypothesis about the class,
  satisfiable by every realistic one but not derivable from the mixins. It is also
  why `wrap` needs the hypothesis and `seqComp` does not.
- **No internal-language presentation.** The closure proofs explicitly assemble
  admissible functions using the class mixins. A term language for that plumbing
  is not part of the current API.

## References

See [`REFERENCES.md`](../../REFERENCES.md) — `AM74`, `AMMS13`, `PR89`, `Uus15`,
`PM15`, `Blum67`, `FKL22`, `DH11`, `Cob65`, `HUM13`, `GHP09` for the realizability notion, and
`Coc93`, `CLW93`, `Wal91`, `CF92`, `CDGH12`, `CH08`, `Clo99` for the
distributive-category and function-algebra vocabulary; plus `SN24`, `LS25`, and
`Abe26`.

Terminology follows classical (co)algebraic *realization* theory rather than the
word "implementation", which Aberlé (2026) uses for the free-monad Kleisli
morphism — that is, for the program side.

One clash worth flagging: in computable analysis *admissible representation* is a
fixed technical term (Weihrauch 1985), where "admissible" qualifies the
representation rather than the function class. This layer uses "admissible" in the
sense of Petcher–Morrisett's FCF admissibility predicate — a property of a
function, relative to chosen representations.

`PureResourceCertificate.eval_polynomial` exposes the derived pure-program resource bound
through the component code's public work and size polynomials. Consumers can inspect exact
specializations without unfolding the resource implementation across package boundaries.

### Bounded iteration

`PolyFun/Realizability/Quantitative/Iteration.lean` gives a uniform `IterationCode` taking an
encoded count and state. Its backend comparison charges each actual step code at the reached
state, plus explicit loop administration. `PolynomialBounds` separately bounds the iteration
count and initial-state size in the encoded input, and supplies a uniform additive growth bound.
These premises derive a polynomial state envelope and count-times-step-work bound for the same
code. A polynomial one-step time bound alone does not control repeated state growth.

This is a certificate constructor, not an instance asserting that every backend can implement
loops. A concrete backend must supply the iterator code and prove its local cost decomposition.
The arithmetic regression fixture checks changing per-step costs, zero-iteration setup, and the
rejection of unbounded doubling or a count erased from the input representation.
