# Realizability By Admissible State Machines

`PolyFun/Realizability/` answers the question "can this program be run by a
machine whose transition functions satisfy a given predicate?" — generically in
the predicate. It is the missing third ingredient above the existing machine
layer:

| Question | Where it is answered |
| --- | --- |
| *What* interaction does the program perform? | `PFunctor.FreeM p β` |
| *How* does a machine perform it? | `PFunctor.DynSystem.DynComputation p α β` |
| Do the two agree (and within what budget)? | `Implements` / `ImplementsWithin` |
| Is the machine's *machinery* allowed? | **this subtree** |

Instantiating the predicate recovers a spectrum of notions from one definition:
finite-state realizability, machines with computable transitions, and — the
motivating case downstream — the polynomial-time adversary model used in
cryptography.

## The Four Modules

```text
PolyFun/Realizability/
  StepClass.lean    PFunctor.StepClass; HasProd / HasSum / HasOption /
                    IsDistributive mixins; the Distributive bundle; Refines
  Machine.lean      the first-order step maps: head, update?, updateFlat,
                    output, expose, stepD, their transport lemmas, and
                    faithfulness of the flat presentation
  Basic.lean        Boundary, Realization, IsRealizableBy, IsRealizableWithin
  Closure.lean      closure under ofFn, precomp, mapResult, seqComp (bind),
                    wrap (interface transport), and class refinement
  Instances.lean    unconstrained, finite, computable, WordClass
```

`Machine.lean` and `StepClass.lean` are independent; `Basic.lean` joins them.

## `StepClass`: A Class Of Admissible Functions

```lean
structure PFunctor.StepClass where
  Str : Type u → Type v
  Hom : {A B : Type u} → Str A → Str B → (A → B) → Prop
  id_mem : ∀ {A} (a : Str A), Hom a a id
  comp_mem : Hom a b f → Hom b d g → Hom a d (g ∘ f)
```

A wide subcategory of `Type u`, presented pointwise. Two deliberate choices:

- **`Str` is data, not a proposition.** A resource bound only makes sense
  relative to a chosen representation: "`f` runs in polynomial time" is a
  statement about encoded inputs, not about the bare function.
- **`Hom` is a proposition.** The realizability layer only ever asks *whether* a
  step map is admissible. A cost-bearing refinement — witnesses carrying
  running-time and description-size measures — would replace it by a
  `Type`-valued field. That refinement is deliberately not in this subtree.

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

They are kept out of `StepClass` so that a cost-bearing successor can require
different structure, and split so that each theorem asks for exactly what it
consumes.

### It really is a distributive category

A class with `HasProd`, `HasSum`, and `IsDistributive` is exactly a **distributive
category** in the sense of Cockett (MSCS 1993) and Carboni–Lack–Walters (JPAA
1993), presented concretely — i.e. with a faithful functor to `Type` preserving
finite products and coproducts. Two points worth knowing:

* **This is not a one-sided weakening.** The *other* direction of the canonical
  map, the cogap `(A × I) ⊕ (B × I) → (A ⊕ B) × I`, is derivable from `HasProd`
  and `HasSum` alone and ships as `StepClass.codistrib_mem`. Both directions
  being admissible is literally "the canonical map is an isomorphism in the
  subcategory", which is Cockett's axiom verbatim.
* **Mathlib's canonical orientation is the opposite one.** Mathlib does have this
  concept — `CategoryTheory.IsCartesianDistributive`, citing the same two papers —
  and states the axiom in the cogap direction. Our `distrib_mem` field is the
  *inverse*. Do not read the arrow as a mistake.

We deliberately do **not** import Mathlib's version. `MorphismProperty (Type u)`
cannot type our `Hom`, which is indexed by *representations* and not just by
types; the `BundledHom` framework that matched this pattern exactly was
deprecated to nothing in February 2026; and `IsCartesianDistributive` has zero
consumers in Mathlib, so adopting it would cost a full monoidal/limit-cone layer
for no new theorem. Only the binary case is axiomatized here — no terminal or
initial representation is required, and none is needed — so
`StepClass.Distributive` is deliberately weaker than `IsCartesianDistributive`.

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

A `Boundary` is always a *parameter* of a realizability statement. A statement
of the form `∃ bd, IsRealizableBy C bd program` is **vacuous**: a representation
is only required to be admissible, not canonical, so an adversarially chosen
encoding can precompute across the boundary. Only the machine's own state
representation is chosen by the realization — and that choice is harmless, being
exactly the freedom to pick a state layout.

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

### Contract for a quantitative refinement

The qualitative layer proves which first-order maps compose; it does not infer a
total running-time bound from a query budget. A cost-bearing refinement must
therefore keep four obligations explicit:

1. charge initialization, `head`, and each enabled `update?` separately;
2. accumulate the size of reachable states, rather than assume query count bounds
   the cost of carrying or growing them;
3. transport costs only across pinned boundary representations with an explicit
   admissible translation and invariance theorem; and
4. retain a word-level encode/decode retraction when a concrete complexity class
   is used, so injectivity alone cannot hide non-computable advice in an encoding.

These are client obligations rather than extra fields of `IsRealizableWithin`:
the latter intentionally remains a qualitative admissibility predicate plus a
visible-query bound.

## Universe Discipline

`StepClass.Str` speaks about types in a single universe, so the realizability
predicates are stated at `p : PFunctor.{u, u}` with `α β : Type u`, hence
`State : Type u`. Then `p.A`, `p.Idx`, `β ⊕ p.A`, and `State × p.Idx` all live in
`Type u`. The underlying `DynComputation` API stays fully universe-polymorphic;
only this layer is pinned. Every intended instantiation target is monomorphic
anyway.

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

Injectivity of the encoding is the only semantic demand, exactly as for a raw bit
encoding.

Products and sums are *not* automatic. They need a pairing codec and a tagging
scheme whose operations the word class admits, supplied as `WordPairing` and
`WordTagging` and consumed by `ofWordClass.hasProd` / `ofWordClass.hasSum`. As of
this writing complexitylib has the ingredients (`Complexity.pair`, `unpair?`,
`delimit`) but has not exposed them as a class-level closure result, and cslib's
`PolyTimeComputable` has `id` and `comp` but no pairing or projection machines at
all. So a cslib instantiation is blocked upstream, not here.

`StepClass.computable` — Mathlib's `Primcodable` representations and `Computable`
functions — is the in-repo instance that works today and exercises every mixin.

## Known Gaps

- **No cost-bearing layer.** `Hom` is `Prop`-valued, so nothing here measures
  running time or description size. The successor layer needs `Hom` replaced by a
  `Type`-valued witness field carrying measures in an ordered semiring, with
  `size` additive under composition and `time` composing by substitution.
- **`ImplementsWithin` is pinned to a uniform `ℕ` budget.** `FreeM.IsRollBound`
  is already generic in the budget type; `ImplementsWithin` is not.
- **No terminal or initial representation**, hence only binary distributivity and
  no unparameterized equality test. Nothing needs them; adding them would tax
  every instance.
- **Constant maps are not assumed admissible**, with one exception: `HasOption`
  asserts `none_mem`, because a machine that has returned takes no step and so has
  a constantly-`none` transition. Everything else — `isRealizableBy_pure`, for
  instance — takes constant-admissibility as a per-theorem hypothesis.
- **`Lens.IsAdmissible` has no `.id` and no `.comp`.** This is not an oversight:
  `pullHeadIdx` compares the incoming answer's tag against the position the lens
  exposes, so even the identity lens's pullback performs an equality test on
  positions. Admissibility of a lens is a genuine hypothesis about the class,
  satisfiable by every realistic one but not derivable from the mixins. It is also
  why `wrap` needs the hypothesis and `seqComp` does not.
- **No internal-language presentation.** An inductive syntax for the free
  distributive category over the class's own maps, with one induction discharging
  all plumbing, is real prior art on paper (Cockett–Fukushima's Charity; Vigna,
  *Distributive computability*, 2003) and appears to be unformalized in any proof
  assistant. It would replace the hand-assembled combinator chains in
  `Closure.lean` with "exhibit a term". Worth doing if the combinator lemmas start
  multiplying; over-engineering for the five closure theorems here.

## References

See [`REFERENCES.md`](../../REFERENCES.md) — `AM74`, `AMMS13`, `PR89`, `Uus15`,
`PM15`, `Blum67`, `GHP09` for the realizability notion, and `Coc93`, `CLW93`,
`Wal91`, `CF92`, `CDGH12`, `CH08`, `Clo99` for the distributive-category and
function-algebra vocabulary; plus `SN24`, `LS25`, and `Abe26`.

Terminology follows classical (co)algebraic *realization* theory rather than the
word "implementation", which Aberlé (2026) uses for the free-monad Kleisli
morphism — that is, for the program side.

One clash worth flagging: in computable analysis *admissible representation* is a
fixed technical term (Weihrauch 1985), where "admissible" qualifies the
representation rather than the function class. This layer uses "admissible" in the
sense of Petcher–Morrisett's FCF admissibility predicate — a property of a
function, relative to chosen representations.
