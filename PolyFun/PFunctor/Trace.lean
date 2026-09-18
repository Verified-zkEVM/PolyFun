/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import PolyFun.Control.Trace
public import PolyFun.PFunctor.Chart.Basic

/-!
# Traces of polynomial-functor events

For a polynomial functor `P`, the universal "log of `P`-events" is the free
monoid on indices `Idx P = Σ a : P.A, P.B a`.  This file packages that monoid
together with the abstract `Control.Trace` machinery from
`PolyFun/Control/Trace.lean`.

## Main definitions

* `PFunctor.TraceList P` — the carrier `FreeMonoid (Idx P)`,
  definitionally `List (Σ a, P.B a)`.
* `PFunctor.Trace P X` — the type of `X`-indexed `P`-event traces,
  i.e. `X → TraceList P`, with monoid structure inherited pointwise.
* `PFunctor.Trace.mapPartial`, `mapChart`,
  `restrictLeft`, `restrictRight` — the standard push / filter operations
  along chart morphisms and direct-sum projections.
* `PFunctor.Trace.toMonoid` — the universal property: every valuation
  `Idx P → ω` extends uniquely to a monoid hom `TraceList P →* ω`, and so to
  a trace map `Trace P X → Control.Trace ω X`.

## Boundary-emitter intuition

Reading `Trace P X` as "for each input `x : X`, the finite, ordered list of
`P`-events that get emitted on the boundary": this is precisely the boundary
shape of a stateless effectful Mealy machine in the `List`-Writer Kleisli
category.  Stateful executors (e.g. running over an `OracleComp`) are handled
separately in `VCVio/OracleComp/QueryTracking/`.

The canonical user inside this repository is `BoundaryAction.emit` in
`PolyFun/Interaction/UC/OpenProcess.lean`, where `Trace Δ.Out X` records the
list of output-port packets a node emits when the local state transitions
to `x : X`. Operations such as `mapBoundary`, `wireLeft`, `wireRight`, and
the tensor embeddings of open processes are implemented directly by
`PFunctor.Trace.mapChart` and `PFunctor.Trace.mapPartial` against
appropriate boundary morphisms.


## References

* Bonchi, Di Lavore, Romàn — *Effectful Mealy machines and Kleisli
  categories*.
* Hancock, Setzer — *Interactive programs and weakly final coalgebras in
  dependent type theory*.
* Spivak, Niu — *Polynomial Functors: A Mathematical Theory of Interaction*,
  arXiv:2312.00990.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ v w

namespace PFunctor

/- `occurrences_cons_self/of_ne` and the base case of
`getAt?_mul_self_occurrences` reconstruct dependent position/answer pairs.
Those pairs must agree with `Idx` at implicit transparency when applying the
generator equations. Keep this override until an upstream `Idx` constructor
API, or consistently named event values, removes the mixed `Idx`/Sigma applications. -/
attribute [local implicit_reducible] PFunctor.Idx

/--
The free monoid on `P`-events.  Definitionally `FreeMonoid (Idx P)`, which
in turn is reducibly `List (Idx P)`.  This is the universal carrier for
"finite ordered logs of `P`-events".
-/
@[reducible] def TraceList (P : PFunctor.{uA, uB}) : Type max uA uB :=
  FreeMonoid (Idx P)

namespace TraceList

/-- The ordered input positions of a typed event trace, retaining repeated occurrences. -/
def positions {P : PFunctor.{uA, uB}} (events : TraceList P) : List P.A :=
  List.map (fun event : P.Idx => event.1) events.toList

@[simp]
theorem positions_nil {P : PFunctor.{uA, uB}} : positions ([] : TraceList P) = [] := rfl

@[simp]
theorem positions_cons {P : PFunctor.{uA, uB}} (event : P.Idx) (events : TraceList P) :
    positions (event :: events) = event.1 :: positions events := rfl

@[simp]
theorem length_positions {P : PFunctor.{uA, uB}} (events : TraceList P) :
    (positions events).length = events.length := List.length_map ..

@[simp]
theorem positions_one {P : PFunctor.{uA, uB}} : positions (1 : TraceList P) = [] := rfl

/-- Concatenating traces preserves the order and multiplicity of positions. -/
@[simp]
theorem positions_mul {P : PFunctor.{uA, uB}} (first second : TraceList P) :
    positions (first * second) = positions first ++ positions second := by
  simp only [positions, FreeMonoid.toList_mul, List.map_append]

/-- Every event in a trace carries a direction allowed at its position.

The allowed directions remain fiber-indexed: checking an event `⟨a, b⟩`
uses `allowed a`, so no equality casts or decidable equality on positions are
needed. -/
def DirectionsWithin {P : PFunctor.{uA, uB}}
    (allowed : (a : P.A) → Set (P.B a)) (events : TraceList P) : Prop :=
  ∀ event ∈ events, event.2 ∈ allowed event.1

@[simp]
theorem directionsWithin_nil {P : PFunctor.{uA, uB}} (allowed : (a : P.A) → Set (P.B a)) :
    DirectionsWithin allowed ([] : TraceList P) :=
  fun _ event_mem => absurd event_mem List.not_mem_nil

@[simp]
theorem directionsWithin_cons {P : PFunctor.{uA, uB}}
    (allowed : (a : P.A) → Set (P.B a)) (event : P.Idx) (events : TraceList P) :
    DirectionsWithin allowed (event :: events) ↔
      event.2 ∈ allowed event.1 ∧ DirectionsWithin allowed events :=
  List.forall_mem_cons

/-- Number of events at a given position in an erased execution trace. -/
def occurrences {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (target : P.A) (events : TraceList P) : Nat :=
  events.toList.countP fun (event : P.Idx) => event.1 = target

@[simp]
theorem occurrences_nil {P : PFunctor.{uA, uB}} [DecidableEq P.A] (target : P.A) :
    occurrences target ([] : TraceList P) = 0 := rfl

@[simp]
theorem occurrences_one {P : PFunctor.{uA, uB}} [DecidableEq P.A] (target : P.A) :
    occurrences target (1 : TraceList P) = 0 := rfl

/-- Prepending an answer at the target adds one occurrence. -/
@[simp]
theorem occurrences_cons_self {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (target : P.A) (answer : P.B target) (tail : TraceList P) :
    occurrences target ((⟨target, answer⟩ : P.Idx) :: tail) =
      occurrences target tail + 1 := by
  change occurrences target (FreeMonoid.of ⟨target, answer⟩ * tail) = _
  simp [occurrences]

/-- An event at a different position does not contribute to the count. -/
@[simp]
theorem occurrences_cons_of_ne {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    {a target : P.A} (hne : a ≠ target) (answer : P.B a) (tail : TraceList P) :
    occurrences target ((⟨a, answer⟩ : P.Idx) :: tail) =
      occurrences target tail := by
  change occurrences target (FreeMonoid.of ⟨a, answer⟩ * tail) = _
  simp [occurrences, hne]

/-- Occurrence counts add under trace concatenation. -/
@[simp]
theorem occurrences_mul {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (target : P.A) (first second : TraceList P) :
    occurrences target (first * second) =
      occurrences target first + occurrences target second := by
  simp only [occurrences, FreeMonoid.toList_mul, List.countP_append]

/-- Counting after prepending a monoid generator tests only its position. -/
theorem occurrences_of_mul {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (target : P.A) (event : P.Idx) (tail : TraceList P) :
    occurrences target (FreeMonoid.of event * tail) =
      occurrences target tail + if event.1 = target then 1 else 0 := by
  simp only [occurrences, FreeMonoid.toList_of_mul, List.countP_cons, decide_eq_true_eq]

/-- The answer carried by the `n`-th event at `target`, if that occurrence exists. -/
def getAt? {P : PFunctor.{uA, uB}} [DecidableEq P.A] :
    (events : TraceList P) → (target : P.A) → Nat → Option (P.B target)
  | [], _, _ => none
  | ⟨a, answer⟩ :: tail, target, 0 =>
      if h : a = target then some (h ▸ answer) else getAt? tail target 0
  | ⟨a, _⟩ :: tail, target, n + 1 =>
      if a = target then getAt? tail target n else getAt? tail target (n + 1)

theorem getAt?_cons_zero {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (event : P.Idx) (tail : TraceList P) (target : P.A) :
    getAt? (event :: tail) target 0 =
      if h : event.1 = target then some (h ▸ event.2) else getAt? tail target 0 := by
  rcases event with ⟨a, answer⟩
  rfl

theorem getAt?_cons_succ {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (event : P.Idx) (tail : TraceList P) (target : P.A) (n : Nat) :
    getAt? (event :: tail) target (n + 1) =
      if event.1 = target then getAt? tail target n else getAt? tail target (n + 1) := by
  rcases event with ⟨a, answer⟩
  rfl

@[simp] theorem getAt?_nil {P : PFunctor.{uA, uB}} [DecidableEq P.A] (target : P.A) (n : Nat) :
    getAt? ([] : TraceList P) target n = none := rfl

@[simp] theorem getAt?_cons_self_zero {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (target : P.A) (answer : P.B target) (tail : TraceList P) :
    getAt? (⟨target, answer⟩ :: tail) target 0 = some answer := by
  simp [getAt?]

@[simp] theorem getAt?_cons_self_succ {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (target : P.A) (answer : P.B target) (tail : TraceList P) (n : Nat) :
    getAt? (⟨target, answer⟩ :: tail) target (n + 1) =
      getAt? tail target n := by
  simp [getAt?]

@[simp] theorem getAt?_cons_of_ne {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    {a target : P.A} (hne : a ≠ target) (answer : P.B a) (tail : TraceList P) (n : Nat) :
    getAt? (⟨a, answer⟩ :: tail) target n = getAt? tail target n := by
  cases n <;> simp [getAt?, hne]

/-- Inspect the first event through the free-monoid constructor. -/
theorem getAt?_of_mul {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (event : P.Idx) (tail : TraceList P) (target : P.A) (n : Nat) :
    getAt? (FreeMonoid.of event * tail) target n =
      if h : event.1 = target then
        match n with
        | 0 => some (h ▸ event.2)
        | k + 1 => getAt? tail target k
      else getAt? tail target n := by
  rcases event with ⟨a, answer⟩
  cases n <;> rfl

/-- A dependent trace lookup succeeds exactly for the counted occurrences. -/
@[simp] theorem getAt?_isSome_iff_lt_occurrences {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (events : TraceList P) (target : P.A) (n : Nat) :
    (getAt? events target n).isSome ↔ n < occurrences target events := by
  induction events using FreeMonoid.recOn generalizing n with
  | one =>
      change false = true ↔ n < 0
      simp
  | of_mul event tail ih =>
      rw [getAt?_of_mul, occurrences_of_mul]
      by_cases h : event.1 = target
      · cases n <;> simp [h, ih]
      · simp [h, ih]

/-- The generator following a prefix is found at the prefix's occurrence count. -/
theorem getAt?_mul_self_occurrences {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (before after : TraceList P) (target : P.A) (answer : P.B target) :
    getAt? (before * (FreeMonoid.of (α := P.Idx) ⟨target, answer⟩ * after)) target
      (occurrences target before) = some answer := by
  induction before using FreeMonoid.recOn with
  | one => simp only [one_mul, occurrences_one, getAt?_of_mul, ↓reduceDIte]
  | of_mul event before ih =>
      rw [mul_assoc, getAt?_of_mul, occurrences_of_mul]
      by_cases h : event.1 = target <;> simpa [h] using ih

/-- The event following a prefix is found at the prefix's occurrence count. -/
theorem getAt?_append_self_occurrences {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (before after : TraceList P) (target : P.A) (answer : P.B target) :
    getAt? (List.append before (⟨target, answer⟩ :: after)) target
      (occurrences target before) = some answer :=
  getAt?_mul_self_occurrences before after target answer

/-- Relabel-and-filter the events of a trace list along a partial map of
indices: `List.filterMap` with the monoid structure of `TraceList` made
explicit. `Trace.mapPartial` is this operation pointwise. -/
def mapPartial {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (f : Idx P → Option (Idx Q)) (t : TraceList P) : TraceList Q :=
  FreeMonoid.ofList (t.toList.filterMap f)

/-- The list view of a partially mapped trace uses ordinary list filtering. -/
@[simp]
theorem toList_mapPartial {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (f : Idx P → Option (Idx Q)) (t : TraceList P) :
    (mapPartial f t).toList = t.toList.filterMap f :=
  FreeMonoid.toList_ofList _

@[simp] theorem mapPartial_one {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (f : Idx P → Option (Idx Q)) : mapPartial f (1 : TraceList P) = 1 :=
  rfl

theorem mapPartial_mul {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (f : Idx P → Option (Idx Q)) (a b : TraceList P) :
    mapPartial f (a * b) = mapPartial f a * mapPartial f b := by
  apply FreeMonoid.toList.injective
  simp only [toList_mapPartial, FreeMonoid.toList_mul, List.filterMap_append]

@[simp]
theorem mapPartial_some {P : PFunctor.{uA, uB}} (t : TraceList P) :
    mapPartial (fun i => some i) t = t := by
  apply FreeMonoid.toList.injective
  simp only [toList_mapPartial, List.filterMap_some]

@[simp]
theorem mapPartial_none {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (t : TraceList P) : mapPartial (Q := Q) (fun _ => none) t = 1 := by
  apply FreeMonoid.toList.injective
  simp

/-- Partial event maps compose by binding their optional outputs. -/
theorem mapPartial_comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} (g : Idx Q → Option (Idx R))
    (f : Idx P → Option (Idx Q)) (t : TraceList P) :
    mapPartial g (mapPartial f t) = mapPartial (fun i => (f i).bind g) t := by
  apply FreeMonoid.toList.injective
  simp only [toList_mapPartial, List.filterMap_filterMap]

end TraceList

/--
An `X`-indexed trace of `P`-events: for each input `x : X`, a finite ordered
list of `P`-events.  Specialisation of `Control.Trace` at
`ω = TraceList P`, inheriting a pointwise monoid structure.
-/
@[reducible] def Trace (P : PFunctor.{uA, uB}) (X : Type v) : Type max uA uB v :=
  Control.Trace (TraceList P) X

namespace Trace

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
  {R : PFunctor.{uA₃, uB₃}} {X Y : Type v}

/--
Relabel-and-filter a trace along a partial map of indices.  This is the
single primitive for moving traces between polynomial functors: total chart
pushforward and summand restriction are both specialisations of it.
-/
def mapPartial (f : Idx P → Option (Idx Q)) (t : Trace P X) : Trace Q X :=
  fun x => TraceList.mapPartial f (t x)

/-- Push a `P`-trace forward along a chart `P → Q`. -/
def mapChart (φ : Chart P Q) : Trace P X → Trace Q X :=
  mapPartial (fun i => some (Chart.mapIdx φ i))

/-- Pre-compose a `P`-trace with `f : Y → X` (input variance). -/
def precomp (f : Y → X) (t : Trace P X) : Trace P Y := Control.Trace.precomp f t

/--
The universal map into any monoid-valued trace via the free-monoid universal
property.  Every valuation `φ : Idx P → ω` extends uniquely to a monoid
homomorphism `FreeMonoid (Idx P) →* ω`; `toMonoid φ` post-composes a `P`-trace
with that hom.
-/
def toMonoid {ω : Type w} [Monoid ω] (φ : Idx P → ω) : Trace P X → Control.Trace ω X :=
  Control.Trace.map (FreeMonoid.lift φ)

/-! ### Pointwise behaviour -/

@[simp] theorem mapPartial_apply (f : Idx P → Option (Idx Q)) (t : Trace P X) (x : X) :
    mapPartial f t x = List.filterMap f (t x) := rfl

@[simp] theorem mapChart_apply (φ : Chart P Q) (t : Trace P X) (x : X) :
    mapChart φ t x = (t x).filterMap (fun i => some (Chart.mapIdx φ i)) := rfl

@[simp] theorem toMonoid_apply {ω : Type w} [Monoid ω] (φ : Idx P → ω) (t : Trace P X) (x : X) :
    toMonoid φ t x = FreeMonoid.lift φ (t x) := rfl

/-! ### Functoriality of `mapPartial` and `mapChart` -/

@[simp] theorem mapPartial_some (t : Trace P X) :
    mapPartial (fun i => some i) t = t := by
  funext x
  exact TraceList.mapPartial_some (t x)

theorem mapPartial_comp (g : Idx Q → Option (Idx R)) (f : Idx P → Option (Idx Q)) (t : Trace P X) :
    mapPartial g (mapPartial f t) = mapPartial (fun i => (f i).bind g) t := by
  funext x
  exact TraceList.mapPartial_comp g f (t x)

@[simp]
theorem mapPartial_none (t : Trace P X) : mapPartial (Q := Q) (fun _ => none) t = 1 := by
  funext x
  exact TraceList.mapPartial_none (t x)

@[simp] theorem mapChart_id (t : Trace P X) : mapChart (Chart.id P) t = t :=
  mapPartial_some t

@[simp] theorem mapChart_comp (g : Chart Q R) (f : Chart P Q) (t : Trace P X) :
    mapChart (g ∘c f) t = mapChart g (mapChart f t) := by
  change mapPartial (fun i => some (Chart.mapIdx (g ∘c f) i)) t =
    mapPartial (fun i => some (Chart.mapIdx g i))
      (mapPartial (fun i => some (Chart.mapIdx f i)) t)
  rw [mapPartial_comp]
  rfl

/-! ### Trivial-trace lemmas

The unit trace `1 : Trace P X = fun _ => []` is annihilated by all relabel /
filter operations.  These are needed downstream to reason about
boundary actions whose default emission is the empty trace. -/

@[simp] theorem mapPartial_one (f : Idx P → Option (Idx Q)) :
    mapPartial f (1 : Trace P X) = 1 := rfl

@[simp] theorem mapChart_one (φ : Chart P Q) :
    mapChart φ (1 : Trace P X) = 1 := rfl

/-! ### Naturality of `toMonoid`

Pushing a `P`-trace along a chart `φ : P → Q` and then evaluating against a
`Q`-valuation `ψ` is the same as evaluating against the precomposed
`P`-valuation `ψ ∘ Chart.mapIdx φ`.  This is exactly the free-monoid
naturality square. -/

@[simp] theorem toMonoid_mapChart {ω : Type w} [Monoid ω] (ψ : Idx Q → ω)
    (φ : Chart P Q) (t : Trace P X) :
    toMonoid ψ (mapChart φ t) = toMonoid (ψ ∘ Chart.mapIdx φ) t := by
  funext x
  change FreeMonoid.lift ψ
      (TraceList.mapPartial (some ∘ Chart.mapIdx φ) (t x)) =
        FreeMonoid.lift (ψ ∘ Chart.mapIdx φ) (t x)
  rw [FreeMonoid.lift_apply, TraceList.toList_mapPartial,
    List.filterMap_eq_map (f := Chart.mapIdx φ), FreeMonoid.lift_apply, List.map_map]

end Trace

/-! ### Restriction along direct-sum projections

The summand restriction operations need `P` and `Q` to share the `B` universe
so that `P + Q` typechecks. -/

namespace Trace

variable {P Q : PFunctor.{uA, uB}} {X : Type v}

/-- Restrict a trace on `P + Q` to its `P`-summand. -/
def restrictLeft : Trace (P + Q) X → Trace P X :=
  mapPartial (fun i => match i with
    | ⟨Sum.inl a, b⟩ => some ⟨a, b⟩
    | ⟨Sum.inr _, _⟩ => none)

/-- Restrict a trace on `P + Q` to its `Q`-summand. -/
def restrictRight : Trace (P + Q) X → Trace Q X :=
  mapPartial (fun i => match i with
    | ⟨Sum.inl _, _⟩ => none
    | ⟨Sum.inr a, b⟩ => some ⟨a, b⟩)

end Trace

end PFunctor
