/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Realizability.Machine
public import PolyFun.Realizability.StepClass

/-!
# Realizability of free programs by admissible state machines

A well-founded program family `program : α → FreeM p β` says *what* interaction
to perform. A `DynComputation p α β` says *how* a machine performs it, and
`DynComputation.Implements` says the two agree. This module adds the missing
third ingredient: a constraint on the machine's transition functions.

`IsRealizableBy C bd program` holds when some `C`-admissible machine implements
`program`, where `C` is a `StepClass` and admissibility is asserted of the three
first-order step maps `init`, `head`, and `update?` from
`PolyFun.Realizability.Machine`. `IsRealizableWithin C bd program k` additionally
demands that every branch resolve within `k` visible queries.

Instantiating `C` recovers a spectrum of concrete notions from one definition:
the trivial class gives back plain implementability, a finiteness class gives
finite-state realizability, a computability class gives machines with computable
transitions, and a resource-bounded class gives the polynomial-time
adversary model used in cryptography.

## The boundary is a parameter, never an existential

`Boundary` collects the representations of the input type, the result type, and
the interface. It is always a *parameter* of a realizability statement. A
statement of the form `∃ bd, IsRealizableBy C bd program` is vacuous, because a
representation is only required to be admissible, not canonical: an adversarially
chosen encoding can precompute across the boundary. Only the machine's own state
representation is chosen by the realization, and that choice is harmless — it is
exactly the freedom to pick a state layout.

## Universe discipline

`StepClass.Str` speaks about types in a single universe, so this layer is stated
at `p : PFunctor.{u, u}` with `α β : Type u` and hence `State : Type u`. Then
`p.A`, `p.Idx`, `β ⊕ p.A`, and `State × p.Idx` all live in `Type u`. The
underlying `DynComputation` API remains fully universe-polymorphic; only the
realizability predicates are pinned.

## Provenance

This is a `C`-relative *realization* condition in the sense of classical
(co)algebraic realization theory (Arbib–Manes 1974; Adámek–Milius–Moss–Sousa
2013) and of finite-state realizability in reactive synthesis (Pnueli–Rosner
1989), transported to the free-monad-over-a-polynomial-functor setting of
Libkind–Spivak 2025 and Aberlé 2026, with the resource bound imposed as an
admissibility predicate on the structure maps rather than as a Blum-style
measure on runs (Blum 1967).

Two identifications make the shape of the definition inevitable. A `p`-coalgebra
on `S` *is* a way of running every `FreeM p` program in `S` (Uustalu 2015:
stateful runners are comodels, hence coalgebras), so a realization has nowhere
else to live. And the known special case at the class "given by a finite `FreeM`
term" is the alternating `νX.μY.` representation of stream processors
(Ghani–Hancock–Pattinson 2009).

The word *realization* rather than *implementation* is deliberate: Aberlé uses
"implementation" for the free-monad Kleisli morphism, that is, for the program
side. See `REFERENCES.md`.
-/

@[expose] public section

universe u v v₂

namespace PFunctor

namespace DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {α β : Type u}

/-! ## The boundary of a realizability statement -/

/-- The pinned representations at the boundary of a realizability statement: the
input type, the returned-value type, and the interface's query positions and
index space.

The positions and the index space are supplied independently — nothing derives
one from the other, since a class need not represent dependent sums. -/
structure Boundary (C : StepClass.{u, v}) (p : PFunctor.{u, u}) (α β : Type u) :
    Type v where
  /-- Representation of the input type. -/
  input : C.Str α
  /-- Representation of the returned-value type. -/
  out : C.Str β
  /-- Representation of the interface's query positions. -/
  pos : C.Str p.A
  /-- Representation of the interface's index space `Idx p = Σ a, p.B a`. -/
  idx : C.Str p.Idx

/-- The interface portion of a realizability boundary, independent of a program's input and
returned-value representations.

This projection is useful when several programs share one response policy or resource contract.
The position and index representations remain independent because a step class need not construct
dependent-sum representations. -/
structure InterfaceBoundary (C : StepClass.{u, v}) (p : PFunctor.{u, u}) : Type v where
  /-- Representation of the interface's query positions. -/
  pos : C.Str p.A
  /-- Representation of the interface's dependent position-response index. -/
  idx : C.Str p.Idx

namespace Boundary

variable {C : StepClass.{u, v}}

/-- Forget a boundary's input and returned-value representations. -/
def interface (bd : Boundary C p α β) : InterfaceBoundary C p :=
  ⟨bd.pos, bd.idx⟩

@[simp] theorem interface_pos (bd : Boundary C p α β) : bd.interface.pos = bd.pos := rfl

@[simp] theorem interface_idx (bd : Boundary C p α β) : bd.interface.idx = bd.idx := rfl

/-- The representation of a machine's one-step readout `β ⊕ p.A`, assembled from
the result and position representations. -/
def head [S : C.HasSum] (bd : Boundary C p α β) : C.Str (β ⊕ p.A) :=
  S.sum bd.out bd.pos

/-- The representation of the flattened transition's domain: a machine state
paired with the interface's index space. -/
def stateIdx [P : C.HasProd] (bd : Boundary C p α β) {S : Type u}
    (state : C.Str S) : C.Str (S × p.Idx) :=
  P.prod state bd.idx

/-- Replace the input representation of a boundary, keeping the result and
interface representations. -/
def withInput {γ : Type u} (bd : Boundary C p α β) (inputRep : C.Str γ) :
    Boundary C p γ β :=
  ⟨inputRep, bd.out, bd.pos, bd.idx⟩

/-- Replace the result representation of a boundary, keeping the input and
interface representations. -/
def withOut {γ : Type u} (bd : Boundary C p α β) (outRep : C.Str γ) :
    Boundary C p α γ :=
  ⟨bd.input, outRep, bd.pos, bd.idx⟩

@[simp] theorem withInput_input {γ : Type u} (bd : Boundary C p α β)
    (inputRep : C.Str γ) : (bd.withInput inputRep).input = inputRep := rfl

@[simp] theorem withOut_out {γ : Type u} (bd : Boundary C p α β)
    (outRep : C.Str γ) : (bd.withOut outRep).out = outRep := rfl

@[simp] theorem withInput_head [C.HasSum] {γ : Type u} (bd : Boundary C p α β)
    (inputRep : C.Str γ) : (bd.withInput inputRep).head = bd.head := rfl

@[simp] theorem withOut_input {γ : Type u} (bd : Boundary C p α β)
    (outRep : C.Str γ) : (bd.withOut outRep).input = bd.input := rfl

/-- The middle boundary of a sequential composition: the second phase reads the
first's results and shares its interface.

Derived rather than constrained. Representations are *data*, so a `Prop`-valued
equality between two boundaries would force `subst` transport at every use site;
deriving the middle boundary makes every compatibility fact hold by `rfl`. The
composite boundary of a sequential composition is then simply
`bd.withOut outRep`. -/
def mid {γ : Type u} (bd : Boundary C p α β) (outRep : C.Str γ) :
    Boundary C p β γ :=
  (bd.withOut outRep).withInput bd.out

@[simp] theorem mid_input {γ : Type u} (bd : Boundary C p α β)
    (outRep : C.Str γ) : (bd.mid outRep).input = bd.out := rfl

@[simp] theorem mid_out {γ : Type u} (bd : Boundary C p α β)
    (outRep : C.Str γ) : (bd.mid outRep).out = outRep := rfl

@[simp] theorem mid_pos {γ : Type u} (bd : Boundary C p α β)
    (outRep : C.Str γ) : (bd.mid outRep).pos = bd.pos := rfl

@[simp] theorem mid_idx {γ : Type u} (bd : Boundary C p α β)
    (outRep : C.Str γ) : (bd.mid outRep).idx = bd.idx := rfl

/-- Two boundaries compose when the second reads the first's results and both
describe the same interface. A convenience wrapper over `mid`, for use sites that
already have both boundaries in hand. -/
structure Composable {γ : Type u} (bd₁ : Boundary C p α β)
    (bd₂ : Boundary C p β γ) : Prop where
  /-- The second phase reads the first's results. -/
  input_eq : bd₂.input = bd₁.out
  /-- Both phases describe the same query positions. -/
  pos_eq : bd₂.pos = bd₁.pos
  /-- Both phases describe the same index space. -/
  idx_eq : bd₂.idx = bd₁.idx

theorem eq_mid_of_composable {γ : Type u} {bd₁ : Boundary C p α β}
    {bd₂ : Boundary C p β γ} (h : bd₁.Composable bd₂) :
    bd₂ = bd₁.mid bd₂.out := by
  obtain ⟨input, out, pos, idx⟩ := bd₂
  obtain ⟨hinput, hpos, hidx⟩ := h
  subst hinput
  subst hpos
  subst hidx
  rfl

/-- Replace the interface representations of a boundary, keeping the input and
result representations. This is the target boundary of an interface transport. -/
def withInterface (bd : Boundary C p α β) {q : PFunctor.{u, u}}
    (posRep : C.Str q.A) (idxRep : C.Str q.Idx) : Boundary C q α β :=
  ⟨bd.input, bd.out, posRep, idxRep⟩

@[simp] theorem withInterface_input (bd : Boundary C p α β)
    {q : PFunctor.{u, u}} (posRep : C.Str q.A) (idxRep : C.Str q.Idx) :
    (bd.withInterface posRep idxRep).input = bd.input := rfl

@[simp] theorem withInterface_out (bd : Boundary C p α β)
    {q : PFunctor.{u, u}} (posRep : C.Str q.A) (idxRep : C.Str q.Idx) :
    (bd.withInterface posRep idxRep).out = bd.out := rfl

@[simp] theorem withInterface_pos (bd : Boundary C p α β)
    {q : PFunctor.{u, u}} (posRep : C.Str q.A) (idxRep : C.Str q.Idx) :
    (bd.withInterface posRep idxRep).pos = posRep := rfl

@[simp] theorem withInterface_idx (bd : Boundary C p α β)
    {q : PFunctor.{u, u}} (posRep : C.Str q.A) (idxRep : C.Str q.Idx) :
    (bd.withInterface posRep idxRep).idx = idxRep := rfl

/-- Translate a boundary along a refinement of step classes. -/
def mapRefines {D : StepClass.{u, v₂}} [C.HasProd] [C.HasSum] [C.HasOption]
    [D.HasProd] [D.HasSum] [D.HasOption] (Ref : C.Refines D)
    (bd : Boundary C p α β) : Boundary D p α β :=
  ⟨Ref.str bd.input, Ref.str bd.out, Ref.str bd.pos, Ref.str bd.idx⟩

end Boundary

/-! ## Admissible realizations -/

/-- A `C`-admissible realization of an interface-`p` computation with inputs `α`
and results `β`.

The data is a returning dynamical computation together with a representation of
its hidden state — chosen freely by the realization — and proofs that its three
first-order step maps are `C`-morphisms:

* `init : α → State` starts the machine. Constraining it is what forbids
  smuggling precomputed advice into the initial state.
* `head : State → β ⊕ p.A` reads off a returned value or an exposed query.
* `update? : State × p.Idx → Option State` consumes a tagged answer, partially.

By `ofStep_step_eq_of_flat_eq` those three maps determine the machine, so this is
a constraint on the machine itself rather than on a lossy projection of it.

Nothing here constrains the machine's *behaviour*: a realization is admissible
machinery, and agreement with a program is the separate `Implements` predicate.
The two are combined by `IsRealizableBy`. -/
structure Realization (C : StepClass.{u, v}) [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq p.A] (bd : Boundary C p α β) where
  /-- The underlying machine. -/
  machine : DynComputation.{u} p α β
  /-- The chosen representation of the machine's hidden state. -/
  state : C.Str machine.State
  /-- Initialization is admissible. -/
  init_mem : C.Hom bd.input state machine.init
  /-- The one-step readout is admissible. -/
  head_mem : C.Hom state bd.head machine.head
  /-- The partial flattened transition is admissible. -/
  update_mem : C.Hom (bd.stateIdx state) (StepClass.HasOption.option state)
    machine.update?

/-! ## The realizability predicates -/

/-- `program` is `C`-realizable: some `C`-admissible machine implements it.

Resource bounds are deliberately not part of this predicate; see
`IsRealizableWithin` for the bounded form. -/
def IsRealizableBy (C : StepClass.{u, v}) [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq p.A] (bd : Boundary C p α β) (program : α → FreeM p β) : Prop :=
  ∃ R : Realization C bd, R.machine.Implements program

/-- `program` is `C`-realizable within the uniform query budget `k`: some
`C`-admissible machine implements it and resolves every answer branch within `k`
visible queries. -/
def IsRealizableWithin (C : StepClass.{u, v}) [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq p.A] (bd : Boundary C p α β) (program : α → FreeM p β)
    (k : ℕ) : Prop :=
  ∃ R : Realization C bd, R.machine.ImplementsWithin program k

section Basic

variable {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq p.A] {bd : Boundary C p α β} {program : α → FreeM p β}

/-- A bounded realization is in particular a realization. -/
theorem IsRealizableWithin.isRealizableBy {k : ℕ}
    (h : IsRealizableWithin C bd program k) : IsRealizableBy C bd program := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, ((implementsWithin_iff_implements_and_bound R.machine program k).mp hR).1⟩

/-- A bounded realization certifies that the program itself fits the budget: the
resource bound is a property of the syntax, extracted from the machine. -/
theorem IsRealizableWithin.isTotalRollBound {k : ℕ}
    (h : IsRealizableWithin C bd program k) (input : α) :
    (program input).IsTotalRollBound k := by
  obtain ⟨R, hR⟩ := h
  exact ((implementsWithin_iff_implements_and_bound R.machine program k).mp hR).2 input

/-- Bounded realizability is monotone in the query budget. -/
theorem IsRealizableWithin.mono {j k : ℕ}
    (h : IsRealizableWithin C bd program j) (hjk : j ≤ k) :
    IsRealizableWithin C bd program k := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, hR.mono hjk⟩

/-- Realizability only depends on the program family through its values. -/
theorem IsRealizableBy.congr {program' : α → FreeM p β}
    (h : IsRealizableBy C bd program) (hprog : ∀ input, program input = program' input) :
    IsRealizableBy C bd program' := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, fun input => (hprog input) ▸ hR input⟩

/-- Bounded realizability only depends on the program family through its
values. -/
theorem IsRealizableWithin.congr {program' : α → FreeM p β} {k : ℕ}
    (h : IsRealizableWithin C bd program k)
    (hprog : ∀ input, program input = program' input) :
    IsRealizableWithin C bd program' k := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, fun input => (hprog input) ▸ hR input⟩

end Basic

end DynSystem.DynComputation

end PFunctor
