/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import PolyFunCslib.Backend
public import ToCslib.Computability.BitEncoding

/-!
# Non-uniform P/poly realizations backed by cslib machines

This module connects the parameter-indexed single-tape certificates in
`ToCslib` to PolyFun returning dynamical computations. It deliberately uses
PolyFun's compositional first-order boundary: initialization, the combined
return-or-query `head`, and the enabled partial transition `update?`.

The predicate is named `IsPPolyBy`, rather than unqualified polynomial time or
PPT. Its witness contains one cslib machine for each security parameter and a
single polynomial bound on machine descriptions, so it is explicitly
non-uniform. Boundary encodings remain pinned parameters and are never chosen
existentially by the predicate.
-/

@[expose] public section

universe u

namespace PFunctor
namespace CslibPPoly

open ToCslib.Computability
open DynSystem.DynComputation

variable {p : ℕ → PFunctor.{u, u}} {input output : ℕ → Type u}

/-! ## Pinned parameterized boundaries -/

/-- Fixed binary representations for a parameterized program family and its
polynomial-functor interface. -/
structure Boundary (p : ℕ → PFunctor.{u, u}) (input output : ℕ → Type u) where
  /-- Fixed-width input representation. -/
  input : BitEncFam input
  /-- Fixed-width returned-value representation. -/
  output : BitEncFam output
  /-- Fixed-width representation of query positions. -/
  position : BitEncFam fun n ↦ (p n).A
  /-- Fixed-width representation of dependent position/answer pairs. -/
  index : BitEncFam fun n ↦ (p n).Idx

namespace Boundary

variable {nextOutput : ℕ → Type u}

/-- Variable-width representation of the combined return-or-query head. -/
noncomputable def head (bd : Boundary p input output) :
    StrEncFam fun n ↦ output n ⊕ (p n).A :=
  bd.output.toStrEncFam.sum bd.position.toStrEncFam

/-- Specialize a parameterized pinned boundary to the generic PolyFun
quantitative boundary at one security parameter. -/
noncomputable def toGeneric (bd : Boundary p input output) (n : ℕ) :
    DynSystem.DynComputation.Boundary CslibBackend.encodingStepClass
      (p n) (input n) (output n) where
  input := bd.input.enc n
  out := bd.output.enc n
  pos := bd.position.enc n
  idx := bd.index.enc n

/-- Replace the input representation. -/
def withInput (bd : Boundary p input output) (encoding : BitEncFam nextOutput) :
    Boundary p nextOutput output :=
  ⟨encoding, bd.output, bd.position, bd.index⟩

/-- Replace the output representation. -/
def withOutput (bd : Boundary p input output) (encoding : BitEncFam nextOutput) :
    Boundary p input nextOutput :=
  ⟨bd.input, encoding, bd.position, bd.index⟩

@[simp] theorem withInput_input (bd : Boundary p input output)
    (encoding : BitEncFam nextOutput) : (bd.withInput encoding).input = encoding := rfl

@[simp] theorem withOutput_output (bd : Boundary p input output)
    (encoding : BitEncFam nextOutput) : (bd.withOutput encoding).output = encoding := rfl

@[simp] theorem withInput_head (bd : Boundary p input output)
    (encoding : BitEncFam nextOutput) : (bd.withInput encoding).head = bd.head := rfl

@[simp] theorem withOutput_input (bd : Boundary p input output)
    (encoding : BitEncFam nextOutput) : (bd.withOutput encoding).input = bd.input := rfl

end Boundary

/-! ## Program progress -/

/-- Every query in a finite free program has at least one typed answer, and the
same holds recursively on every answer branch. This is separate from a
branchwise query bound: universal branch obligations are vacuous at a query
whose answer type is empty. -/
def ProgramProgress {p : PFunctor.{u, u}} {result : Type u} : FreeM p result → Prop
  | .pure _ => True
  | .liftBind position next =>
      Nonempty (p.B position) ∧ ∀ direction, ProgramProgress (next direction)

theorem programProgress_pure {p : PFunctor.{u, u}} {result : Type u}
    (value : result) : ProgramProgress (FreeM.pure (P := p) value) :=
  trivial

theorem programProgress_liftBind {p : PFunctor.{u, u}} {result : Type u}
    (position : p.A) (next : p.B position → FreeM p result) :
    ProgramProgress (FreeM.liftBind position next) ↔
      Nonempty (p.B position) ∧ ∀ direction, ProgramProgress (next direction) :=
  Iff.rfl

/-- Mapping returned values preserves the reachable query tree and hence
program progress. -/
theorem ProgramProgress.map {p : PFunctor.{u, u}} {source target : Type u}
    {program : FreeM p source} (progress : ProgramProgress program)
    (function : source → target) : ProgramProgress (FreeM.map function program) := by
  induction program with
  | pure value => trivial
  | lift_bind position next induction =>
      exact ⟨progress.1, fun direction ↦ induction direction (progress.2 direction)⟩

/-! ## Machine families -/

variable [∀ n, DecidableEq (p n).A]

/-- A family of PolyFun machines whose three compositional step maps are
implemented by cslib single-tape machines with uniform time and description
bounds. The polynomial `rounds` bounds visible interactions. -/
structure Realization (bd : Boundary p input output) where
  /-- One returning dynamical computation per security parameter. -/
  machine : (n : ℕ) → DynSystem.DynComputation (p n) (input n) (output n)
  /-- Uniform polynomial bound on visible interaction rounds. -/
  rounds : Polynomial ℕ
  /-- Polynomially length-bounded representation of hidden states. -/
  state : StrEncFam fun n ↦ (machine n).State
  /-- Cslib code for initialization. -/
  initCode : EncPolyTimeFam bd.input.enc state.enc fun n ↦ (machine n).init
  /-- Cslib code for the combined returned-value-or-query head. -/
  headCode : EncPolyTimeFam state.enc bd.head.enc fun n ↦ (machine n).head
  /-- Cslib code for the enabled partial transition. -/
  updateCode : EncPolyTimeFam (state.pairVar bd.index).enc state.option.enc
    fun n ↦ (machine n).update?

namespace Realization

variable {bd : Boundary p input output}

/-- One member of the family as an ordinary generic quantitative PolyFun
realization. This is the canonical bridge through which trace, progress,
traffic, peak-size, and closure APIs are consumed. -/
noncomputable def toQuantitative (realization : Realization bd) (n : ℕ) :
    DynSystem.DynComputation.QuantitativeRealization CslibBackend.quantitative
      (bd.toGeneric n) where
  machine := realization.machine n
  state := realization.state.enc n
  initCode := realization.initCode.wit n
  headCode := realization.headCode.wit n
  updateCode := (realization.updateCode.wit n).recode id
    (realization.machine n).update? (fun _ ↦ rfl) (fun step ↦ by
      change _ = realization.state.option.enc n ((realization.machine n).update? step)
      cases value : (realization.machine n).update? step <;> rfl)

/-- Initialization time after substituting the canonical input-width bound. -/
noncomputable def initTime (realization : Realization bd) : Polynomial ℕ :=
  realization.initCode.time.comp (.X + bd.input.widBound)

/-- Observation time after substituting the hidden-state length bound. -/
noncomputable def headTime (realization : Realization bd) : Polynomial ℕ :=
  realization.headCode.time.comp (.X + realization.state.bound)

/-- Enabled-transition time after substituting the state and index length bounds. -/
noncomputable def updateTime (realization : Realization bd) : Polynomial ℕ :=
  realization.updateCode.time.comp
    (.X + realization.state.bound + bd.index.widBound)

/-- Additive worst-case time for initialization, at most `rounds` visible updates,
and one observation before every update plus the final observation. This avoids the
invalid shortcut of composing a step-machine polynomial `rounds` times. -/
noncomputable def totalTime (realization : Realization bd) : Polynomial ℕ :=
  realization.initTime + (realization.rounds + 1) * realization.headTime +
    realization.rounds * realization.updateTime

/-- One polynomial dominating all machine descriptions carried by the family. -/
noncomputable def descriptionSize (realization : Realization bd) : Polynomial ℕ :=
  realization.initCode.size + realization.headCode.size + realization.updateCode.size

/-- The parameter-substituted initialization polynomial bounds the actual cslib
  machine on every pinned encoded input. -/
theorem initTime_le (realization : Realization bd) (n : ℕ) (value : input n) :
    ((realization.initCode.wit n).time).eval (bd.input.enc n value).length ≤
      realization.initTime.eval n := by
  refine (realization.initCode.time_le n _).trans ?_
  rw [initTime, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X]
  rw [bd.input.len_eq]
  exact Polynomial.eval_le_eval (Nat.add_le_add_left (bd.input.wid_le n) n)

/-- The parameter-substituted observation polynomial bounds every hidden state. -/
theorem headTime_le (realization : Realization bd) (n : ℕ)
    (state : (realization.machine n).State) :
    ((realization.headCode.wit n).time).eval (realization.state.enc n state).length ≤
      realization.headTime.eval n := by
  refine (realization.headCode.time_le n _).trans ?_
  rw [headTime, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X]
  exact Polynomial.eval_le_eval (Nat.add_le_add_left (realization.state.len_le n state) n)

/-- The parameter-substituted transition polynomial bounds every flattened index,
including mismatched tags on which `update?` is allowed to return `none`. -/
theorem updateTime_le (realization : Realization bd) (n : ℕ)
    (step : (realization.machine n).State × (p n).Idx) :
    ((realization.updateCode.wit n).time).eval
        ((realization.state.pairVar bd.index).enc n step).length ≤
      realization.updateTime.eval n := by
  refine (realization.updateCode.time_le n _).trans ?_
  rw [updateTime, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X]
  apply Polynomial.eval_le_eval
  simp only [StrEncFam.pairVar_enc, List.length_append]
  rw [bd.index.len_eq]
  have stateLength := realization.state.len_le n step.1
  have indexWidth := bd.index.wid_le n
  omega

/-! ## Generic pathwise resource accounting -/

/-- The standard PolyFun quantitative trace for one member of the family. This
alias deliberately exposes the generic trace API rather than maintaining a
backend-specific parallel hierarchy. -/
abbrev ExecutionTrace (realization : Realization bd) (n : ℕ) :=
  (realization.toQuantitative n).ExecutionTrace

variable {n : ℕ}

/-- The generic trace's cslib time-envelope charges, including its final head
observation, are bounded by one observation per state and one enabled update per
visible transition. -/
theorem certifiedTimeCharge_le (realization : Realization bd)
    {start finish : (realization.machine n).State}
    (trace : DynSystem.DynComputation.QuantitativeRealization.ExecutionTrace
      (realization.toQuantitative n) start finish) :
    trace.cost.work +
        CslibBackend.quantitative.cost
          (realization.toQuantitative n).headCode finish ≤
      (trace.length + 1) * realization.headTime.eval n +
      trace.length * realization.updateTime.eval n := by
  apply CslibBackend.traceWork_add_finalHead_le
  · intro state
    change ((realization.headCode.wit n).time).eval
      (realization.state.enc n state).length ≤ realization.headTime.eval n
    exact realization.headTime_le n state
  · intro step
    change ((realization.updateCode.wit n).time).eval
      ((realization.state.pairVar bd.index).enc n step).length ≤
        realization.updateTime.eval n
    exact realization.updateTime_le n step

/-- The work component of PolyFun's generic `executionCost` is bounded by the
family's declared total-time polynomial on every prefix within the round budget.
The backend work metric is the cslib witness's certified time envelope. -/
theorem executionWork_le_totalTime (realization : Realization bd) (value : input n)
    {finish : (realization.machine n).State}
    (trace : ExecutionTrace realization n ((realization.machine n).init value) finish)
    (roundBound : trace.length ≤ realization.rounds.eval n) :
    ((realization.toQuantitative n).executionCost value trace).work ≤
      realization.totalTime.eval n := by
  have initBound := realization.initTime_le n value
  have traceBound := realization.certifiedTimeCharge_le trace
  change trace.cost.work +
        ((realization.headCode.wit n).time).eval
          (realization.state.enc n finish).length ≤
      (trace.length + 1) * realization.headTime.eval n +
        trace.length * realization.updateTime.eval n at traceBound
  have headFactor : trace.length + 1 ≤ realization.rounds.eval n + 1 := by omega
  have headBound := Nat.mul_le_mul_right (realization.headTime.eval n) headFactor
  have updateBound := Nat.mul_le_mul_right (realization.updateTime.eval n) roundBound
  change ((realization.initCode.wit n).time).eval (bd.input.enc n value).length +
      trace.cost.work +
        ((realization.headCode.wit n).time).eval
          (realization.state.enc n finish).length ≤ realization.totalTime.eval n
  rw [Realization.totalTime]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  omega

/-- Precompose the input of a realization with a supplied cslib machine family. -/
noncomputable def precomp {nextInput : ℕ → Type u} (realization : Realization bd)
    (function : (n : ℕ) → nextInput n → input n) (encoding : BitEncFam nextInput)
    (code : EncPolyTimeFam encoding.enc bd.input.enc function) :
    Realization (bd.withInput encoding) where
  machine n := (realization.machine n).setInit fun value ↦
    (realization.machine n).init (function n value)
  rounds := realization.rounds
  state := realization.state
  initCode := (code.comp realization.initCode).copy _ fun _ _ ↦ rfl
  headCode := realization.headCode.copy _ fun n state ↦ by
    exact (head_setInit (realization.machine n)
      (fun value ↦ (realization.machine n).init (function n value)) state).symm
  updateCode := realization.updateCode.copy _ fun n step ↦ by
    exact (update?_setInit (realization.machine n)
      (fun value ↦ (realization.machine n).init (function n value)) step).symm

/-- Postcompose returned values with supplied code for the induced head map. -/
noncomputable def mapResult {nextOutput : ℕ → Type u} (realization : Realization bd)
    (function : (n : ℕ) → output n → nextOutput n) (encoding : BitEncFam nextOutput)
    (headMapCode : EncPolyTimeFam bd.head.enc (bd.withOutput encoding).head.enc
      fun n ↦ Sum.map (function n) id) : Realization (bd.withOutput encoding) where
  machine n := (realization.machine n).mapResult (function n)
  rounds := realization.rounds
  state := realization.state
  initCode := realization.initCode.copy _ fun _ _ ↦ rfl
  headCode := (realization.headCode.comp headMapCode).copy _ fun n state ↦ by
    simpa only [Function.comp_apply] using
      (head_mapResult (realization.machine n) (function n) state).symm
  updateCode := realization.updateCode.copy _ fun n step ↦ by
    exact (update?_mapResult (realization.machine n) (function n) step).symm

end Realization

/-! ## Program witnesses and predicate -/

variable {bd : Boundary p input output}

/-- Agreement of a cslib-backed realization with a parameterized free-program
family at its polynomial round budget. -/
def Realization.Implements (realization : Realization bd)
    (program : (n : ℕ) → input n → FreeM (p n) (output n)) : Prop :=
  ∀ n, (realization.machine n).ImplementsWithin (program n) (realization.rounds.eval n)

/-- A non-uniform P/poly witness for a parameterized free-program family. -/
structure Witness (bd : Boundary p input output)
    (program : (n : ℕ) → input n → FreeM (p n) (output n)) where
  /-- The cslib-backed machine family. -/
  realization : Realization bd
  /-- The machines implement the programs within the polynomial round bound. -/
  implements : realization.Implements program
  /-- Every syntactically reachable query has a possible typed response. -/
  progress : ∀ n value, ProgramProgress (program n value)

/-- Backend-relative non-uniform P/poly realizability at a pinned boundary. -/
def IsPPolyBy (bd : Boundary p input output)
    (program : (n : ℕ) → input n → FreeM (p n) (output n)) : Prop :=
  Nonempty (Witness bd program)

namespace Witness

variable {bd : Boundary p input output}
  {program : (n : ℕ) → input n → FreeM (p n) (output n)}

/-- Every certified computation resolves along every typed answer path within
the witness round bound. -/
theorem resolvesIn (witness : Witness bd program) (n : ℕ) (value : input n) :
    (witness.realization.machine n).ResolvesIn
      (witness.realization.rounds.eval n) ((witness.realization.machine n).init value) :=
  (witness.implements n).resolvesIn value

/-- The implemented syntax itself has the polynomial total interaction bound. -/
theorem isTotalRollBound (witness : Witness bd program) (n : ℕ) (value : input n) :
    (program n value).IsTotalRollBound (witness.realization.rounds.eval n) :=
  ((implementsWithin_iff_implements_and_bound
    (witness.realization.machine n) (program n)
      (witness.realization.rounds.eval n)).mp (witness.implements n)).2 value

/-- A realization of an immediately returning program exposes that return at
its initial state. This is the bridge from PolyFun's coinductive semantics to
the first-order `headCode` consumed by machine-counting arguments. -/
theorem head_init_eq_of_pure {function : (n : ℕ) → input n → output n}
    (witness : Witness bd (fun n value ↦ FreeM.pure (function n value)))
    (n : ℕ) (value : input n) :
    (witness.realization.machine n).head
        ((witness.realization.machine n).init value) = Sum.inl (function n value) := by
  have implementation :=
    ((implementsWithin_iff_implements_and_bound
      (witness.realization.machine n) (fun value ↦ FreeM.pure (function n value))
        (witness.realization.rounds.eval n)).mp (witness.implements n)).1 value
  have firstStep := congrArg Resumption.dest implementation
  rw [DynSystem.DynComputation.dest_denote] at firstStep
  change Sum.map (fun result ↦ result)
      ((p n).map (witness.realization.machine n).toDynSystem.behavior)
        ((witness.realization.machine n).view
          ((witness.realization.machine n).init value)) =
      Sum.inl (function n value) at firstStep
  cases viewEquation : (witness.realization.machine n).view
      ((witness.realization.machine n).init value) with
  | inl result =>
      rw [viewEquation] at firstStep
      simp only [Sum.map_inl, Sum.inl.injEq] at firstStep
      simpa [firstStep] using
        (witness.realization.machine n).head_eq_inl_of_view viewEquation
  | inr query =>
      rw [viewEquation] at firstStep
      simp at firstStep

end Witness

namespace IsPPolyBy

variable {bd : Boundary p input output}
  {program program' : (n : ℕ) → input n → FreeM (p n) (output n)}

/-- Transport a P/poly certificate along pointwise program equality. -/
theorem congr (equality : ∀ n value, program n value = program' n value)
    (certificate : IsPPolyBy bd program) : IsPPolyBy bd program' := by
  obtain ⟨witness⟩ := certificate
  exact ⟨{
    realization := witness.realization
    implements := fun n value ↦ by
      rw [← equality n value]
      exact witness.implements n value
    progress := fun n value ↦ by
      rw [← equality n value]
      exact witness.progress n value }⟩

/-- P/poly is closed under input precomposition when the input map carries a
cslib family certificate. -/
theorem precomp {nextInput : ℕ → Type u} (certificate : IsPPolyBy bd program)
    (function : (n : ℕ) → nextInput n → input n) (encoding : BitEncFam nextInput)
    (code : EncPolyTimeFam encoding.enc bd.input.enc function) :
    IsPPolyBy (bd.withInput encoding) fun n value ↦ program n (function n value) := by
  obtain ⟨witness⟩ := certificate
  refine ⟨{
    realization := witness.realization.precomp function encoding code
    implements := fun n value ↦ ?_
    progress := fun n value ↦ witness.progress n (function n value) }⟩
  change ((witness.realization.machine n).setInit fun value ↦
      (witness.realization.machine n).init (function n value)).unroll
        (witness.realization.rounds.eval n)
        ((witness.realization.machine n).init (function n value)) = _
  rw [unroll_setInit]
  exact witness.implements n (function n value)

/-- P/poly is closed under result mapping when the induced head map carries a
cslib family certificate. -/
theorem mapResult {nextOutput : ℕ → Type u} (certificate : IsPPolyBy bd program)
    (function : (n : ℕ) → output n → nextOutput n) (encoding : BitEncFam nextOutput)
    (headMapCode : EncPolyTimeFam bd.head.enc (bd.withOutput encoding).head.enc
      fun n ↦ Sum.map (function n) id) :
    IsPPolyBy (bd.withOutput encoding) fun n value ↦
      FreeM.map (function n) (program n value) := by
  obtain ⟨witness⟩ := certificate
  refine ⟨{
    realization := witness.realization.mapResult function encoding headMapCode
    implements := fun n value ↦ ?_
    progress := fun n value ↦
      (witness.progress n value).map (function n) }⟩
  have implementation := witness.implements n value
  change (witness.realization.machine n).unroll
      (witness.realization.rounds.eval n) ((witness.realization.machine n).init value) = _
    at implementation
  change ((witness.realization.machine n).mapResult (function n)).unroll
      (witness.realization.rounds.eval n) ((witness.realization.machine n).init value) = _
  rw [unroll_mapResult, implementation, ← FreeM.comp_map, ← FreeM.comp_map]
  rfl

end IsPPolyBy

end CslibPPoly
end PFunctor
