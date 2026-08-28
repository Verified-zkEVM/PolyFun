/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.BoundedClosure
public import PolyFun.Realizability.Quantitative.Polynomial

/-!
# Resource contracts for quantitative realizations

This module gives `ExecutionCost` an inspectable second-order polynomial bound and describes the
response-size environments under which an open quantitative realization runs. The definitions are
generic in a polynomial-functor interface and a quantitative backend. They do not select a machine
model or assert a complexity class.

`PolynomialRunBound` concerns one already chosen realization and is deliberately independent of
semantic `FreeM` syntax. `PolynomialProgramWitness` adds implementation and returned-output
recovery as a separate layer. Local pure, ranked-potential, and sequential-composition
certificates construct these bounds without replacing backend costs by an asserted meter.
-/

public section

universe u v w x y

namespace PFunctor

/-! ## Execution-cost polynomials -/

/-- A second-order polynomial upper bound for every component of `ExecutionCost`. -/
structure ExecutionCostPolynomial (label : Type x) where
  /-- Backend-relative local work. -/
  work : _root_.Complexity.SecondOrderPolynomial label
  /-- Number of visible interactions. -/
  queries : _root_.Complexity.SecondOrderPolynomial label
  /-- Total encoded position-response traffic. -/
  traffic : _root_.Complexity.SecondOrderPolynomial label
  /-- Peak encoded hidden-state size. -/
  peakStateSize : _root_.Complexity.SecondOrderPolynomial label
  /-- Peak encoded one-step readout size. -/
  peakHeadSize : _root_.Complexity.SecondOrderPolynomial label
  deriving DecidableEq, Repr

namespace ExecutionCostPolynomial

variable {label : Type x}

/-- Regard a first-order polynomial as one which does not inspect its length environment. -/
def ofFirstOrder (bound : _root_.Complexity.FirstOrderPolynomial) :
    _root_.Complexity.SecondOrderPolynomial label :=
  bound.reindex PEmpty.elim

@[simp]
theorem eval_ofFirstOrder (bound : _root_.Complexity.FirstOrderPolynomial)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (ofFirstOrder bound : _root_.Complexity.SecondOrderPolynomial label).eval length inputSize =
      bound.eval inputSize := by
  unfold ofFirstOrder
  rw [_root_.Complexity.SecondOrderPolynomial.eval_reindex]
  change _ = _root_.Complexity.SecondOrderPolynomial.eval PEmpty.elim inputSize bound
  congr 1
  funext interface
  exact interface.elim

/-- Evaluate every resource component at an input size and length environment. -/
def eval (bound : ExecutionCostPolynomial label) (length : label → ℕ → ℕ)
    (inputSize : ℕ) : ExecutionCost where
  work := bound.work.eval length inputSize
  queries := bound.queries.eval length inputSize
  traffic := bound.traffic.eval length inputSize
  peakStateSize := bound.peakStateSize.eval length inputSize
  peakHeadSize := bound.peakHeadSize.eval length inputSize

@[simp] theorem eval_work (bound : ExecutionCostPolynomial label) (length : label → ℕ → ℕ)
    (inputSize : ℕ) : (bound.eval length inputSize).work = bound.work.eval length inputSize := by
  simp [eval]

@[simp] theorem eval_queries (bound : ExecutionCostPolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (bound.eval length inputSize).queries = bound.queries.eval length inputSize := by
  simp [eval]

@[simp] theorem eval_traffic (bound : ExecutionCostPolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (bound.eval length inputSize).traffic = bound.traffic.eval length inputSize := by
  simp [eval]

@[simp] theorem eval_peakStateSize (bound : ExecutionCostPolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (bound.eval length inputSize).peakStateSize =
      bound.peakStateSize.eval length inputSize := by
  simp [eval]

@[simp] theorem eval_peakHeadSize (bound : ExecutionCostPolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (bound.eval length inputSize).peakHeadSize =
      bound.peakHeadSize.eval length inputSize := by
  simp [eval]

/-- A constant execution-cost bound. -/
def const (cost : ExecutionCost) : ExecutionCostPolynomial label where
  work := .const cost.work
  queries := .const cost.queries
  traffic := .const cost.traffic
  peakStateSize := .const cost.peakStateSize
  peakHeadSize := .const cost.peakHeadSize

/-- A conservative sequential sum of two execution-cost bounds.

The additive components add exactly. Polynomial addition upper-bounds the `max` used by the two
peak components. -/
def add (left right : ExecutionCostPolynomial label) : ExecutionCostPolynomial label where
  work := .add left.work right.work
  queries := .add left.queries right.queries
  traffic := .add left.traffic right.traffic
  peakStateSize := .add left.peakStateSize right.peakStateSize
  peakHeadSize := .add left.peakHeadSize right.peakHeadSize

instance : Add (ExecutionCostPolynomial label) := ⟨add⟩

/-- Replace the base input-size variable in every component. -/
def comp (bound : ExecutionCostPolynomial label)
    (inputBound : _root_.Complexity.SecondOrderPolynomial label) :
    ExecutionCostPolynomial label where
  work := bound.work.comp inputBound
  queries := bound.queries.comp inputBound
  traffic := bound.traffic.comp inputBound
  peakStateSize := bound.peakStateSize.comp inputBound
  peakHeadSize := bound.peakHeadSize.comp inputBound

/-- Relabel every length-function symbol in an execution-cost bound. -/
def reindex {target : Type y} (bound : ExecutionCostPolynomial label) (map : label → target) :
    ExecutionCostPolynomial target where
  work := bound.work.reindex map
  queries := bound.queries.reindex map
  traffic := bound.traffic.reindex map
  peakStateSize := bound.peakStateSize.reindex map
  peakHeadSize := bound.peakHeadSize.reindex map

/-- Substitute a second-order transformer for every source length-function symbol. -/
def subst {target : Type y} (bound : ExecutionCostPolynomial label)
    (replacement : label → _root_.Complexity.SecondOrderPolynomial target) :
    ExecutionCostPolynomial target where
  work := bound.work.subst replacement
  queries := bound.queries.subst replacement
  traffic := bound.traffic.subst replacement
  peakStateSize := bound.peakStateSize.subst replacement
  peakHeadSize := bound.peakHeadSize.subst replacement

@[simp]
theorem eval_const (cost : ExecutionCost) (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (const cost : ExecutionCostPolynomial label).eval length inputSize = cost :=
  by
    ext <;> simp [const, eval]

@[simp]
theorem eval_comp (bound : ExecutionCostPolynomial label)
    (inputBound : _root_.Complexity.SecondOrderPolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (bound.comp inputBound).eval length inputSize =
      bound.eval length (inputBound.eval length inputSize) := by
  ext <;> simp [eval, comp]

@[simp]
theorem eval_reindex {target : Type y} (bound : ExecutionCostPolynomial label)
    (map : label → target) (length : target → ℕ → ℕ) (inputSize : ℕ) :
    (bound.reindex map).eval length inputSize =
      bound.eval (fun symbol ↦ length (map symbol)) inputSize := by
  ext <;> simp [eval, reindex]

@[simp]
theorem eval_subst {target : Type y} (bound : ExecutionCostPolynomial label)
    (replacement : label → _root_.Complexity.SecondOrderPolynomial target)
    (length : target → ℕ → ℕ) (inputSize : ℕ) :
    (bound.subst replacement).eval length inputSize =
      bound.eval (fun symbol size ↦ (replacement symbol).eval length size) inputSize := by
  ext <;> simp [eval, subst]

/-- Sequentially accumulated costs fit the conservative polynomial sum. -/
theorem add_eval_le_eval_add (left right : ExecutionCostPolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    left.eval length inputSize + right.eval length inputSize ≤
      (left + right).eval length inputSize := by
  rw [ExecutionCost.le_iff]
  exact ⟨le_rfl, le_rfl, le_rfl, max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _),
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)⟩

/-- Evaluation is monotone in encoded input size when every length function is monotone. -/
theorem eval_mono_input (bound : ExecutionCostPolynomial label) {length : label → ℕ → ℕ}
    (hLength : _root_.Complexity.SecondOrderPolynomial.MonotoneLengths length)
    {smaller larger : ℕ} (hle : smaller ≤ larger) :
    bound.eval length smaller ≤ bound.eval length larger := by
  rw [ExecutionCost.le_iff]
  exact ⟨bound.work.eval_monotone hLength hle, bound.queries.eval_monotone hLength hle,
    bound.traffic.eval_monotone hLength hle, bound.peakStateSize.eval_monotone hLength hle,
    bound.peakHeadSize.eval_monotone hLength hle⟩

/-- Evaluation is monotone under pointwise enlargement of monotone length functions. -/
theorem eval_mono_lengths (bound : ExecutionCostPolynomial label)
    {smaller larger : label → ℕ → ℕ}
    (hLarger : _root_.Complexity.SecondOrderPolynomial.MonotoneLengths larger)
    (hle : ∀ symbol size, smaller symbol size ≤ larger symbol size) (inputSize : ℕ) :
    bound.eval smaller inputSize ≤ bound.eval larger inputSize := by
  rw [ExecutionCost.le_iff]
  exact ⟨bound.work.eval_mono_lengths hLarger hle inputSize,
    bound.queries.eval_mono_lengths hLarger hle inputSize,
    bound.traffic.eval_mono_lengths hLarger hle inputSize,
    bound.peakStateSize.eval_mono_lengths hLarger hle inputSize,
    bound.peakHeadSize.eval_mono_lengths hLarger hle inputSize⟩

end ExecutionCostPolynomial

namespace DynSystem.DynComputation

/-! ## Response-size environments -/

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  {Q : QuantitativeStepClass.{u, v, w} C} {label : Type x}

/-- The response-length function exposed for each labelled interface. -/
inductive ResponseModulus (label : Type x) where
  /-- Encoded dependent-response length as a function of encoded position length. -/
  | responseSize (interface : label)
  deriving DecidableEq, Repr

/-- One family of admitted responses and monotone encoded-response size envelopes. -/
structure ResponseResourceModel (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C p) (labelOf : p.A → label) where
  /-- Replies admitted at each typed position. -/
  allows : ∀ position : p.A, p.B position → Prop
  /-- Encoded response length for each labelled interface. -/
  responseSize : label → ℕ → ℕ
  /-- Every response-size envelope is monotone in encoded position size. -/
  responseSize_monotone : ∀ interface, Monotone (responseSize interface)
  /-- Every admitted dependent response fits its selected envelope. -/
  responseSize_le : ∀ (position : p.A) (answer : p.B position), allows position answer →
    Q.size interface.idx ⟨position, answer⟩ ≤
      responseSize (labelOf position) (Q.size interface.pos position)

namespace ResponseResourceModel

variable {interface : InterfaceBoundary C p} {labelOf : p.A → label}
  (model : ResponseResourceModel Q interface labelOf)

/-- Expose a response model as the length environment of a second-order polynomial. -/
def modulus : ResponseModulus label → ℕ → ℕ
  | .responseSize interface => model.responseSize interface

@[simp]
theorem modulus_responseSize (interface : label) (size : ℕ) :
    model.modulus (.responseSize interface) size = model.responseSize interface size := by
  simp [modulus]

/-- Every length function exposed by a response model is monotone. -/
theorem modulus_monotone :
    _root_.Complexity.SecondOrderPolynomial.MonotoneLengths model.modulus := by
  intro symbol
  cases symbol with
  | responseSize interface => exact model.responseSize_monotone interface

end ResponseResourceModel

/-- A pinned position labelling and a nonempty collection of admissible response models. -/
structure ResponseResourceContract (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C p) (label : Type x) where
  /-- Label assigned to each interface position. -/
  labelOf : p.A → label
  /-- Response environments admitted by the contract. -/
  admissible : ResponseResourceModel Q interface labelOf → Prop
  /-- At least one global finite response envelope satisfies the contract. -/
  model_nonempty : ∃ model, admissible model

namespace ResponseResourceContract

variable {interface : InterfaceBoundary C p}
  (contract : ResponseResourceContract Q interface label)

/-- Response environments carrying evidence that they satisfy a contract. -/
abbrev Model := { model : ResponseResourceModel Q interface contract.labelOf //
  contract.admissible model }

namespace Model

variable {contract : ResponseResourceContract Q interface label}

/-- Forget contract admissibility evidence. -/
abbrev resourceModel (model : contract.Model) :
    ResponseResourceModel Q interface contract.labelOf :=
  model.1

/-- The second-order length environment supplied by a compatible response model. -/
abbrev modulus (model : contract.Model) : ResponseModulus label → ℕ → ℕ :=
  model.resourceModel.modulus

/-- Every compatible response model supplies monotone length functions. -/
theorem modulus_monotone (model : contract.Model) :
    _root_.Complexity.SecondOrderPolynomial.MonotoneLengths model.modulus :=
  model.resourceModel.modulus_monotone

end Model

end ResponseResourceContract

/-! ## Polynomial run and program witnesses -/

variable [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {input output : Type u} {bd : Boundary C p input output}

/-- A second-order polynomial bound on one already selected quantitative realization.

This structure contains no semantic `FreeM` program and no output-recovery policy. It can therefore
be reused when the same realization is related to syntax in more than one way. -/
structure PolynomialRunBound (R : QuantitativeRealization Q bd)
    (contract : ResponseResourceContract Q bd.interface label) where
  /-- One bound shared by every response model admitted by the contract. -/
  polynomial : ExecutionCostPolynomial (ResponseModulus label)
  /-- Every conforming finite prefix satisfies the shared bound. -/
  runsWithin : ∀ model : contract.Model,
    R.RunsWithinUnder model.resourceModel.allows fun value ↦
      polynomial.eval model.modulus (Q.size bd.input value)

namespace PolynomialRunBound

variable {R : QuantitativeRealization Q bd}
  {contract : ResponseResourceContract Q bd.interface label}

/-- The input-indexed execution bound selected by one compatible response model. -/
def bound (certificate : PolynomialRunBound R contract) (model : contract.Model) :
    input → ExecutionCost :=
  fun value ↦ certificate.polynomial.eval model.modulus (Q.size bd.input value)

/-- Restate the certificate's pathwise theorem through its named input-indexed bound. -/
theorem runsWithin_bound (certificate : PolynomialRunBound R contract)
    (model : contract.Model) :
    R.RunsWithinUnder model.resourceModel.allows (certificate.bound model) :=
  certificate.runsWithin model

end PolynomialRunBound

/-- A polynomially resource-bounded realization together with its semantic program witness.

The run bound remains a separate field so closure constructions can operate on it without
reproving implementation or returned-output recovery. -/
structure PolynomialProgramWitness (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C p input output)
    (contract : ResponseResourceContract Q bd.interface label)
    (program : input → FreeM p output) where
  /-- The selected executable realization. -/
  realization : QuantitativeRealization Q bd
  /-- Semantic agreement with the free interaction syntax. -/
  implements : realization.machine.Implements program
  /-- Returned payload size is recoverable from the charged tagged readout size. -/
  outputRecovery : Q.PolyOutputSizeRecovery bd
  /-- The realization's response-relative execution bound. -/
  runBound : PolynomialRunBound realization contract

namespace PolynomialProgramWitness

variable {contract : ResponseResourceContract Q bd.interface label}
  {program : input → FreeM p output}

/-- A second-order polynomial bounding returned payload size through the charged peak readout. -/
def outputSizePolynomial (witness : PolynomialProgramWitness Q bd contract program) :
    _root_.Complexity.SecondOrderPolynomial (ResponseModulus label) :=
  (ExecutionCostPolynomial.ofFirstOrder witness.outputRecovery.polynomial).comp
    witness.runBound.polynomial.peakHeadSize

@[simp]
theorem eval_outputSizePolynomial (witness : PolynomialProgramWitness Q bd contract program)
    (model : contract.Model) (value : input) :
    witness.outputSizePolynomial.eval model.modulus (Q.size bd.input value) =
      witness.outputRecovery.polynomial.eval
        (witness.runBound.bound model value).peakHeadSize := by
  simp [outputSizePolynomial, PolynomialRunBound.bound, ExecutionCostPolynomial.eval]

/-- Every return reached by a conforming execution has polynomially bounded encoded payload
size. -/
theorem returnedSize_le (witness : PolynomialProgramWitness Q bd contract program)
    (model : contract.Model) (value : input) {finish : witness.realization.machine.State}
    (trace : witness.realization.ExecutionTrace
      (witness.realization.machine.init value) finish)
    (htrace : trace.Conforms model.resourceModel.allows) (result : output)
    (view_eq : witness.realization.machine.view finish = Sum.inl result) :
    Q.size bd.out result ≤
      witness.outputSizePolynomial.eval model.modulus (Q.size bd.input value) := by
  have hreturned := witness.realization.returnedSize_le_peakHeadSize
    witness.outputRecovery.toOutputSizeRecovery value trace result view_eq
  have hcost := (witness.runBound.runsWithin_bound model).cost_le value trace htrace
  rw [witness.eval_outputSizePolynomial model value]
  exact hreturned.trans (witness.outputRecovery.polynomial.eval_monotone hcost.2.2.2.2)

/-- Transport a program witness across extensional equality of whole program families. -/
def congrProgram {program' : input → FreeM p output}
    (witness : PolynomialProgramWitness Q bd contract program)
    (hprogram : program = program') : PolynomialProgramWitness Q bd contract program' :=
  hprogram ▸ witness

/-- A program witness retains ordinary quantitative realizability. -/
theorem isQuantitativelyRealizableBy
    (witness : PolynomialProgramWitness Q bd contract program) :
    IsQuantitativelyRealizableBy Q bd program :=
  ⟨witness.realization, witness.implements⟩

/-- A program witness supplies the corresponding exact bound under each compatible model. -/
theorem isQuantitativelyRealizableWithinUnder
    (witness : PolynomialProgramWitness Q bd contract program) (model : contract.Model) :
    IsQuantitativelyRealizableWithinUnder Q bd model.resourceModel.allows program
      (witness.runBound.bound model) :=
  ⟨witness.realization, witness.implements, witness.runBound.runsWithin_bound model⟩

/-- If a response model admits every typed reply, the query component bounds the full free
syntax. -/
theorem isTotalRollBound (witness : PolynomialProgramWitness Q bd contract program)
    (model : contract.Model)
    (hAllows : ∀ position answer, model.resourceModel.allows position answer)
    (value : input) :
    (program value).IsTotalRollBound (witness.runBound.bound model value).queries := by
  have hAllowsEq : model.resourceModel.allows = fun _ _ ↦ True := by
    funext position answer
    apply propext
    exact ⟨fun _ ↦ trivial, fun _ ↦ hAllows position answer⟩
  have hRuns : witness.realization.RunsWithin (witness.runBound.bound model) := by
    change witness.realization.RunsWithinUnder (fun _ _ ↦ True) _
    rw [← hAllowsEq]
    exact witness.runBound.runsWithin_bound model
  exact hRuns.isTotalRollBound witness.implements value

end PolynomialProgramWitness

/-! ## Immediately returning programs -/

/-- Executable polynomial data for an immediately returning function.

The partial update realizer is required for a complete realization but needs no resource bound:
an immediately returning machine never invokes it. -/
structure PureResourceCertificate
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p input output)
    (function : input → output) where
  /-- Executable result computation with polynomial work and output growth. -/
  result : Q.PolyRealizer bd.input bd.out function
  /-- Executable resolved-state readout, including its sum tag. -/
  head : Q.PolyRealizer bd.out bd.head (Sum.inl : output → output ⊕ p.A)
  /-- Returned payload recovery from the tagged readout representation. -/
  outputRecovery : Q.PolyOutputSizeRecovery bd
  /-- Executable evidence for the unreachable partial update. -/
  update : Q.Realizer (bd.stateIdx bd.out) (StepClass.HasOption.option bd.out)
    (DynComputation.ofFn (p := p) function).update?

namespace PureResourceCertificate

variable {function : input → output}

/-- Construct pure-program data from one result realizer and an explicit polynomial model. -/
def ofPolyRealizer (model : Q.PolynomialModel)
    (result : Q.PolyRealizer bd.input bd.out function) :
    letI := model.kernel.cProd
    letI := model.kernel.cSum
    letI := model.kernel.cOption
    PureResourceCertificate Q bd function := by
  letI := model.category
  letI := model.kernel.cProd
  letI := model.kernel.cSum
  letI := model.kernel.cOption
  exact
    { result := result
      head := model.structural.inl bd.out bd.pos
      outputRecovery := model.structural.polyOutputSizeRecovery bd
      update :=
        (model.structural.optionNone (bd.stateIdx bd.out) bd.out).code.castFunction (by
          funext step
          exact (DynComputation.update?_of_view_return
            (DynComputation.ofFn (p := p) function)
            (DynComputation.view_ofFn function step.1) step.2).symm) }

/-- Assemble the quantitative realization of an immediately returning function. -/
def realization (certificate : PureResourceCertificate Q bd function) :
    QuantitativeRealization Q bd where
  machine := DynComputation.ofFn (p := p) function
  state := bd.out
  initCode := certificate.result.code
  headCode := certificate.head.code
  updateCode := certificate.update

/-- The first-order work and size certificates lifted into all execution-cost components. -/
def polynomial {resourceLabel : Type x}
    (certificate : PureResourceCertificate Q bd function) :
    ExecutionCostPolynomial resourceLabel where
  work := ExecutionCostPolynomial.ofFirstOrder <|
    _root_.Complexity.FirstOrderPolynomial.add certificate.result.work <|
      _root_.Complexity.FirstOrderPolynomial.comp certificate.head.work
        certificate.result.outputSize
  queries := .const 0
  traffic := .const 0
  peakStateSize := ExecutionCostPolynomial.ofFirstOrder certificate.result.outputSize
  peakHeadSize := ExecutionCostPolynomial.ofFirstOrder <|
    _root_.Complexity.FirstOrderPolynomial.comp certificate.head.outputSize
      certificate.result.outputSize

/-- The assembled realization implements the corresponding pure `FreeM` program. -/
theorem implements (certificate : PureResourceCertificate Q bd function) :
    certificate.realization.machine.Implements fun input ↦ FreeM.pure (function input) := by
  change (DynComputation.ofFn (p := p) function).Implements _
  intro input
  rw [denote_ofFn]
  simp

/-- Every finite prefix of the pure realization satisfies its derived polynomial bound. -/
theorem runsWithin {resourceLabel : Type x}
    (certificate : PureResourceCertificate Q bd function)
    (allows : ∀ position, p.B position → Prop)
    (length : resourceLabel → ℕ → ℕ) :
    certificate.realization.RunsWithinUnder allows fun input ↦
      (certificate.polynomial (resourceLabel := resourceLabel)).eval length
        (Q.size bd.input input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace _
    cases trace with
    | nil state =>
        rw [ExecutionCost.le_iff]
        simp only [QuantitativeRealization.executionCost,
          QuantitativeRealization.ExecutionTrace.cost,
          realization, polynomial, ExecutionCostPolynomial.eval,
          ExecutionCostPolynomial.eval_ofFirstOrder,
          _root_.Complexity.FirstOrderPolynomial.eval_add,
          _root_.Complexity.FirstOrderPolynomial.eval_comp,
          ExecutionCost.ofWork, ExecutionCost.observe, ExecutionCost.work_add,
          ExecutionCost.queries_add, ExecutionCost.traffic_add,
          ExecutionCost.peakStateSize_add, ExecutionCost.peakHeadSize_add,
          add_zero, Nat.max_zero, Nat.zero_max]
        refine ⟨?_, le_rfl, le_rfl, ?_, ?_⟩
        · exact Nat.add_le_add (certificate.result.work_le input) <|
            (certificate.head.work_le (function input)).trans <|
              certificate.head.work.eval_monotone (certificate.result.outputSize_le input)
        · exact certificate.result.outputSize_le input
        · exact (certificate.head.outputSize_le (function input)).trans <|
            certificate.head.outputSize.eval_monotone
              (certificate.result.outputSize_le input)
    | query view_eq direction tail =>
        change Sum.inl _ = Sum.inr _ at view_eq
        exact nomatch view_eq
  · intro input
    exact resolvesInUnder_return _ _ 0 _ _ (view_ofFn function (function input))
  · intro input state trace _ position next view_eq
    change Sum.inl state =
      Sum.inr (⟨position, next⟩ : p.Obj certificate.realization.machine.State)
      at view_eq
    exact nomatch view_eq

/-- Package a pure certificate as a run-only polynomial bound under any response contract. -/
def runBound (certificate : PureResourceCertificate Q bd function)
    (contract : ResponseResourceContract Q bd.interface label) :
    PolynomialRunBound certificate.realization contract where
  polynomial := certificate.polynomial
  runsWithin model := certificate.runsWithin model.resourceModel.allows model.modulus

/-- Package a pure certificate together with its semantic program witness. -/
def programWitness (certificate : PureResourceCertificate Q bd function)
    (contract : ResponseResourceContract Q bd.interface label) :
    PolynomialProgramWitness Q bd contract fun input ↦ FreeM.pure (function input) where
  realization := certificate.realization
  implements := certificate.implements
  outputRecovery := certificate.outputRecovery
  runBound := certificate.runBound contract

end PureResourceCertificate

/-! ## Ranked resource potentials -/

namespace RankedResource

/-- Cost of observing a state as the final state of an execution prefix. -/
def terminalCost (R : QuantitativeRealization Q bd) (state : R.machine.State) :
    ExecutionCost :=
  ExecutionCost.ofWork (Q.cost R.headCode state) +
    ExecutionCost.observe (Q.size R.state state) (Q.size bd.head (R.machine.head state))

/-- Cost contributed by one enabled position-response transition. -/
def queryStepCost (R : QuantitativeRealization Q bd) (state : R.machine.State)
    (position : p.A) (direction : p.B position) : ExecutionCost :=
  ExecutionCost.ofWork (Q.cost R.headCode state) +
    ExecutionCost.ofWork (Q.cost R.updateCode (state, ⟨position, direction⟩)) +
    ExecutionCost.observe (Q.size R.state state) (Q.size bd.head (R.machine.head state)) +
    ExecutionCost.query (Q.size bd.pos position) (Q.size bd.idx ⟨position, direction⟩)

@[simp]
theorem executionTrace_cost_query {R : QuantitativeRealization Q bd}
    {state : R.machine.State} {position : p.A} {next : p.B position → R.machine.State}
    {finish : R.machine.State}
    (view_eq : R.machine.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position) (tail : R.ExecutionTrace (next direction) finish) :
    (QuantitativeRealization.ExecutionTrace.query (R := R) view_eq direction tail).cost =
      queryStepCost R state position direction + tail.cost :=
  by
    simp [QuantitativeRealization.ExecutionTrace.cost, queryStepCost]

/-- Split prefix cost into initialization, transition cost, and the final observation. -/
theorem executionCost_eq_init_add_trace_add_terminal
    (R : QuantitativeRealization Q bd) (value : input) {finish : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init value) finish) :
    R.executionCost value trace =
      ExecutionCost.ofWork (Q.cost R.initCode value) + (trace.cost + terminalCost R finish) := by
  simp [QuantitativeRealization.executionCost, terminalCost, add_assoc]

/-- Local resource potentials combined with a decreasing, progress-bearing query rank. -/
structure PotentialCertificate (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) (bound : input → ExecutionCost) where
  /-- Backend-independent termination and non-vacuous progress evidence. -/
  toRankedRunCertificate : RankedRunCertificate R allows
  /-- Resource potential available at each hidden state. -/
  potential : R.machine.State → ExecutionCost
  /-- Stopping a prefix at any state fits that state's potential. -/
  terminal_le : ∀ state, terminalCost R state ≤ potential state
  /-- One admitted transition and the successor potential fit the source potential. -/
  query_le : ∀ {state : R.machine.State} {position : p.A}
    {next : p.B position → R.machine.State},
    R.machine.view state = Sum.inr ⟨position, next⟩ →
      ∀ direction, allows position direction →
        queryStepCost R state position direction + potential (next direction) ≤ potential state
  /-- Initialization work and the initial potential fit the advertised bound. -/
  init_le : ∀ value,
    ExecutionCost.ofWork (Q.cost R.initCode value) + potential (R.machine.init value) ≤
      bound value
  /-- The query component of the advertised bound dominates the initial rank. -/
  rank_init_le : ∀ value,
    toRankedRunCertificate.rank (R.machine.init value) ≤ (bound value).queries

namespace PotentialCertificate

variable {R : QuantitativeRealization Q bd}
  {allows : ∀ position, p.B position → Prop} {bound : input → ExecutionCost}

/-- Transition cost plus the final observation of a conforming trace fits its start potential. -/
theorem traceCost_add_terminal_le (certificate : PotentialCertificate R allows bound)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish)
    (htrace : trace.Conforms allows) :
    trace.cost + terminalCost R finish ≤ certificate.potential start := by
  induction trace with
  | nil state =>
      simpa only [QuantitativeRealization.ExecutionTrace.cost, zero_add] using
        certificate.terminal_le state
  | @query state position next finish view_eq direction tail ih =>
      calc
        (QuantitativeRealization.ExecutionTrace.query (R := R) view_eq direction tail).cost +
            terminalCost R finish =
            queryStepCost R state position direction +
              (tail.cost + terminalCost R finish) := by
          simp only [QuantitativeRealization.ExecutionTrace.cost, queryStepCost, add_assoc]
        _ ≤ queryStepCost R state position direction + certificate.potential (next direction) :=
          ExecutionCost.add_le_add le_rfl (ih htrace.2)
        _ ≤ certificate.potential state := certificate.query_le view_eq direction htrace.1

/-- The decreasing rank gives branchwise resolution from every hidden state. -/
theorem resolvesInUnder (certificate : PotentialCertificate R allows bound)
    (state : R.machine.State) :
    R.machine.ResolvesInUnder allows (certificate.toRankedRunCertificate.rank state) state :=
  certificate.toRankedRunCertificate.resolvesInUnder state

/-- A ranked local potential supplies the complete non-vacuous pathwise run bound. -/
theorem runsWithinUnder (certificate : PotentialCertificate R allows bound) :
    R.RunsWithinUnder allows bound := by
  apply certificate.toRankedRunCertificate.runsWithinUnder bound
  · intro value finish trace htrace
    rw [executionCost_eq_init_add_trace_add_terminal R value trace]
    exact (ExecutionCost.add_le_add le_rfl
      (certificate.traceCost_add_terminal_le trace htrace)).trans (certificate.init_le value)
  · exact certificate.rank_init_le

end PotentialCertificate

end RankedResource

/-! ## Ranked polynomial program certificates -/

/-- A polynomial program witness presented through model-relative ranked local potentials. -/
structure RankedResourceCertificate
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p input output)
    (contract : ResponseResourceContract Q bd.interface label)
    (program : input → FreeM p output) where
  /-- The selected executable realization. -/
  realization : QuantitativeRealization Q bd
  /-- Semantic agreement with the free interaction syntax. -/
  implements : realization.machine.Implements program
  /-- Returned payload recovery from the charged tagged readout. -/
  outputRecovery : Q.PolyOutputSizeRecovery bd
  /-- One polynomial shared by every compatible response model. -/
  polynomial : ExecutionCostPolynomial (ResponseModulus label)
  /-- Local ranked evidence specialized to each compatible model. -/
  resourcePotential : ∀ model : contract.Model,
    RankedResource.PotentialCertificate realization model.resourceModel.allows fun value ↦
      polynomial.eval model.modulus (Q.size bd.input value)

namespace RankedResourceCertificate

variable {contract : ResponseResourceContract Q bd.interface label}
  {program : input → FreeM p output}

/-- Forget local ranked evidence to the realization-only polynomial run bound. -/
def runBound (certificate : RankedResourceCertificate Q bd contract program) :
    PolynomialRunBound certificate.realization contract where
  polynomial := certificate.polynomial
  runsWithin model := (certificate.resourcePotential model).runsWithinUnder

/-- Forget local ranked evidence to the standard polynomial program witness. -/
def programWitness (certificate : RankedResourceCertificate Q bd contract program) :
    PolynomialProgramWitness Q bd contract program where
  realization := certificate.realization
  implements := certificate.implements
  outputRecovery := certificate.outputRecovery
  runBound := certificate.runBound

end RankedResourceCertificate

/-! ## Polynomial sequential-composition certificates -/

section SeqComp

variable [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive]
  {final : Type u} {middleOut : C.Str final}
  {R₁ : QuantitativeRealization Q bd}
  {R₂ : QuantitativeRealization Q (bd.mid middleOut)}
  {contract : ResponseResourceContract Q bd.interface label}

/-- A response-model-uniform polynomial envelope for every reachable second-phase run. -/
structure PolynomialSeqCompHandoffBound
    (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid middleOut))
    (contract : ResponseResourceContract Q bd.interface label)
    (second : PolynomialRunBound R₂ contract) where
  /-- Shared polynomial envelope for the reached second phase. -/
  polynomial : ExecutionCostPolynomial (ResponseModulus label)
  /-- The exact handoff certificate under each compatible response model. -/
  certificate : ∀ model : contract.Model,
    SeqCompHandoffBound R₁ model.resourceModel.allows (second.bound model)
  /-- Every model-specific handoff envelope fits the shared polynomial. -/
  bound_le : ∀ (model : contract.Model) input,
    (certificate model).bound input ≤
      polynomial.eval model.modulus (Q.size bd.input input)

/-- A response-model-uniform polynomial allowance for structural composition overhead. -/
structure PolynomialSeqCompCostCertificate
    (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid middleOut))
    (contract : ResponseResourceContract Q bd.interface label) where
  /-- Shared polynomial envelope for structural wiring and phase switching. -/
  polynomial : ExecutionCostPolynomial (ResponseModulus label)
  /-- The exact composite/source cost comparison under each compatible response model. -/
  certificate : ∀ model : contract.Model,
    SeqCompCostCertificate R₁ R₂ model.resourceModel.allows
  /-- Every model-specific structural allowance fits the shared polynomial. -/
  overhead_le : ∀ (model : contract.Model) input,
    (certificate model).overhead input ≤
      polynomial.eval model.modulus (Q.size bd.input input)

namespace PolynomialRunBound

/-- Polynomial run bounds compose using the exact phase decomposition from bounded closure.

The first-phase, handoff, and structural bounds are accumulated conservatively. The two peak
components may therefore be loose, but remain sound because `ExecutionCost` combines peaks by
`max`. -/
def seqComp (first : PolynomialRunBound R₁ contract)
    (second : PolynomialRunBound R₂ contract)
    (handoff : PolynomialSeqCompHandoffBound R₁ R₂ contract second)
    (cost : PolynomialSeqCompCostCertificate R₁ R₂ contract) :
    PolynomialRunBound (R₁.seqComp R₂) contract where
  polynomial := first.polynomial + handoff.polynomial + cost.polynomial
  runsWithin model := by
    have assembled := (first.runsWithin_bound model).seqComp
      (second.runsWithin_bound model) (handoff.certificate model) (cost.certificate model)
    apply assembled.mono
    intro input
    let size := Q.size bd.input input
    let length := model.modulus
    have h₁ :
        first.polynomial.eval length size + handoff.polynomial.eval length size ≤
          (first.polynomial + handoff.polynomial).eval length size :=
      ExecutionCostPolynomial.add_eval_le_eval_add _ _ _ _
    have h₂ :
        (first.polynomial + handoff.polynomial).eval length size +
            cost.polynomial.eval length size ≤
          (first.polynomial + handoff.polynomial + cost.polynomial).eval length size :=
      ExecutionCostPolynomial.add_eval_le_eval_add _ _ _ _
    change first.polynomial.eval length size + (handoff.certificate model).bound input +
        (cost.certificate model).overhead input ≤ _
    calc
      first.polynomial.eval length size + (handoff.certificate model).bound input +
          (cost.certificate model).overhead input ≤
          (first.polynomial.eval length size + handoff.polynomial.eval length size) +
            cost.polynomial.eval length size :=
        ExecutionCost.add_le_add
          (ExecutionCost.add_le_add le_rfl (handoff.bound_le model input))
          (cost.overhead_le model input)
      _ ≤ (first.polynomial + handoff.polynomial).eval length size +
          cost.polynomial.eval length size :=
        ExecutionCost.add_le_add h₁ le_rfl
      _ ≤ (first.polynomial + handoff.polynomial + cost.polynomial).eval length size := h₂

end PolynomialRunBound

namespace PolynomialProgramWitness

variable {program₁ : input → FreeM p output} {program₂ : output → FreeM p final}

/-- Compose program witnesses along `FreeM.bind`, keeping semantic implementation separate from
the resource decomposition certificates needed by the two execution phases. -/
def bind (first : PolynomialProgramWitness Q bd contract program₁)
    (second : PolynomialProgramWitness Q (bd.mid middleOut) contract program₂)
    (handoff : PolynomialSeqCompHandoffBound first.realization second.realization contract
      second.runBound)
    (cost : PolynomialSeqCompCostCertificate first.realization second.realization contract) :
    PolynomialProgramWitness Q (bd.withOut middleOut) contract
      (fun input ↦ FreeM.bind (program₁ input) program₂) where
  realization := first.realization.seqComp second.realization
  implements := first.implements.seqComp second.implements
  outputRecovery :=
    { polynomial := second.outputRecovery.polynomial
      output_le := second.outputRecovery.output_le }
  runBound := first.runBound.seqComp second.runBound handoff cost

end PolynomialProgramWitness

end SeqComp

end DynSystem.DynComputation

end PFunctor
