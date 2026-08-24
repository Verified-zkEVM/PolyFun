/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Basic

/-!
# Quantitative realizability

This file refines the qualitative `StepClass` boundary with Type-valued executable
evidence and a backend-relative work measure. A `QuantitativeStepClass C` packages
one concrete notion of code for `C`-admissible functions together with its operational
cost semantics. Identity and composition are deliberately separate, optional structure:
`QuantitativeStepClass.HasCategory` supplies executable categorical wiring and a sound
upper bound for its cost, while `QuantitativeStepClass.HasExactCategory` records the
stronger exact-cost equation when a backend supports one. A later adequacy theorem must
connect a chosen backend to a conventional machine model before the costs support a claim
such as polynomial time.

`QuantitativeRealization` applies that evidence to the three compositional maps of
a returning dynamical computation:

* `init`, once at the start of a run;
* `head`, once at every visited state; and
* the partial `update?`, once for every enabled query-answer transition.

Finite `ExecutionTrace`s record prefixes of fully syntactic interaction. Their
cost accumulates backend work, visible queries, encoded boundary traffic, and
peak reachable-state/readout sizes. Quantifying over prefixes is important: an
infinite query path cannot satisfy a finite bound merely because it has no
terminating trace. `TraceProgress` separately rules out a trace-reachable query
whose response type is empty, where universal branchwise termination would be
vacuous.

Representations and boundaries remain explicit parameters. In particular, this
module neither chooses encodings existentially nor defines an unqualified notion
of PPT.
-/

@[expose] public section

universe u v w

namespace PFunctor

/-! ## Backend-relative code and work -/

/-- Type-valued realizers for the morphisms of a qualitative step class.

`Realizer a b f` is the backend's executable evidence for the represented
function `f`. Its type index supplies semantic correctness; `admissible` erases
the evidence to the qualitative class. `cost` is exact only relative to the
chosen backend. Establishing that it counts steps of a standard machine model is
a separate adequacy obligation for each backend.

Identity and composition are not core fields: some quantitative backends are useful
before they have certified closure under code composition. -/
structure QuantitativeStepClass (C : StepClass.{u, v}) where
  /-- Executable evidence for a represented function. -/
  Realizer : {A B : Type u} → C.Str A → C.Str B → (A → B) → Type w
  /-- Encoded size of a value relative to its pinned representation. -/
  size : {A : Type u} → C.Str A → A → ℕ
  /-- Exact work used by a realizer on an input, relative to this backend. -/
  cost : {A B : Type u} → {a : C.Str A} → {b : C.Str B} → {f : A → B} →
    Realizer a b f → A → ℕ
  /-- Every quantitative realizer is qualitatively admissible. -/
  admissible : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B},
    Realizer a b f → C.Hom a b f

namespace QuantitativeStepClass

variable {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C)

/-- Executable identity and sequential composition for a quantitative backend.

Composition exposes its connection overhead and only requires a certified upper bound.
Backends whose operational semantics gives an exact equation can additionally implement
`HasExactCategory`. -/
class HasCategory where
  /-- Executable evidence for identity functions. -/
  identity : ∀ {A : Type u} (a : C.Str A), Q.Realizer a a id
  /-- Sequentially compose two pieces of executable evidence. -/
  compose : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D}, Q.Realizer a b f → Q.Realizer b d g →
      Q.Realizer a d (g ∘ f)
  /-- Work spent by the backend to connect two sequential pieces of code. -/
  composeOverhead : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D},
    Q.Realizer a b f → Q.Realizer b d g → A → ℕ
  /-- Sound upper bound for the cost of sequentially composed evidence. -/
  cost_compose_le : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D}
    (rf : Q.Realizer a b f) (rg : Q.Realizer b d g) (input : A),
    Q.cost (compose rf rg) input ≤
      Q.cost rf input + Q.cost rg (f input) + composeOverhead rf rg input

/-- The identity code selected by a quantitative category instance. -/
def identity [Q.HasCategory] {A : Type u} (a : C.Str A) : Q.Realizer a a id :=
  HasCategory.identity a

/-- Sequential composition selected by a quantitative category instance. -/
def compose [Q.HasCategory] {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D}
    (rf : Q.Realizer a b f) (rg : Q.Realizer b d g) : Q.Realizer a d (g ∘ f) :=
  HasCategory.compose rf rg

/-- Connection overhead selected by a quantitative category instance. -/
def composeOverhead [Q.HasCategory] {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D}
    (rf : Q.Realizer a b f) (rg : Q.Realizer b d g) (input : A) : ℕ :=
  HasCategory.composeOverhead rf rg input

/-- Optional exact-cost refinement of `QuantitativeStepClass.HasCategory`. -/
class HasExactCategory [Q.HasCategory] : Prop where
  /-- Exact cost equation for sequentially composed evidence. -/
  cost_compose_eq : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D}
    (rf : Q.Realizer a b f) (rg : Q.Realizer b d g) (input : A),
    Q.cost (Q.compose rf rg) input =
      Q.cost rf input + Q.cost rg (f input) + Q.composeOverhead rf rg input

/-- Exact categorical data in one bundle, convenient for operational backends whose composition
cost has an exact equation. `ExactCategory.toHasCategory` forgets equality to the sound upper
bound required by generic closure, and `ExactCategory.toHasExactCategory` restores the
refinement. -/
structure ExactCategory where
  /-- Executable evidence for identity functions. -/
  identity : ∀ {A : Type u} (a : C.Str A), Q.Realizer a a id
  /-- Sequentially compose two pieces of executable evidence. -/
  compose : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D}, Q.Realizer a b f → Q.Realizer b d g →
      Q.Realizer a d (g ∘ f)
  /-- Exact work spent connecting two pieces of code. -/
  composeOverhead : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D},
    Q.Realizer a b f → Q.Realizer b d g → A → ℕ
  /-- Exact cost equation for sequential composition. -/
  cost_compose_eq : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D}
    (rf : Q.Realizer a b f) (rg : Q.Realizer b d g) (input : A),
    Q.cost (compose rf rg) input =
      Q.cost rf input + Q.cost rg (f input) + composeOverhead rf rg input

namespace ExactCategory

variable {Q}

/-- Forget an exact composition equation to its sound upper-bound category. -/
@[instance_reducible]
def toHasCategory (category : Q.ExactCategory) : Q.HasCategory where
  identity := category.identity
  compose := category.compose
  composeOverhead := category.composeOverhead
  cost_compose_le first second input := Nat.le_of_eq (category.cost_compose_eq first second input)

/-- Recover the optional exact refinement for the category obtained from exact data. -/
theorem toHasExactCategory (category : Q.ExactCategory) :
    letI := category.toHasCategory
    Q.HasExactCategory := by
  let _ := category.toHasCategory
  exact ⟨category.cost_compose_eq⟩

end ExactCategory

/-- The qualitative admissibility proof carried by executable evidence. -/
theorem Realizer.toHom {A B : Type u} {a : C.Str A} {b : C.Str B}
    {f : A → B} (code : Q.Realizer a b f) : C.Hom a b f :=
  Q.admissible code

/-- The cost of composed code is at most the two component costs plus the backend's
explicit connection overhead. -/
theorem cost_comp_le [Q.HasCategory] {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D}
    (rf : Q.Realizer a b f) (rg : Q.Realizer b d g) (input : A) :
    Q.cost (Q.compose rf rg) input ≤
      Q.cost rf input + Q.cost rg (f input) + Q.composeOverhead rf rg input :=
  HasCategory.cost_compose_le rf rg input

/-- Exact cost of composition for a backend carrying the optional exact refinement. -/
theorem cost_comp [Q.HasCategory] [Q.HasExactCategory]
    {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D}
    (rf : Q.Realizer a b f) (rg : Q.Realizer b d g) (input : A) :
    Q.cost (Q.compose rf rg) input =
      Q.cost rf input + Q.cost rg (f input) + Q.composeOverhead rf rg input :=
  HasExactCategory.cost_compose_eq rf rg input

end QuantitativeStepClass

/-! ## Additive execution resources -/

/-- Additive resources accumulated by an interaction prefix.

`work` and encoded sizes are supplied by the quantitative backend. `queries` is
counted structurally from the PolyFun trace and therefore cannot be changed by a
backend cost annotation. Work, query count, and boundary traffic add under
composition; reachable-state and one-step-readout sizes compose by `max`. -/
@[ext]
structure ExecutionCost where
  /-- Backend-relative local work. -/
  work : ℕ
  /-- Number of visible query-answer transitions. -/
  queries : ℕ
  /-- Total encoded query and answer traffic. -/
  traffic : ℕ
  /-- Greatest encoded hidden-state size observed so far. -/
  peakStateSize : ℕ
  /-- Greatest encoded `head` value size observed so far. -/
  peakHeadSize : ℕ
  deriving DecidableEq

namespace ExecutionCost

/-- No work and no visible queries. -/
instance : Zero ExecutionCost := ⟨⟨0, 0, 0, 0, 0⟩⟩

/-- Sequential resource use adds componentwise. -/
instance : Add ExecutionCost := ⟨fun left right =>
  ⟨left.work + right.work, left.queries + right.queries,
    left.traffic + right.traffic, max left.peakStateSize right.peakStateSize,
    max left.peakHeadSize right.peakHeadSize⟩⟩

instance : AddCommMonoid ExecutionCost where
  add_assoc left middle right := by
    apply ExecutionCost.ext
    · exact Nat.add_assoc left.work middle.work right.work
    · exact Nat.add_assoc left.queries middle.queries right.queries
    · exact Nat.add_assoc left.traffic middle.traffic right.traffic
    · exact max_assoc left.peakStateSize middle.peakStateSize right.peakStateSize
    · exact max_assoc left.peakHeadSize middle.peakHeadSize right.peakHeadSize
  zero_add cost := by
    apply ExecutionCost.ext
    · exact Nat.zero_add cost.work
    · exact Nat.zero_add cost.queries
    · exact Nat.zero_add cost.traffic
    · exact zero_max cost.peakStateSize
    · exact zero_max cost.peakHeadSize
  add_zero cost := by
    apply ExecutionCost.ext
    · exact Nat.add_zero cost.work
    · exact Nat.add_zero cost.queries
    · exact Nat.add_zero cost.traffic
    · exact max_zero cost.peakStateSize
    · exact max_zero cost.peakHeadSize
  add_comm left right := by
    apply ExecutionCost.ext
    · exact Nat.add_comm left.work right.work
    · exact Nat.add_comm left.queries right.queries
    · exact Nat.add_comm left.traffic right.traffic
    · exact max_comm left.peakStateSize right.peakStateSize
    · exact max_comm left.peakHeadSize right.peakHeadSize
  nsmul := nsmulRec

/-- Bounds compare each resource component independently. -/
instance : PartialOrder ExecutionCost where
  le left right := left.work ≤ right.work ∧ left.queries ≤ right.queries ∧
    left.traffic ≤ right.traffic ∧ left.peakStateSize ≤ right.peakStateSize ∧
      left.peakHeadSize ≤ right.peakHeadSize
  le_refl cost := ⟨Nat.le_refl cost.work, Nat.le_refl cost.queries,
    Nat.le_refl cost.traffic, Nat.le_refl cost.peakStateSize,
    Nat.le_refl cost.peakHeadSize⟩
  le_trans left middle right hlm hmr :=
    ⟨Nat.le_trans hlm.1 hmr.1, Nat.le_trans hlm.2.1 hmr.2.1,
      Nat.le_trans hlm.2.2.1 hmr.2.2.1,
      Nat.le_trans hlm.2.2.2.1 hmr.2.2.2.1,
      Nat.le_trans hlm.2.2.2.2 hmr.2.2.2.2⟩
  le_antisymm left right hlr hrl := by
    ext
    · exact Nat.le_antisymm hlr.1 hrl.1
    · exact Nat.le_antisymm hlr.2.1 hrl.2.1
    · exact Nat.le_antisymm hlr.2.2.1 hrl.2.2.1
    · exact Nat.le_antisymm hlr.2.2.2.1 hrl.2.2.2.1
    · exact Nat.le_antisymm hlr.2.2.2.2 hrl.2.2.2.2

/-- Embed local backend work without adding a visible query. -/
def ofWork (work : ℕ) : ExecutionCost := ⟨work, 0, 0, 0, 0⟩

/-- Observe a represented hidden state and one-step readout. These dimensions
compose by maximum rather than addition. -/
def observe (stateSize headSize : ℕ) : ExecutionCost :=
  ⟨0, 0, 0, stateSize, headSize⟩

/-- The structural count and encoded traffic of one visible query-answer
transition. -/
def query (positionSize indexSize : ℕ) : ExecutionCost :=
  ⟨0, 1, positionSize + indexSize, 0, 0⟩

@[simp] theorem work_zero : (0 : ExecutionCost).work = 0 := rfl

@[simp] theorem queries_zero : (0 : ExecutionCost).queries = 0 := rfl

@[simp] theorem traffic_zero : (0 : ExecutionCost).traffic = 0 := rfl

@[simp] theorem peakStateSize_zero : (0 : ExecutionCost).peakStateSize = 0 := rfl

@[simp] theorem peakHeadSize_zero : (0 : ExecutionCost).peakHeadSize = 0 := rfl

@[simp] theorem work_add (left right : ExecutionCost) :
    (left + right).work = left.work + right.work := rfl

@[simp] theorem queries_add (left right : ExecutionCost) :
    (left + right).queries = left.queries + right.queries := rfl

@[simp] theorem traffic_add (left right : ExecutionCost) :
    (left + right).traffic = left.traffic + right.traffic := rfl

@[simp] theorem peakStateSize_add (left right : ExecutionCost) :
    (left + right).peakStateSize = max left.peakStateSize right.peakStateSize := rfl

@[simp] theorem peakHeadSize_add (left right : ExecutionCost) :
    (left + right).peakHeadSize = max left.peakHeadSize right.peakHeadSize := rfl

@[simp] theorem work_ofWork (work : ℕ) : (ofWork work).work = work := rfl

@[simp] theorem queries_ofWork (work : ℕ) : (ofWork work).queries = 0 := rfl

@[simp] theorem traffic_ofWork (work : ℕ) : (ofWork work).traffic = 0 := rfl

@[simp] theorem work_observe (stateSize headSize : ℕ) :
    (observe stateSize headSize).work = 0 := rfl

@[simp] theorem queries_observe (stateSize headSize : ℕ) :
    (observe stateSize headSize).queries = 0 := rfl

@[simp] theorem traffic_observe (stateSize headSize : ℕ) :
    (observe stateSize headSize).traffic = 0 := rfl

@[simp] theorem peakStateSize_observe (stateSize headSize : ℕ) :
    (observe stateSize headSize).peakStateSize = stateSize := rfl

@[simp] theorem peakHeadSize_observe (stateSize headSize : ℕ) :
    (observe stateSize headSize).peakHeadSize = headSize := rfl

@[simp] theorem work_query (positionSize indexSize : ℕ) :
    (query positionSize indexSize).work = 0 := rfl

@[simp] theorem queries_query (positionSize indexSize : ℕ) :
    (query positionSize indexSize).queries = 1 := rfl

@[simp] theorem traffic_query (positionSize indexSize : ℕ) :
    (query positionSize indexSize).traffic = positionSize + indexSize := rfl

theorem le_iff {actual bound : ExecutionCost} :
    actual ≤ bound ↔ actual.work ≤ bound.work ∧ actual.queries ≤ bound.queries ∧
      actual.traffic ≤ bound.traffic ∧ actual.peakStateSize ≤ bound.peakStateSize ∧
        actual.peakHeadSize ≤ bound.peakHeadSize :=
  Iff.rfl

/-- Componentwise bounds add under sequential composition. -/
theorem add_le_add {actual₁ bound₁ actual₂ bound₂ : ExecutionCost}
    (h₁ : actual₁ ≤ bound₁) (h₂ : actual₂ ≤ bound₂) :
    actual₁ + actual₂ ≤ bound₁ + bound₂ :=
  ⟨Nat.add_le_add h₁.1 h₂.1, Nat.add_le_add h₁.2.1 h₂.2.1,
    Nat.add_le_add h₁.2.2.1 h₂.2.2.1,
    max_le_max h₁.2.2.2.1 h₂.2.2.2.1,
    max_le_max h₁.2.2.2.2 h₂.2.2.2.2⟩

end ExecutionCost

namespace DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {α β : Type u}
  {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq p.A] (Q : QuantitativeStepClass.{u, v, w} C)
  (bd : Boundary C p α β)

/-! ## Quantitative realizations -/

/-- A returning dynamical computation whose three compositional step maps carry
executable, costed evidence from a chosen quantitative backend. -/
structure QuantitativeRealization where
  /-- The underlying returning state machine. -/
  machine : DynComputation.{u} p α β
  /-- The pinned representation of its hidden state. -/
  state : C.Str machine.State
  /-- Costed executable evidence for initialization. -/
  initCode : Q.Realizer bd.input state machine.init
  /-- Costed executable evidence for the one-step readout. -/
  headCode : Q.Realizer state bd.head machine.head
  /-- Costed executable evidence for the enabled partial transition. -/
  updateCode : Q.Realizer (bd.stateIdx state) (StepClass.HasOption.option state)
    machine.update?

namespace QuantitativeRealization

variable {Q bd}

/-- Forget quantitative code and costs, retaining the qualitative realization. -/
def toRealization (R : QuantitativeRealization Q bd) : Realization C bd where
  machine := R.machine
  state := R.state
  init_mem := Q.admissible R.initCode
  head_mem := Q.admissible R.headCode
  update_mem := Q.admissible R.updateCode

@[simp] theorem toRealization_machine (R : QuantitativeRealization Q bd) :
    R.toRealization.machine = R.machine := rfl

/-! ## Fully syntactic execution prefixes -/

/-- A finite, fully syntactic query-answer prefix of a quantitative realization.

The indices are the starting and ending hidden states. `nil` observes no query.
`query` records the exposed dependent position, one typed answer, and the rest
of the prefix. Its `view_eq` proof ensures that the charged `update?` call is
enabled rather than a junk-input branch of the partial function. -/
inductive ExecutionTrace (R : QuantitativeRealization Q bd) :
    R.machine.State → R.machine.State → Type u where
  /-- The empty prefix at a state. -/
  | nil (state : R.machine.State) : ExecutionTrace R state state
  /-- Extend a prefix by one exposed query and typed answer. -/
  | query {state : R.machine.State} {position : p.A}
      {next : p.B position → R.machine.State} {finish : R.machine.State}
      (view_eq : R.machine.view state = Sum.inr ⟨position, next⟩)
      (direction : p.B position)
      (tail : ExecutionTrace R (next direction) finish) :
      ExecutionTrace R state finish

namespace ExecutionTrace

variable {R : QuantitativeRealization Q bd}

/-- Every response recorded by a syntactic trace satisfies a dependent answer relation.

The relation is supplied externally, so this predicate can express an oracle contract without
changing the fully syntactic trace type or pretending that disallowed answers do not exist. -/
def Conforms (allows : ∀ position, p.B position → Prop)
    {start finish : R.machine.State} : ExecutionTrace R start finish → Prop
  | .nil _ => True
  | .query (position := position) _ direction tail =>
      allows position direction ∧ tail.Conforms allows

/-- Every syntactic trace conforms to the relation that allows every typed answer. -/
theorem conforms_all {start finish : R.machine.State}
    (trace : ExecutionTrace R start finish) :
    trace.Conforms (fun _ _ ↦ True) := by
  induction trace with
  | nil => trivial
  | query view_eq direction tail ih => exact ⟨trivial, ih⟩

/-- Conformance is monotone under pointwise enlargement of the allowed-answer relation. -/
theorem Conforms.mono {allows allows' : ∀ position, p.B position → Prop}
    (hAllows : ∀ position direction, allows position direction → allows' position direction)
    {start finish : R.machine.State} {trace : ExecutionTrace R start finish}
    (h : trace.Conforms allows) : trace.Conforms allows' := by
  induction trace with
  | nil => trivial
  | query view_eq direction tail ih => exact ⟨hAllows _ _ h.1, ih h.2⟩

/-- Number of visible query-answer transitions in a prefix. -/
def length {start finish : R.machine.State} : ExecutionTrace R start finish → ℕ
  | .nil _ => 0
  | .query _ _ tail => tail.length + 1

/-- Number of query-answer transitions carrying one selected interface label. -/
def queryCount {label : Type*} [DecidableEq label] (labelOf : p.A → label)
    (interface : label) {start finish : R.machine.State} :
    ExecutionTrace R start finish → ℕ
  | .nil _ => 0
  | .query (position := position) _ _ tail =>
      if labelOf position = interface then tail.queryCount labelOf interface + 1
      else tail.queryCount labelOf interface

/-- Encoded query-answer traffic carrying one selected interface label. -/
def interfaceTraffic {label : Type*} [DecidableEq label] (labelOf : p.A → label)
    (interface : label) {start finish : R.machine.State} :
    ExecutionTrace R start finish → ℕ
  | .nil _ => 0
  | .query (position := position) _ direction tail =>
      if labelOf position = interface then
        Q.size bd.pos position + Q.size bd.idx ⟨position, direction⟩ +
          tail.interfaceTraffic labelOf interface
      else tail.interfaceTraffic labelOf interface

/-- A selected interface cannot account for more queries than occur in the whole trace. -/
theorem queryCount_le_length {label : Type*} [DecidableEq label]
    (labelOf : p.A → label) (interface : label)
    {start finish : R.machine.State} (trace : ExecutionTrace R start finish) :
    trace.queryCount labelOf interface ≤ trace.length := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih =>
      simp only [queryCount, length]
      split <;> omega

/-- The partial transition charged by a query trace step is enabled and reaches
the state at which its tail begins. -/
theorem update_eq_some {state : R.machine.State} {position : p.A}
    {next : p.B position → R.machine.State}
    (view_eq : R.machine.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position) :
    R.machine.update? (state, ⟨position, direction⟩) = some (next direction) :=
  R.machine.update?_of_view_query view_eq direction

/-- Backend work and visible queries used by the transitions in a prefix.

This excludes initialization and the final state's `head`; `executionCost`
adds those exactly once. Each query step charges `head` at its source, the
enabled `update?`, and one structural visible query. -/
def cost {start finish : R.machine.State} : ExecutionTrace R start finish → ExecutionCost
  | .nil _ => 0
  | .query (position := position) _ direction tail =>
      ExecutionCost.ofWork (Q.cost R.headCode start) +
        ExecutionCost.ofWork (Q.cost R.updateCode (start, ⟨position, direction⟩)) +
        ExecutionCost.observe (Q.size R.state start)
          (Q.size bd.head (R.machine.head start)) +
        ExecutionCost.query (Q.size bd.pos position)
          (Q.size bd.idx ⟨position, direction⟩) + cost tail

/-- A trace starting at a returning state is empty: its final state is unchanged and it incurs no
transition cost.

This inversion principle keeps clients from having to eliminate an indexed `ExecutionTrace`
directly, which is especially awkward when the starting state is definitionally hidden behind a
concrete realization. -/
theorem finish_eq_and_cost_eq_zero_of_view_return
    {start finish : R.machine.State} (trace : ExecutionTrace R start finish)
    {value : β} (view_eq : R.machine.view start = Sum.inl value) :
    finish = start ∧ trace.cost = 0 := by
  cases trace with
  | nil => exact ⟨rfl, rfl⟩
  | query query_eq direction tail =>
      rw [view_eq] at query_eq
      exact nomatch query_eq

/-- Encoded traffic on one selected interface is at most the trace's total traffic. -/
theorem interfaceTraffic_le_traffic_cost {label : Type*} [DecidableEq label]
    (labelOf : p.A → label) (interface : label)
    {start finish : R.machine.State} (trace : ExecutionTrace R start finish) :
    trace.interfaceTraffic labelOf interface ≤ trace.cost.traffic := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih =>
      simp only [interfaceTraffic, cost, ExecutionCost.traffic_add,
        ExecutionCost.traffic_ofWork, ExecutionCost.traffic_observe,
        ExecutionCost.traffic_query]
      split <;> omega

/-- The query component of the resource fold is exactly the syntactic trace
length and is independent of backend work or size accounting. -/
@[simp] theorem queries_cost {start finish : R.machine.State}
    (trace : ExecutionTrace R start finish) : trace.cost.queries = trace.length := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih => simp [cost, length, ih, Nat.add_comm]

/-- Concatenate two adjacent execution prefixes. -/
def append {start middle finish : R.machine.State}
    (left : ExecutionTrace R start middle) (right : ExecutionTrace R middle finish) :
    ExecutionTrace R start finish :=
  match left with
  | .nil _ => right
  | .query view_eq direction tail => .query view_eq direction (tail.append right)

/-- Conformance composes under concatenation of adjacent traces. -/
theorem conforms_append {allows : ∀ position, p.B position → Prop}
    {start middle finish : R.machine.State}
    (left : ExecutionTrace R start middle) (right : ExecutionTrace R middle finish) :
    (left.append right).Conforms allows ↔ left.Conforms allows ∧ right.Conforms allows := by
  induction left with
  | nil => simp [append, Conforms]
  | query view_eq direction tail ih => simp [append, Conforms, ih, and_assoc]

/-- Trace cost composes additively under concatenation. -/
theorem cost_append {start middle finish : R.machine.State}
    (left : ExecutionTrace R start middle) (right : ExecutionTrace R middle finish) :
    cost (left.append right) = cost left + cost right := by
  induction left with
  | nil => simp [append, cost]
  | query view_eq direction tail ih =>
      simp only [append, cost, ih]
      simp only [add_assoc]

/-- Per-interface query counts add under trace concatenation. -/
theorem queryCount_append {label : Type*} [DecidableEq label]
    (labelOf : p.A → label) (interface : label)
    {start middle finish : R.machine.State}
    (left : ExecutionTrace R start middle) (right : ExecutionTrace R middle finish) :
    (left.append right).queryCount labelOf interface =
      left.queryCount labelOf interface + right.queryCount labelOf interface := by
  induction left with
  | nil => simp [append, queryCount]
  | query view_eq direction tail ih =>
      simp only [append, queryCount]
      split <;> simp [ih, Nat.add_left_comm, Nat.add_comm]

/-- Per-interface encoded traffic adds under trace concatenation. -/
theorem interfaceTraffic_append {label : Type*} [DecidableEq label]
    (labelOf : p.A → label) (interface : label)
    {start middle finish : R.machine.State}
    (left : ExecutionTrace R start middle) (right : ExecutionTrace R middle finish) :
    (left.append right).interfaceTraffic labelOf interface =
      left.interfaceTraffic labelOf interface + right.interfaceTraffic labelOf interface := by
  induction left with
  | nil => simp [append, interfaceTraffic]
  | query view_eq direction tail ih =>
      simp only [append, interfaceTraffic]
      split <;> simp [ih, Nat.add_assoc]

/-- Bounds for adjacent prefixes compose by addition. -/
theorem cost_append_le {start middle finish : R.machine.State}
    (left : ExecutionTrace R start middle) (right : ExecutionTrace R middle finish)
    {leftBound rightBound : ExecutionCost} (hleft : cost left ≤ leftBound)
    (hright : cost right ≤ rightBound) :
    cost (left.append right) ≤ leftBound + rightBound := by
  rw [cost_append]
  exact ExecutionCost.add_le_add hleft hright

end ExecutionTrace

/-! ## Exact pathwise bounds -/

/-- Exact resource use of an execution prefix from a concrete input.

Initialization is charged once, transition costs are folded from the trace, and
`head` is charged once at the final observed state. Thus a prefix of `k` queries
charges exactly `k + 1` readouts and `k` enabled updates. -/
def executionCost (R : QuantitativeRealization Q bd) (input : α)
    {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) : ExecutionCost :=
  ExecutionCost.ofWork (Q.cost R.initCode input) + trace.cost +
    ExecutionCost.ofWork (Q.cost R.headCode finish) +
      ExecutionCost.observe (Q.size R.state finish)
        (Q.size bd.head (R.machine.head finish))

/-- Initialization and observation add no visible queries, so total query use
remains the syntactic length of the execution prefix. -/
@[simp] theorem queries_executionCost (R : QuantitativeRealization Q bd) (input : α)
    {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) :
    (R.executionCost input trace).queries = trace.length := by
  simp [executionCost]

end QuantitativeRealization

/-! ## Resolution under an answer relation -/

/-- Every answer branch allowed by `allows` returns within `k` visible queries.

This is the contract-relative analogue of `DynComputation.ResolvesIn`. Disallowed typed answers
remain part of the underlying interface syntax, but they are not quantified over by this bound. -/
def ResolvesInUnder (M : DynComputation.{u} p α β)
    (allows : ∀ position, p.B position → Prop) : ℕ → M.State → Prop
  | 0, state => match M.view state with
    | Sum.inl _ => True
    | Sum.inr _ => False
  | k + 1, state => match M.view state with
    | Sum.inl _ => True
    | Sum.inr ⟨position, next⟩ =>
        ∀ direction, allows position direction → M.ResolvesInUnder allows k (next direction)

omit [DecidableEq p.A] in
/-- At budget zero, relation-restricted resolution is exactly immediate return. -/
theorem resolvesInUnder_zero (M : DynComputation.{u} p α β)
    (allows : ∀ position, p.B position → Prop) (state : M.State) :
    M.ResolvesInUnder allows 0 state ↔ ∃ value, M.view state = Sum.inl value := by
  cases hview : M.view state <;> simp [ResolvesInUnder, hview]

omit [DecidableEq p.A] in
/-- A returning state resolves under every answer relation and every budget. -/
@[simp] theorem resolvesInUnder_return (M : DynComputation.{u} p α β)
    (allows : ∀ position, p.B position → Prop) (k : ℕ) (state : M.State) (value : β)
    (hview : M.view state = Sum.inl value) : M.ResolvesInUnder allows k state := by
  cases k <;> simp [ResolvesInUnder, hview]

omit [DecidableEq p.A] in
/-- A query cannot resolve with zero remaining queries, even under a restrictive relation. -/
theorem not_resolvesInUnder_query_zero (M : DynComputation.{u} p α β)
    (allows : ∀ position, p.B position → Prop) (state : M.State) (position : p.A)
    (next : p.B position → M.State) (hview : M.view state = Sum.inr ⟨position, next⟩) :
    ¬M.ResolvesInUnder allows 0 state := by
  simp [ResolvesInUnder, hview]

omit [DecidableEq p.A] in
/-- Unfold relation-restricted resolution at a querying state. -/
theorem resolvesInUnder_query_succ_iff (M : DynComputation.{u} p α β)
    (allows : ∀ position, p.B position → Prop) (k : ℕ) (state : M.State)
    (position : p.A) (next : p.B position → M.State)
    (hview : M.view state = Sum.inr ⟨position, next⟩) :
    M.ResolvesInUnder allows (k + 1) state ↔
      ∀ direction, allows position direction →
        M.ResolvesInUnder allows k (next direction) := by
  simp [ResolvesInUnder, hview]

omit [DecidableEq p.A] in
/-- Relation-restricted resolution is monotone in the available query budget. -/
theorem ResolvesInUnder.mono {M : DynComputation.{u} p α β}
    {allows : ∀ position, p.B position → Prop} {j k : ℕ} {state : M.State}
    (h : M.ResolvesInUnder allows j state) (hjk : j ≤ k) :
    M.ResolvesInUnder allows k state := by
  induction j generalizing k state with
  | zero =>
      obtain ⟨value, hview⟩ := (M.resolvesInUnder_zero allows state).mp h
      exact M.resolvesInUnder_return allows k state value hview
  | succ j ih =>
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      cases hview : M.view state with
      | inl value => exact M.resolvesInUnder_return allows _ state value hview
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [M.resolvesInUnder_query_succ_iff allows j state position next hview] at h
          rw [M.resolvesInUnder_query_succ_iff allows k state position next hview]
          exact fun direction hAllows ↦ ih (h direction hAllows) (by omega)

omit [DecidableEq p.A] in
/-- Restricting the set of admitted answers preserves relation-restricted resolution. -/
theorem ResolvesInUnder.antitone {M : DynComputation.{u} p α β}
    {allows allows' : ∀ position, p.B position → Prop}
    (hAllows : ∀ position direction, allows' position direction → allows position direction)
    {k : ℕ} {state : M.State} (h : M.ResolvesInUnder allows k state) :
    M.ResolvesInUnder allows' k state := by
  induction k generalizing state with
  | zero => simpa [ResolvesInUnder] using h
  | succ k ih =>
      cases hview : M.view state with
      | inl value => exact M.resolvesInUnder_return allows' _ state value hview
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [M.resolvesInUnder_query_succ_iff allows k state position next hview] at h
          rw [M.resolvesInUnder_query_succ_iff allows' k state position next hview]
          exact fun direction hAllows' ↦
            ih (h direction (hAllows position direction hAllows'))

omit [DecidableEq p.A] in
/-- Allowing every typed answer recovers ordinary branchwise resolution. -/
theorem resolvesInUnder_all_iff (M : DynComputation.{u} p α β)
    (k : ℕ) (state : M.State) :
    M.ResolvesInUnder (fun _ _ ↦ True) k state ↔ M.ResolvesIn k state := by
  induction k generalizing state with
  | zero =>
      cases hview : M.view state <;> rfl
  | succ k ih =>
      cases hview : M.view state with
      | inl value => simp [ResolvesInUnder, ResolvesIn, hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          simp only [ResolvesInUnder, ResolvesIn, hview, true_implies]
          exact forall_congr' fun direction ↦ ih (next direction)

namespace QuantitativeRealization

variable {Q bd}

/-! ## Syntactic progress under an answer relation -/

/-- Every pending query reachable by a conforming finite trace has at least one allowed response.

This is a syntactic progress condition, not a choice of response or an oracle semantics. It is
stated separately from `ResolvesInUnder`: recursive universal quantification is vacuous when no
answer is allowed. Requiring progress at every conformingly reachable state closes that loophole
without imposing an inhabitant on unreachable or contract-disallowed queries. -/
def TraceProgressUnder (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) (input : α) : Prop :=
  ∀ {state : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) state), trace.Conforms allows →
    ∀ {position : p.A} {next : p.B position → R.machine.State},
    R.machine.view state = Sum.inr ⟨position, next⟩ →
      ∃ direction, allows position direction

/-- Every trace-reachable pending query has at least one typed response. -/
def TraceProgress (R : QuantitativeRealization Q bd) (input : α) : Prop :=
  R.TraceProgressUnder (fun _ _ ↦ True) input

/-- Unrestricted progress is definitionally the all-answers specialization. -/
theorem traceProgress_iff_traceProgressUnder_all (R : QuantitativeRealization Q bd)
    (input : α) :
    R.TraceProgress input ↔ R.TraceProgressUnder (fun _ _ ↦ True) input :=
  Iff.rfl

/-- Every conforming finite answer prefix stays within its bound, every allowed branch resolves
within the same query budget, and every conformingly reachable query admits an allowed response.

The progress conjunct is necessary because `ResolvesInUnder` is otherwise vacuous at a query for
which the contract allows no answer. -/
def RunsWithinUnder (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) (bound : α → ExecutionCost) : Prop :=
  (∀ (input : α) {finish : R.machine.State}
      (trace : ExecutionTrace R (R.machine.init input) finish),
      trace.Conforms allows → R.executionCost input trace ≤ bound input) ∧
    (∀ input, R.machine.ResolvesInUnder allows (bound input).queries
      (R.machine.init input)) ∧
      ∀ input, R.TraceProgressUnder allows input

/-- Unrestricted syntactic resource bounds are the specialization allowing every typed answer. -/
def RunsWithin (R : QuantitativeRealization Q bd) (bound : α → ExecutionCost) : Prop :=
  R.RunsWithinUnder (fun _ _ ↦ True) bound

/-- Unrestricted runs are definitionally the all-answers specialization. -/
theorem runsWithin_iff_runsWithinUnder_all (R : QuantitativeRealization Q bd)
    (bound : α → ExecutionCost) :
    R.RunsWithin bound ↔ R.RunsWithinUnder (fun _ _ ↦ True) bound :=
  Iff.rfl

/-- Relation-restricted exact bounds are monotone pointwise. -/
theorem RunsWithinUnder.mono {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop}
    {bound bound' : α → ExecutionCost} (h : R.RunsWithinUnder allows bound)
    (hbound : ∀ input, bound input ≤ bound' input) : R.RunsWithinUnder allows bound' :=
  ⟨fun input _ trace htrace ↦ le_trans (h.1 input trace htrace) (hbound input),
    fun input ↦ (h.2.1 input).mono (hbound input).2.1, h.2.2⟩

/-- Retrieve the resource inequality for one conforming finite typed trace. -/
theorem RunsWithinUnder.cost_le {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : α → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (input : α) {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) (htrace : trace.Conforms allows) :
    R.executionCost input trace ≤ bound input :=
  h.1 input trace htrace

/-- A restricted resource bound supplies a query bound for every conforming prefix. -/
theorem RunsWithinUnder.traceLength_le {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : α → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (input : α) {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) (htrace : trace.Conforms allows) :
    trace.length ≤ (bound input).queries := by
  rw [← R.queries_executionCost input trace]
  exact (h.cost_le input trace htrace).2.1

/-- Every selected interface inherits the total query bound on a conforming run. -/
theorem RunsWithinUnder.queryCount_le {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : α → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) {label : Type*} [DecidableEq label]
    (labelOf : p.A → label) (interface : label) (input : α) {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) (htrace : trace.Conforms allows) :
    trace.queryCount labelOf interface ≤ (bound input).queries :=
  (trace.queryCount_le_length labelOf interface).trans (h.traceLength_le input trace htrace)

/-- Every selected interface inherits the encoded-traffic bound on a conforming run. -/
theorem RunsWithinUnder.interfaceTraffic_le {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : α → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) {label : Type*} [DecidableEq label]
    (labelOf : p.A → label) (interface : label) (input : α) {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) (htrace : trace.Conforms allows) :
    trace.interfaceTraffic labelOf interface ≤ (bound input).traffic := by
  have hcost : trace.cost.traffic ≤ (bound input).traffic := by
    simpa [executionCost] using (h.cost_le input trace htrace).2.2.1
  exact (trace.interfaceTraffic_le_traffic_cost labelOf interface).trans hcost

/-- Retrieve relation-restricted branchwise resolution. -/
theorem RunsWithinUnder.resolvesIn {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : α → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (input : α) :
    R.machine.ResolvesInUnder allows (bound input).queries (R.machine.init input) :=
  h.2.1 input

/-- Retrieve relation-restricted progress. -/
theorem RunsWithinUnder.traceProgress {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : α → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (input : α) :
    R.TraceProgressUnder allows input :=
  h.2.2 input

/-- Every conformingly reachable pending query has an allowed typed response. -/
theorem RunsWithinUnder.response_exists {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : α → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (input : α) {state : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) state) (htrace : trace.Conforms allows)
    {position : p.A} {next : p.B position → R.machine.State}
    (view_eq : R.machine.view state = Sum.inr ⟨position, next⟩) :
    ∃ direction, allows position direction :=
  h.traceProgress input trace htrace view_eq

/-- Pointwise equivalent answer relations define the same restricted run predicate. -/
theorem runsWithinUnder_congr {R : QuantitativeRealization Q bd}
    {allows allows' : ∀ position, p.B position → Prop} {bound : α → ExecutionCost}
    (hAllows : ∀ position direction, allows position direction ↔ allows' position direction) :
    R.RunsWithinUnder allows bound ↔ R.RunsWithinUnder allows' bound := by
  have hEq : allows = allows' := by
    funext position direction
    exact propext (hAllows position direction)
  cases hEq
  exact Iff.rfl

/-- Exact bounds are monotone pointwise. -/
theorem RunsWithin.mono {R : QuantitativeRealization Q bd}
    {bound bound' : α → ExecutionCost} (h : R.RunsWithin bound)
    (hbound : ∀ input, bound input ≤ bound' input) : R.RunsWithin bound' :=
  RunsWithinUnder.mono h hbound

/-- Retrieve the exact resource inequality for one finite typed trace. -/
theorem RunsWithin.cost_le {R : QuantitativeRealization Q bd}
    {bound : α → ExecutionCost} (h : R.RunsWithin bound) (input : α)
    {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) :
    R.executionCost input trace ≤ bound input :=
  h.1 input trace trace.conforms_all

/-- An exact resource bound supplies a query bound for every syntactic prefix. -/
theorem RunsWithin.traceLength_le {R : QuantitativeRealization Q bd}
    {bound : α → ExecutionCost} (h : R.RunsWithin bound) (input : α)
    {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) :
    trace.length ≤ (bound input).queries := by
  rw [← R.queries_executionCost input trace]
  exact (h.cost_le input trace).2.1

/-- Every selected interface inherits the total query bound of a quantitative run. -/
theorem RunsWithin.queryCount_le {R : QuantitativeRealization Q bd}
    {bound : α → ExecutionCost} (h : R.RunsWithin bound)
    {label : Type*} [DecidableEq label] (labelOf : p.A → label)
    (interface : label) (input : α) {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) :
    trace.queryCount labelOf interface ≤ (bound input).queries :=
  le_trans (trace.queryCount_le_length labelOf interface) (h.traceLength_le input trace)

/-- Every selected interface inherits the total encoded-traffic bound of a quantitative run. -/
theorem RunsWithin.interfaceTraffic_le {R : QuantitativeRealization Q bd}
    {bound : α → ExecutionCost} (h : R.RunsWithin bound)
    {label : Type*} [DecidableEq label] (labelOf : p.A → label)
    (interface : label) (input : α) {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) :
    trace.interfaceTraffic labelOf interface ≤ (bound input).traffic := by
  have hcost : trace.cost.traffic ≤ (bound input).traffic := by
    simpa [executionCost] using (h.cost_le input trace).2.2.1
  exact le_trans (trace.interfaceTraffic_le_traffic_cost labelOf interface) hcost

/-- The query component of a quantitative bound supplies branchwise resolution. -/
theorem RunsWithin.resolvesIn {R : QuantitativeRealization Q bd}
    {bound : α → ExecutionCost} (h : R.RunsWithin bound) (input : α) :
    R.machine.ResolvesIn (bound input).queries (R.machine.init input) :=
  (R.machine.resolvesInUnder_all_iff _ _).mp (h.2.1 input)

/-- A quantitative run satisfies syntactic progress at every trace-reachable state. -/
theorem RunsWithin.traceProgress {R : QuantitativeRealization Q bd}
    {bound : α → ExecutionCost} (h : R.RunsWithin bound) (input : α) :
    R.TraceProgress input :=
  h.2.2 input

/-- Every trace-reachable pending query has a typed response. -/
theorem RunsWithin.response_nonempty {R : QuantitativeRealization Q bd}
    {bound : α → ExecutionCost} (h : R.RunsWithin bound) (input : α)
    {state : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) state)
    {position : p.A} {next : p.B position → R.machine.State}
    (view_eq : R.machine.view state = Sum.inr ⟨position, next⟩) :
    Nonempty (p.B position) :=
  let ⟨direction, _⟩ := h.traceProgress input trace trace.conforms_all view_eq
  ⟨direction⟩

/-- For an implementing realization, the structural query budget also bounds
the actual free interaction syntax on every answer branch. -/
theorem RunsWithin.isTotalRollBound {R : QuantitativeRealization Q bd}
    {bound : α → ExecutionCost} {program : α → FreeM p β}
    (h : R.RunsWithin bound) (implements : R.machine.Implements program)
    (input : α) :
    (program input).IsTotalRollBound (bound input).queries :=
  (R.machine.resolvesIn_iff_isTotalRollBound_of_behavior_eq
    (bound input).queries (R.machine.init input) (program input)
      (implements input)).mp (h.resolvesIn input)

end QuantitativeRealization

/-! ## Program-level predicates and qualitative erasure -/

/-- A program family has an implementing realization with quantitative code for
all three compositional machine maps. This predicate alone asserts no asymptotic
complexity class. -/
def IsQuantitativelyRealizableBy (program : α → FreeM p β) : Prop :=
  ∃ R : QuantitativeRealization Q bd, R.machine.Implements program

/-- A quantitatively realizable program whose conforming interaction prefixes fit a pinned,
input-indexed bound and whose allowed answer branches satisfy resolution and progress. -/
def IsQuantitativelyRealizableWithinUnder
    (allows : ∀ position, p.B position → Prop) (program : α → FreeM p β)
    (bound : α → ExecutionCost) : Prop :=
  ∃ R : QuantitativeRealization Q bd,
    R.machine.Implements program ∧ R.RunsWithinUnder allows bound

/-- Unrestricted program bounds are the specialization allowing every typed answer. -/
def IsQuantitativelyRealizableWithin (program : α → FreeM p β)
    (bound : α → ExecutionCost) : Prop :=
  IsQuantitativelyRealizableWithinUnder Q bd (fun _ _ ↦ True) program bound

/-- Unrestricted program bounds are definitionally the all-answers specialization. -/
theorem isQuantitativelyRealizableWithin_iff_under_all
    (program : α → FreeM p β) (bound : α → ExecutionCost) :
    IsQuantitativelyRealizableWithin Q bd program bound ↔
      IsQuantitativelyRealizableWithinUnder Q bd (fun _ _ ↦ True) program bound :=
  Iff.rfl

namespace IsQuantitativelyRealizableBy

variable {Q bd} {program : α → FreeM p β}

/-- Quantitative realizability erases to qualitative realizability. -/
theorem isRealizableBy (h : IsQuantitativelyRealizableBy Q bd program) :
    IsRealizableBy C bd program := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R.toRealization, hR⟩

end IsQuantitativelyRealizableBy

namespace IsQuantitativelyRealizableWithinUnder

variable {Q bd} {allows : ∀ position, p.B position → Prop}
  {program : α → FreeM p β} {bound : α → ExecutionCost}

/-- Dropping a relation-restricted bound retains quantitative realizability. -/
theorem isQuantitativelyRealizableBy
    (h : IsQuantitativelyRealizableWithinUnder Q bd allows program bound) :
    IsQuantitativelyRealizableBy Q bd program := by
  obtain ⟨R, hR, _⟩ := h
  exact ⟨R, hR⟩

/-- A relation-restricted quantitative realization also erases to the qualitative layer. -/
theorem isRealizableBy
    (h : IsQuantitativelyRealizableWithinUnder Q bd allows program bound) :
    IsRealizableBy C bd program :=
  h.isQuantitativelyRealizableBy.isRealizableBy

/-- Program-level relation-restricted bounds are monotone pointwise. -/
theorem mono {bound' : α → ExecutionCost}
    (h : IsQuantitativelyRealizableWithinUnder Q bd allows program bound)
    (hbound : ∀ input, bound input ≤ bound' input) :
    IsQuantitativelyRealizableWithinUnder Q bd allows program bound' := by
  obtain ⟨R, hR, hcost⟩ := h
  exact ⟨R, hR, hcost.mono hbound⟩

end IsQuantitativelyRealizableWithinUnder

namespace IsQuantitativelyRealizableWithin

variable {Q bd} {program : α → FreeM p β} {bound : α → ExecutionCost}

/-- Dropping an exact bound retains quantitative realizability. -/
theorem isQuantitativelyRealizableBy
    (h : IsQuantitativelyRealizableWithin Q bd program bound) :
    IsQuantitativelyRealizableBy Q bd program := by
  obtain ⟨R, hR, _⟩ := h
  exact ⟨R, hR⟩

/-- A bounded quantitative realization also erases to the qualitative layer. -/
theorem isRealizableBy (h : IsQuantitativelyRealizableWithin Q bd program bound) :
    IsRealizableBy C bd program :=
  h.isQuantitativelyRealizableBy.isRealizableBy

/-- Program-level exact bounds are monotone pointwise. -/
theorem mono {bound' : α → ExecutionCost}
    (h : IsQuantitativelyRealizableWithin Q bd program bound)
    (hbound : ∀ input, bound input ≤ bound' input) :
    IsQuantitativelyRealizableWithin Q bd program bound' := by
  obtain ⟨R, hR, hcost⟩ := h
  exact ⟨R, hR, hcost.mono hbound⟩

end IsQuantitativelyRealizableWithin

end DynSystem.DynComputation

end PFunctor
