/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded
public import PolyFun.PFunctor.Dynamical.Run

/-!
# Syntactic machine execution prefixes

An `ExecutionTrace` records an enabled query, its typed answer, and the residual
execution. Both endpoints are indices. Prefixes can stop before termination and
therefore retain work and observations from diverging or aborted executions.
The carrier needs no interpretation, state representation, or resource backend.
-/

public section

universe u uA uB uα uβ

namespace PFunctor.DynSystem.DynComputation

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-- A finite, fully syntactic query-answer prefix of a returning machine.

The indices are the starting and ending hidden states. `nil` observes no query.
`query` records the exposed dependent position, one typed answer, and the rest
of the prefix. Its `view_eq` proof ensures that every transition answers the
operation exposed at its source state. -/
inductive ExecutionTrace (machine : DynComputation.{u} p α β) :
    machine.State → machine.State → Type (max u uA uB) where
  /-- The empty prefix at a state. -/
  | nil (state : machine.State) : ExecutionTrace machine state state
  /-- Extend a prefix by one exposed query and typed answer. -/
  | query {state : machine.State} {position : p.A}
      {next : p.B position → machine.State} {finish : machine.State}
      (view_eq : machine.view state = Sum.inr ⟨position, next⟩)
      (direction : p.B position)
      (tail : ExecutionTrace machine (next direction) finish) :
      ExecutionTrace machine state finish

namespace ExecutionTrace

variable {machine : DynComputation.{u} p α β}

/-- A computational query view is the underlying system's operation-first output. -/
theorem out_eq_of_view_query {state : machine.State} {position : p.A}
    {next : p.B position → machine.State}
    (h : machine.view state = .inr ⟨position, next⟩) :
    machine.toDynSystem.out state = ⟨.inl position, next⟩ := by
  calc
    machine.toDynSystem.out state = Resumption.pack (machine.view state) :=
      (Resumption.pack_unpack _).symm
    _ = _ := by rw [h]; rfl

/-- Every response recorded by a syntactic trace satisfies a dependent answer relation.

The relation is supplied externally, so this predicate can express an oracle contract without
changing the fully syntactic trace type or pretending that disallowed answers do not exist. -/
@[expose] def Conforms (allows : ∀ position, p.B position → Prop)
    {start finish : machine.State} : ExecutionTrace machine start finish → Prop
  | .nil _ => True
  | .query (position := position) _ direction tail =>
      allows position direction ∧ tail.Conforms allows

/-- An empty prefix satisfies every answer contract. -/
@[simp] theorem conforms_nil (allows : ∀ position, p.B position → Prop)
    (state : machine.State) : (nil state).Conforms allows := trivial

/-- Conformance checks the first answer and the remaining prefix. -/
@[simp] theorem conforms_query (allows : ∀ position, p.B position → Prop)
    {state finish : machine.State} {position : p.A} {next : p.B position → machine.State}
    (h : machine.view state = .inr ⟨position, next⟩) (direction : p.B position)
    (tail : ExecutionTrace machine (next direction) finish) :
    (query h direction tail).Conforms allows ↔
      allows position direction ∧ tail.Conforms allows := Iff.rfl

/-- Every syntactic trace conforms to the relation that allows every typed answer. -/
theorem conforms_all {start finish : machine.State}
    (trace : ExecutionTrace machine start finish) :
    trace.Conforms (fun _ _ ↦ True) := by
  induction trace with
  | nil => trivial
  | query view_eq direction tail ih => exact ⟨trivial, ih⟩

/-- Conformance is monotone under pointwise enlargement of the allowed-answer relation. -/
theorem Conforms.mono {allows allows' : ∀ position, p.B position → Prop}
    (hAllows : ∀ position direction, allows position direction → allows' position direction)
    {start finish : machine.State} {trace : ExecutionTrace machine start finish}
    (h : trace.Conforms allows) : trace.Conforms allows' := by
  induction trace with
  | nil => trivial
  | query view_eq direction tail ih => exact ⟨hAllows _ _ h.1, ih h.2⟩

/-- Number of visible query-answer transitions in a prefix. -/
@[expose] def length {start finish : machine.State} : ExecutionTrace machine start finish → ℕ
  | .nil _ => 0
  | .query _ _ tail => tail.length + 1

/-- The length-indexed orbit represented by an endpoint-indexed execution trace. -/
def toPrefix {start finish : machine.State} (trace : ExecutionTrace machine start finish) :
    Prefix machine.toDynSystem start trace.length :=
  match trace with
  | .nil _ => .nil
  | .query h direction tail =>
      .stepOfOut (out_eq_of_view_query h) direction tail.toPrefix

@[simp] theorem toPrefix_nil (state : machine.State) :
    (nil state).toPrefix = .nil := by rw [toPrefix]

@[simp] theorem toPrefix_query {state finish : machine.State} {position : p.A}
    {next : p.B position → machine.State} (h : machine.view state = .inr ⟨position, next⟩)
    (answer : p.B position) (tail : ExecutionTrace machine (next answer) finish) :
    (query h answer tail).toPrefix =
      .stepOfOut (out_eq_of_view_query h) answer tail.toPrefix := by rw [toPrefix]

/-- The orbit bridge preserves the trace's final state. -/
@[simp] theorem last_toPrefix {start finish : machine.State}
    (trace : ExecutionTrace machine start finish) : trace.toPrefix.last = finish := by
  induction trace with
  | nil => rfl
  | query h direction tail ih =>
      exact (Prefix.last_stepOfOut (out_eq_of_view_query h) direction tail.toPrefix).trans ih

/-- The empty prefix has length zero. -/
@[simp] theorem length_nil (state : machine.State) : (nil state).length = 0 := rfl

/-- Extending a prefix consumes one visible query. -/
@[simp] theorem length_query {state finish : machine.State} {position : p.A}
    {next : p.B position → machine.State} (h : machine.view state = .inr ⟨position, next⟩)
    (direction : p.B position) (tail : ExecutionTrace machine (next direction) finish) :
    (query h direction tail).length = tail.length + 1 := rfl

/-- Every execution prefix fits within a branchwise resolution budget at its start. -/
theorem length_le_of_resolvesIn {start finish : machine.State} {budget : ℕ}
    (trace : ExecutionTrace machine start finish) (resolves : machine.ResolvesIn budget start) :
    trace.length ≤ budget := by
  induction trace generalizing budget with
  | nil => simp [length]
  | @query state position next finish view_eq direction tail ih =>
      cases budget with
      | zero =>
          exact False.elim
            (machine.not_resolvesIn_query_zero state position next view_eq resolves)
      | succ budget =>
          exact Nat.succ_le_succ (ih
            ((machine.resolvesIn_query_succ_iff budget state position next view_eq).mp
              resolves direction))

/-- Number of query-answer transitions carrying one selected interface label. -/
@[expose] def queryCount {label : Type*} [DecidableEq label] (labelOf : p.A → label)
    (interface : label) {start finish : machine.State} :
    ExecutionTrace machine start finish → ℕ
  | .nil _ => 0
  | .query (position := position) _ _ tail =>
      if labelOf position = interface then tail.queryCount labelOf interface + 1
      else tail.queryCount labelOf interface

/-- A selected interface cannot account for more queries than occur in the whole trace. -/
theorem queryCount_le_length {label : Type*} [DecidableEq label]
    (labelOf : p.A → label) (interface : label)
    {start finish : machine.State} (trace : ExecutionTrace machine start finish) :
    trace.queryCount labelOf interface ≤ trace.length := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih =>
      simp only [queryCount, length]
      split <;> omega

/-- Concatenate two adjacent execution prefixes. -/
@[expose] def append {start middle finish : machine.State}
    (left : ExecutionTrace machine start middle) (right : ExecutionTrace machine middle finish) :
    ExecutionTrace machine start finish :=
  match left with
  | .nil _ => right
  | .query view_eq direction tail => .query view_eq direction (tail.append right)

/-- Appending an empty trace preserves the original prefix. -/
@[simp] theorem append_nil {start finish : machine.State}
    (trace : machine.ExecutionTrace start finish) : trace.append (.nil finish) = trace := by
  induction trace with
  | nil => rfl
  | query hv answer tail ih => simp only [append, ih]

/-- Concatenating adjacent traces is associative. -/
theorem append_assoc {start first second finish : machine.State}
    (left : machine.ExecutionTrace start first) (middle : machine.ExecutionTrace first second)
    (right : machine.ExecutionTrace second finish) :
    (left.append middle).append right = left.append (middle.append right) := by
  induction left with
  | nil => rfl
  | query hv answer tail ih => simp only [append, ih]


/-- Adjacent execution prefixes have additive lengths. -/
@[simp] theorem length_append {start middle finish : machine.State}
    (left : ExecutionTrace machine start middle) (right : ExecutionTrace machine middle finish) :
    (left.append right).length = left.length + right.length := by
  induction left with
  | nil => simp [append]
  | query h direction tail ih => simp [append, ih, Nat.add_right_comm]

/-- Conformance composes under concatenation of adjacent traces. -/
theorem conforms_append {allows : ∀ position, p.B position → Prop}
    {start middle finish : machine.State}
    (left : ExecutionTrace machine start middle) (right : ExecutionTrace machine middle finish) :
    (left.append right).Conforms allows ↔ left.Conforms allows ∧ right.Conforms allows := by
  induction left with
  | nil => simp [append, Conforms]
  | query view_eq direction tail ih => simp [append, Conforms, ih, and_assoc]

/-- Per-interface query counts add under trace concatenation. -/
theorem queryCount_append {label : Type*} [DecidableEq label]
    (labelOf : p.A → label) (interface : label)
    {start middle finish : machine.State}
    (left : ExecutionTrace machine start middle) (right : ExecutionTrace machine middle finish) :
    (left.append right).queryCount labelOf interface =
      left.queryCount labelOf interface + right.queryCount labelOf interface := by
  induction left with
  | nil => simp [append, queryCount]
  | query view_eq direction tail ih =>
      simp only [append, queryCount]
      split <;> simp [ih, Nat.add_left_comm, Nat.add_comm]

end ExecutionTrace
end PFunctor.DynSystem.DynComputation
