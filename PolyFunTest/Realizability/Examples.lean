/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Realizability.Closure
public import PolyFun.Realizability.Instances
public import Mathlib.Data.Fintype.Sigma

/-!
# Worked examples of admissible realizability

A hand-built two-state machine realizing a one-query program, checked against the
finite step class, plus smoke tests pinning the owner-module definitional
behaviour behind the public closure laws:

* the flat step maps of `ofStep` read back exactly the supplied step function;
* replacing the initialization leaves every step map definitionally unchanged,
  which is the implementation invariant exposed by the `setInit` laws;
* two one-query programs compose under `bind`, with budgets adding, and the
  composite transition satisfies an equation unconditional in the answer index;
* `StepClass.computable.Hom` really is Mathlib's `Computable`;
* a realization transports from the computable class to the unconstrained one
  along a `StepClass.Refines`.
-/

@[expose] public section

namespace PFunctor.RealizabilityExamples

open PFunctor
open PFunctor.DynSystem
open PFunctor.DynSystem.DynComputation

/-! ## A one-query interface and program -/

/-- A single-query interface: one query, answered by a bit. -/
def coin : PFunctor.{0, 0} :=
  { A := Unit, B := fun _ => Bool }

instance : DecidableEq coin.A := inferInstanceAs (DecidableEq Unit)

/-- Ask the single query once and return its answer. -/
def program : Unit → FreeM coin Bool :=
  fun _ => FreeM.lift ()

/-- The realizing machine: `none` before the query, `some answer` after. Two
states suffice, and the whole machine is given by one step function. -/
def machine : DynComputation.{0} coin Unit Bool :=
  DynComputation.ofStep
    (fun state => match state with
      | none => Sum.inr ⟨(), fun answer => some answer⟩
      | some answer => Sum.inl answer)
    fun _ => none

example : machine.State = Option Bool := rfl

/-! ## The flat step maps read back the supplied step function -/

example : machine.head none = Sum.inr () := rfl

example (answer : Bool) : machine.head (some answer) = Sum.inl answer := rfl

example (answer : Bool) :
    machine.update? (none, ⟨(), answer⟩) = some (some answer) :=
  machine.update?_of_view_query rfl answer

/-- A resolved state takes no step, and neither does a mismatched answer — with a
one-position interface only the former can occur. -/
example (answer : Bool) : ∀ given : Bool,
    machine.update? (some answer, ⟨(), given⟩) = none :=
  fun _ => machine.update?_of_view_return rfl _

/-- The total variant collapses `none` to the unchanged state. -/
example (answer : Bool) : ∀ given : Bool,
    machine.updateFlat (some answer, ⟨(), given⟩) = some answer :=
  fun _ => machine.updateFlat_of_view_return rfl _

example : machine.output none = none := rfl

example (answer : Bool) : machine.output (some answer) = some answer := rfl

/-! ## Finite-state realizability -/

/-- The boundary: every type at the boundary of this statement is finite. -/
def finiteBoundary : Boundary StepClass.finite.{0} coin Unit Bool where
  input := inferInstanceAs (Fintype Unit)
  out := inferInstanceAs (Fintype Bool)
  pos := inferInstanceAs (Fintype Unit)
  idx := inferInstanceAs (Fintype (Σ _ : Unit, Bool))

/-- The machine implements the program within one query. Both sides are the same
`FreeM` term, so the check is definitional. -/
example : machine.ImplementsWithin program 1 := fun _ => rfl

/-- `program` is realizable by a finite-state machine within one query. -/
theorem isRealizableWithin_finite :
    IsRealizableWithin StepClass.finite finiteBoundary program 1 :=
  ⟨{ machine := machine
     state := inferInstanceAs (Fintype (Option Bool))
     init_mem := True.intro
     head_mem := True.intro
     update_mem := True.intro }, fun _ => rfl⟩

/-- The bounded predicate implies the unbounded one. -/
example : IsFiniteStateRealizable finiteBoundary program :=
  isRealizableWithin_finite.isRealizableBy

/-- A bounded realization certifies the program's own query depth. -/
example (input : Unit) : (program input).IsTotalRollBound 1 :=
  isRealizableWithin_finite.isTotalRollBound input

/-- Budget monotonicity. -/
example : IsRealizableWithin StepClass.finite finiteBoundary program 3 :=
  isRealizableWithin_finite.mono (by omega)

/-- Result postcomposition in action: negating the returned bit stays realizable
at the same budget, because mapping a result performs no queries. -/
example :
    IsRealizableWithin StepClass.finite
      (finiteBoundary.withOut (inferInstanceAs (Fintype Bool)))
      (fun input => FreeM.map not (program input)) 1 :=
  isRealizableWithin_finite.mapResult True.intro

/-- Input precomposition in action. -/
example :
    IsRealizableWithin StepClass.finite
      (finiteBoundary.withInput (inferInstanceAs (Fintype Bool)))
      (fun _ : Bool => program ()) 1 :=
  isRealizableWithin_finite.precomp (f := fun _ : Bool => ()) True.intro

/-! ## Closure under `bind`

Two one-query programs compose into a two-query one, and the realizations compose
with them. The budgets add, and the composite machine's state is the coproduct of
the two phases' states.
-/

/-- The second phase: the same machine, reindexed to consume the first phase's
result as its input. -/
def machine₂ : DynComputation.{0} coin Bool Bool :=
  machine.contramapInput fun _ : Bool => ()

/-- Ask the query once, then ask it again — realizable by a finite-state machine
within `1 + 1` queries. -/
example : IsRealizableWithin StepClass.finite
    (finiteBoundary.withOut (inferInstanceAs (Fintype Bool)))
    (fun input => FreeM.bind (program input) fun _ => program ()) (1 + 1) :=
  isRealizableWithin_finite.seqComp
    (isRealizableWithin_finite.precomp (f := fun _ : Bool => ()) True.intro)

/-- The composite machine's state really is the coproduct. -/
example :
    (machine.seqComp machine₂).State = (Option Bool ⊕ Option Bool) := rfl

/-- The composite readout hands a returned intermediate value straight to the
second phase, in the same observation. -/
example (answer : Bool) :
    (machine.seqComp machine₂).head (Sum.inl (some answer)) = Sum.inr () := rfl

/-- And the composite transition is unconditional in the answer index — the
equation that partiality buys. -/
example (answer given : Bool) :
    (machine.seqComp machine₂).update? (Sum.inl (some answer), ⟨(), given⟩) =
      Option.map Sum.inr (machine₂.update? (machine₂.init answer, ⟨(), given⟩)) :=
  machine.update?_seqComp_inl machine₂ (some answer) ⟨(), given⟩

/-! ## Non-vacuity of the unconstrained class -/

example :
    IsRealizableBy StepClass.unconstrained.{0, 0}
      (Boundary.unconstrained coin Unit Bool) program :=
  isRealizableBy_unconstrained program

/-! ## Replacing the initialization is definitionally transparent

These owner-module definitional checks guard the implementation invariant behind
`precomp`: a machine and its reinitialization share every step map on the nose.
Ordinary-import clients consume the named transport laws instead.
-/

section SetInit

variable (M : DynComputation.{0} coin Unit Bool) (g : Bool → M.State)

example : (M.setInit g).head = M.head := rfl

example : (M.setInit g).output = M.output := rfl

example (step : M.State × coin.Idx) :
    (M.setInit g).update? step = M.update? step := rfl

example (step : M.State × coin.Idx) :
    (M.setInit g).updateFlat step = M.updateFlat step := rfl

example (handler : (a : coin.A) → coin.B a) :
    (M.setInit g).stepD handler = M.stepD handler := rfl

end SetInit

/-! ## The computable class is Mathlib's `Computable` -/

example : StepClass.computable.{0}.Hom (A := ℕ) (B := ℕ)
    (inferInstanceAs (Primcodable ℕ)) (inferInstanceAs (Primcodable ℕ)) id :=
  Computable.id

example : StepClass.computable.{0}.Hom (A := ℕ × ℕ) (B := ℕ)
    (inferInstanceAs (Primcodable (ℕ × ℕ))) (inferInstanceAs (Primcodable ℕ))
    Prod.fst :=
  Computable.fst

example : StepClass.computable.{0}.Hom (A := ℕ) (B := ℕ ⊕ ℕ)
    (inferInstanceAs (Primcodable ℕ)) (inferInstanceAs (Primcodable (ℕ ⊕ ℕ)))
    Sum.inl :=
  Primrec.sumInl.to_comp

/-! ## Transport along a refinement of step classes

Every computable machine is in particular an unconstrained one. -/

/-- The computable class refines the unconstrained one. -/
def computableRefinesUnconstrained :
    StepClass.computable.{0}.Refines StepClass.unconstrained.{0, 0} where
  str _ := PUnit.unit
  hom _ := True.intro
  str_prod _ _ := rfl
  str_sum _ _ := rfl
  str_option _ := rfl

example (bd : Boundary StepClass.computable.{0} coin Unit Bool)
    (h : IsRealizableBy StepClass.computable bd program) :
    IsRealizableBy StepClass.unconstrained.{0, 0}
      (bd.mapRefines computableRefinesUnconstrained) program :=
  h.mono computableRefinesUnconstrained

end PFunctor.RealizabilityExamples
