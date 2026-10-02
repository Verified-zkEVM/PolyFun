/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Parallel

/-! # Composed read-only reports

Two independent data sources produce reports of unequal lengths. Coproduct injection lets an
application use either source; lockstep composition emits left, right, or joint requests. The
monadic interpreter explicitly executes a joint request left-first. This is not OS threading,
and the order would matter for effectful sources. Source data is immutable; only the audit log
changes. No interchange law for arbitrary handlers is assumed.
-/

@[expose] public section

namespace PolyFunExamples.ParallelReports

open PFunctor

/-- Read one row by stable position. -/
abbrev Rows : PFunctor := ⟨Nat, fun _ => String⟩

/-- Read a numerical limit independently of the rows. -/
abbrev Limit : PFunctor := ⟨Unit, fun _ => Nat⟩

/-- Two queries whose answers contribute to a report. -/
def names : FreeM Rows String := do
  let first ← FreeM.lift (P := Rows) 0
  let second ← FreeM.lift (P := Rows) 1
  return first ++ ", " ++ second

/-- One independent numerical request. -/
def limit : FreeM Limit Nat := FreeM.lift (P := Limit) ()

/-- Audit events distinguish the two sources without conflating data with display text. -/
inductive Event where
  | row (index : Nat)
  | limit
  deriving DecidableEq, Repr

/-- A read-only row source with explicit audit output. -/
def rowsHandler : Handler (StateM (List Event)) Rows := fun index => do
  modify (· ++ [.row index])
  return ["Ada", "Grace"][index]?.getD "missing"

/-- A separate source; no row state or row operations are available here. -/
def limitHandler : Handler (StateM (List Event)) Limit := fun _ => do
  modify (· ++ [.limit])
  return 5

/-- Existing lenses inject component syntax into a larger application interface. -/
def sequential : FreeM (Rows + Limit) (String × Nat) := do
  let label ← names.mapLens (Lens.inl (Q := Limit))
  let bound ← limit.mapLens (Lens.inr (P := Rows))
  return (label, bound)

/-- A joint request followed by a left-only request. -/
def report := FreeM.parallel names limit

/-- The counterpart exercises a joint request followed by a right-only request. -/
def reversed := FreeM.parallel limit names

example : ((sequential.liftM (Handler.sum rowsHandler limitHandler)).run []).run =
    (("Ada, Grace", 5), [.row 0, .row 1, .limit]) := rfl

example : ((report.liftM (Handler.parallelSeq rowsHandler limitHandler)).run []).run =
    (("Ada, Grace", 5), [.row 0, .limit, .row 1]) := rfl

example : ((reversed.liftM (Handler.parallelSeq limitHandler rowsHandler)).run []).run =
    ((5, "Ada, Grace"), [.limit, .row 0, .row 1]) := rfl

end PolyFunExamples.ParallelReports
