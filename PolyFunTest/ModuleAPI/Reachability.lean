/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.WP

/-!
# Ordinary-import reachability boundaries

These consumers distinguish admitted responses from structural support, exercise
dependent answer types and independent result universes, and check the direction
of free-handler refinement. Empty answer sets impose no progress obligation.
-/

@[expose] public section

namespace PolyFunTest.ModuleAPI.Reachability

open PFunctor PFunctor.FreeM

universe uA uB uX uY

example {P : PFunctor.{uA, uB}} {X : Type uX} {Y : Type uY}
    (allows : (a : P.A) → P.B a → Prop) (program : FreeM P X)
    (next : X → FreeM P Y) :
    (FreeM.bind program next).reachableUnder allows =
      ⋃ result ∈ program.reachableUnder allows, (next result).reachableUnder allows := by
  rw [reachableUnder_bind']

example {P : PFunctor.{uA, uB}} {X : Type uX} {Y : Type uY}
    (allows : (a : P.A) → P.B a → Prop) (program : FreeM P X) (f : X → Y) :
    (FreeM.map f program).reachableUnder allows = f '' program.reachableUnder allows := by
  rw [reachableUnder_map]

abbrev coinP : PFunctor := ⟨Unit, fun _ => Bool⟩

def ask : FreeM coinP Bool := FreeM.lift ()

example : ask.reachableUnder (fun _ answer => answer = true) = {true} := by
  simp [ask]

example : ask.reachableUnder (fun _ _ => False) = ∅ := by
  simp [ask]

example : ask.LeavesSatisfyUnder (fun _ _ => False) (fun _ => False) := by
  rw [leavesSatisfyUnder_iff_forall_reachable]
  simp [ask]

example : ¬ ask.wpFold (OpSpec.angelicUnder (fun _ _ => False)) (fun _ => True) := by
  rw [wpFold_angelicUnder_iff_exists_reachable]
  simp [ask]

example : false ∈ ask.reachable := by
  simp [reachable, ask]

example : false ∉ ask.reachableUnder (fun _ answer => answer = true) := by
  simp [ask]

abbrev dependentP : PFunctor := ⟨Nat, Fin⟩

def allowsZero : (a : dependentP.A) → dependentP.B a → Prop := fun _ answer => answer.val = 0

example : (FreeM.lift (P := dependentP) 0).reachable = ∅ := by
  ext result
  exact Fin.elim0 result

example : (FreeM.lift (P := dependentP) 2).reachableUnder allowsZero = {0} := by
  ext result
  simp [allowsZero]

example : ((FreeM.lift (P := dependentP) 2).bind fun answer =>
    FreeM.map Fin.val (FreeM.lift (answer.val + 1))).reachableUnder
      allowsZero = {0} := by
  ext result
  simp [allowsZero]

example (program : FreeM coinP Bool) (result : Bool) :
    result ∈ program.reachableUnder (fun _ answer => answer = true) ↔
      ∃ path : Path program,
        Path.AllowedUnder (fun _ answer => answer = true) program path ∧
          program.output path = result := by
  rw [mem_reachableUnder_iff_exists_path]

example (program : FreeM coinP Bool) : program.reachable = MonadAttach.support program := by
  rw [reachable_eq_support]

def chooseTrue : (a : coinP.A) → FreeM coinP (coinP.B a) := fun _ => pure true

example : (ask.liftM chooseTrue).reachable ⊆ ask.reachable :=
  reachable_liftM_subset chooseTrue ask

example : false ∉ (ask.liftM chooseTrue).reachable := by
  rw [ask, FreeM.liftM_lift]
  simp [reachable, chooseTrue]

example : (ask.liftM chooseTrue).reachableUnder (fun _ _ => True) ⊆
    ask.reachableUnder (fun _ answer => answer = true) := by
  apply reachableUnder_liftM_subset chooseTrue
  intro position
  simp [chooseTrue]

end PolyFunTest.ModuleAPI.Reachability
