/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.IPFunctor.Free.Bound.Substitution

/-!
# Indexed command substitution and charge regressions

Boolean responses determine the next state. The leaf family depends on that
state, and one branch terminates earlier than the other. Replacements have two
nodes or return immediately; label charges count matching shapes on each path.
A nonidentity lens changes responses across independent target universes.
-/

@[expose] public section

namespace IPFunctorSubstitutionTests

open IPFunctor

/-- A shape and response at either Boolean state, moving to the response state. -/
abbrev steps : Endo Bool where
  A _ := Bool
  B _ _ := Bool
  src _ _ b := b

/-- A nonconstant leaf family. -/
abbrev Result (s : Bool) := Fin (if s then 2 else 1)

/-- A leaf payload available at either state. -/
def result (s : Bool) : Result s := ⟨0, by cases s <;> decide⟩

/-- A two-level tree with a shorter branch on the false response. -/
def tree : IFreeM steps Result false :=
  .liftBind false fun b => if b then
    .liftBind true (fun t => .pure (result t)) else .pure (result b)

/-- Replace each shape by two occurrences, returning the second response. -/
def twice : CommandSubstitution steps steps :=
  fun _ a => .liftBind a fun _ => .liftBind a fun b => .pure ⟨b, rfl⟩

example (s : Bool) (x : Result s) :
    (IFreeM.pure (P := steps) x).substitute twice = .pure x := by simp

-- The public constructor equations compute through both replacement nodes.
example (s a : Bool) (next : (b : Bool) → IFreeM steps Result b) :
    (IFreeM.liftBind (s := s) a next).substitute twice =
      .liftBind a (fun _ => .liftBind a (fun b => (next b).substitute twice)) := by
  simp [twice]

-- Sequencing can change the leaf universe after substitution.
example :
    (tree.bind (fun _ _ => IFreeM.pure (ULift.up.{1} Nat.zero))).substitute twice =
      (tree.substitute twice).bind (fun _ _ => .pure (ULift.up.{1} Nat.zero)) := by
  simp only [IFreeM.substitute_bind, IFreeM.substitute_pure]

example : tree.substitute (Lens.id steps).toSubstitution = tree.mapLens (Lens.id steps) := by
  simp only [IFreeM.substitute_toSubstitution]

/-- A target with larger, independent shape and response universes. -/
abbrev flippedSteps : Endo Bool where
  A _ := ULift.{1} Bool
  B _ _ := ULift.{2} Bool
  src _ _ b := !b.down

/-- Both the shape and the returned response change under this lens. -/
def flipLens : Lens steps flippedSteps where
  toFunA _ a := ⟨!a⟩
  toFunB _ _ b := !b.down
  src_eq _ _ _ := rfl

-- The lens bridge computes a nonidentity response map at a dependent leaf family.
example (s a : Bool) (next : (b : Bool) → IFreeM steps Result b) :
    (IFreeM.liftBind (s := s) a next).substitute flipLens.toSubstitution =
      .liftBind ⟨!a⟩ (fun b => (next (!b.down)).mapLens flipLens) := by
  rw [IFreeM.substitute_toSubstitution, IFreeM.mapLens_liftBind]
  rfl

-- The constructor equation holds definitionally.
example (s a : Bool) (next : (b : Bool) → IFreeM steps Result b) :
    (IFreeM.liftBind (s := s) a next).substitute twice =
      .liftBind a (fun _ => .liftBind a (fun b => (next b).substitute twice)) := rfl

/-- Each shape has its own unit charge. -/
def labelCharge (i : Bool) : (s : Bool) → steps.A s → ℕ :=
  fun _ a => if i = a then 1 else 0

theorem tree_label_bound (i : Bool) : tree.IsChargeBound (labelCharge i) 1 := by
  cases i <;> simp [tree, labelCharge, IFreeM.isChargeBound_liftBind_iff, Bool.forall_bool]

-- Adding the simultaneous label budgets gives a total path budget of two.
theorem tree_total_bound : tree.IsChargeBound (fun _ _ => 1) 2 := by
  have h := IFreeM.isChargeBound_sum labelCharge (fun _ => 1) tree_label_bound
  have hc : (fun s a => ∑ i, labelCharge i s a) = (fun _ _ => 1) := by
    funext s a
    cases a <;> simp [labelCharge]
  rw [hc] at h
  simpa only [Fintype.sum_bool, Nat.reduceAdd] using h

theorem twice_bound (s a : Bool) : (twice s a).IsChargeBound (fun _ _ => 1) 2 := by
  simp [twice, IFreeM.isChargeBound_liftBind_iff]

-- Local budgets transport to the substituted tree without enlarging the source budget.
example : (tree.substitute twice).IsChargeBound (fun _ _ => 1) 4 := by
  have h : tree.IsChargeBound (fun _ _ => 2) 4 := tree_total_bound.mul 2
  exact h.substitute twice twice_bound

-- The same replacement cost is a uniform factor of two on unit source charges.
example : (tree.substitute twice).IsChargeBound (fun _ _ => 1) 4 :=
  tree_total_bound.substitute_mul twice 2 twice_bound

-- A smaller budget fails on the branch that traverses all four replacement nodes.
example : ¬ (tree.substitute twice).IsChargeBound (fun _ _ => 1) 3 := by
  simp [tree, twice, IFreeM.isChargeBound_liftBind_iff, Bool.forall_bool]

-- Empty label families and a zero scale both give the zero charge bound.
example : tree.IsChargeBound (fun _ _ => 0) 0 := by
  simpa using IFreeM.isChargeBound_sum (ι := Empty) (fun i => nomatch i)
    (fun i => nomatch i) (x := tree) (fun i => nomatch i)

example : tree.IsChargeBound (fun _ _ => 0) 0 := tree_total_bound.mul 0

/-- Return the current state without rolling a target command. -/
def skip : CommandSubstitution steps steps := fun s _ => .pure ⟨s, rfl⟩

-- Zero-cost replacements discharge the zero-factor theorem, including nonempty sources.
example : (tree.substitute skip).IsChargeBound (fun _ _ => 1) 0 :=
  tree_total_bound.substitute_mul skip 0 (by simp [skip])

-- With the false response returned by skip, the shorter source branch is selected.
example : tree.substitute skip = .pure (result false) := by
  simp [tree, skip]

-- Charge transport allows the target's shape and response universes to differ from the source.
example : (tree.substitute flipLens.toSubstitution).IsChargeBound (fun _ _ => 1) 2 :=
  tree_total_bound.substitute flipLens.toSubstitution
    (by simp [Lens.toSubstitution, IFreeM.isChargeBound_liftBind_iff])

end IPFunctorSubstitutionTests
