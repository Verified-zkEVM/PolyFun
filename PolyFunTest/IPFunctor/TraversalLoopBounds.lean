/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.IPFunctor.Free.Fold
public import PolyFun.IPFunctor.Free.Bound.Traversal
public import PolyFun.IPFunctor.Free.Bound.Loops
public import PolyFun.IPFunctor.Free.Tuple

/-!
# Folds over binds, bounds under traversals, and loop bounds

A single-state signature has two shapes, each with Boolean responses. Folding a bind folds each
continuation at its leaf. A traversal into a depth-indexed signature starts at any depth and
increases it at every node, so its target judgment is not a fixed function of the source index;
its charge bounds follow the traversal laws, including for leaves replaced by a node. Loops of
two-index programs through a monad structure on a definitional wrapper, with a `map` of its
own, keep the sum of their step budgets and a predicate on every shape.
-/

@[expose] public section

universe uI uA uB uX uY uD

namespace IPFunctorTraversalLoopBoundsTests

open IPFunctor

/-! ## Fold over bind -/

-- The leaf families of the tree and its continuation and the carrier are independent.
example {I : Type uI} {P : Endo.{uI, uA, uB} I} {X : I → Type uX} {Y : I → Type uY}
    {D : I → Type uD} (leaf : ∀ s, Y s → D s) (alg : FoldAlgebra P D) {s : I}
    (x : IFreeM P X s) (k : ∀ s', X s' → IFreeM P Y s') :
    (x.bind k).fold leaf alg = x.fold (fun s a => (k s a).fold leaf alg) alg :=
  IFreeM.fold_bind leaf alg x k

/-- Two shapes at the sole state, each with a Boolean response. -/
abbrev Cmd : Endo Unit := ⟨fun _ => Bool, fun _ _ => Bool, fun _ _ _ => ()⟩

/-- The `true` response requests one more `true` shape before returning. -/
def program : IFreeM Cmd (fun _ => Unit) () :=
  .liftBind true fun answer => if answer then .liftBind true (fun _ => .pure ()) else .pure ()

/-- The depth of a tree. -/
def depth : FoldAlgebra Cmd (fun _ => ℕ) := fun _ _ k => max (k true) (k false) + 1

example : program.fold (fun _ _ => 0) depth = 2 := rfl

-- The fold of a sequenced tree reads the continuation's depth at every leaf.
example : (program.bind fun _ _ => program).fold (fun _ _ => 0) depth = 4 := by
  rw [IFreeM.fold_bind]
  rfl

/-! ## Bounds under a traversal with changing target judgments -/

/-- One shape at each depth, with Boolean responses that both go one level deeper. -/
abbrev Deep : Endo ℕ := ⟨fun _ => Unit, fun _ _ => Bool, fun n _ _ => n + 1⟩

/-- Map every shape to the shape at the current depth, keeping responses. -/
def deepen : Traversal Cmd Deep (fun _ _ => PUnit.{1}) where
  op _ _ := ()
  arg _ _ b := b
  next _ _ _ := ⟨⟩

/-- Shapes at depth at least two are free. -/
def shallowCharge (n : ℕ) (_ : Deep.A n) : ℕ := if n < 2 then 1 else 0

/-- Pure translated leaves. -/
def pureLeaf {j : ℕ} (_ : PUnit.{1}) (x : Unit) : IFreeM Deep (fun _ => Unit) j :=
  .pure x

/-- Translated leaves that roll one more shape. -/
def nodeLeaf {j : ℕ} (_ : PUnit.{1}) (x : Unit) : IFreeM Deep (fun _ => Unit) j :=
  .liftBind () fun _ => .pure x

lemma deepen_charge_le {i : Unit} {j : ℕ} (s : PUnit.{1}) (a : Cmd.A i) :
    shallowCharge j (deepen.op s a) ≤ 1 := by
  unfold shallowCharge
  split <;> omega

lemma program_isChargeBound : program.IsChargeBound (fun _ _ => 1) 2 := by
  refine ⟨by decide, fun answer => ?_⟩
  cases answer
  · exact trivial
  · exact ⟨le_rfl, fun _ => trivial⟩

lemma nodeLeaf_isChargeBound {j : ℕ} (s : PUnit.{1}) (x : Unit) :
    (nodeLeaf (j := j) s x).IsChargeBound (fun _ _ => 1) 1 :=
  (IFreeM.isChargeBound_liftBind_iff _ _ _).2 ⟨le_rfl, fun _ => trivial⟩

-- From any start depth, the translation costs at most the source.
example (j : ℕ) :
    (program.traverse deepen pureLeaf (j := j) ⟨⟩).IsChargeBound shallowCharge 2 :=
  IFreeM.IsChargeBound.traverse (m := 0) deepen pureLeaf deepen_charge_le
    (fun _ _ => trivial) ⟨⟩ program_isChargeBound

-- Leaves replaced by one node add the leaf budget.
example (j : ℕ) :
    (program.traverse deepen nodeLeaf (j := j) ⟨⟩).IsChargeBound (fun _ _ => 1) 3 :=
  IFreeM.IsChargeBound.traverse deepen nodeLeaf (fun _ _ => le_rfl)
    nodeLeaf_isChargeBound ⟨⟩ program_isChargeBound

-- Without the leaf budget, the source budget is not enough.
example : ¬ (program.traverse deepen nodeLeaf (j := 0) ⟨⟩).IsChargeBound (fun _ _ => 1) 2 := by
  intro h
  obtain ⟨-, h⟩ := (IFreeM.isChargeBound_liftBind_iff _ _ _).1 h
  obtain ⟨-, h⟩ := (IFreeM.isChargeBound_liftBind_iff _ _ _).1 (h true)
  exact absurd ((IFreeM.isChargeBound_liftBind_iff _ _ _).1 (h true)).1 (by decide)

-- Equal charges and surjective response maps make the traversal exact.
example (j n : ℕ) :
    (program.traverse deepen pureLeaf (j := j) ⟨⟩).IsChargeBound (fun _ _ => 1) n ↔
      program.IsChargeBound (fun _ _ => 1) n :=
  IFreeM.isChargeBound_traverse_iff deepen pureLeaf (fun _ _ => Function.surjective_id)
    (fun _ _ => rfl) (fun _ _ => trivial) ⟨⟩ program n

/-- Keep only the source's `false` branch at every node. -/
def prune : Traversal Cmd Deep (fun _ _ => PUnit.{1}) where
  op _ _ := ()
  arg _ _ _ := false
  next _ _ _ := ⟨⟩

-- Preservation permits pruning; the expensive `true` branch no longer appears.
example : (program.traverse prune pureLeaf (j := 0) ⟨⟩).IsChargeBound (fun _ _ => 1) 1 :=
  ⟨le_rfl, fun _ => trivial⟩

-- Reflection without surjectivity would incorrectly bound the source by one.
example : ¬ program.IsChargeBound (fun _ _ => 1) 1 := by
  intro h
  exact absurd (h.2 true).1 (by decide)

example : ¬ Function.Surjective (prune.arg (i := ()) (j := 0) ⟨⟩ true) := by
  intro h
  obtain ⟨b, hb⟩ := h true
  cases hb

-- Reflection needs no bound on translated leaves, even when they add a charged node.
example (j : ℕ)
    (h : (program.traverse deepen nodeLeaf (j := j) ⟨⟩).IsChargeBound (fun _ _ => 1) 3) :
    program.IsChargeBound (fun _ _ => 1) 3 :=
  IFreeM.IsChargeBound.of_traverse deepen nodeLeaf (fun _ _ => Function.surjective_id)
    (fun _ _ => le_rfl) h

/-- Responses are preserved in state `true`; every child stays in that state. -/
def guarded : Traversal Cmd Deep (fun _ _ => Bool) where
  op _ _ := ()
  arg s _ b := if s then b else false
  next _ _ _ := true

-- Global surjectivity fails in the state excluded by the budget relation.
example : ¬ Function.Surjective (guarded.arg (i := ()) (j := 0) false true) := by
  intro h
  obtain ⟨b, hb⟩ := h true
  cases hb

-- Local response witnesses suffice for reflection from the invariant state.
example (j n : ℕ)
    (h : (program.traverse guarded (fun _ x => .pure x) (j := j) true).IsChargeBound
      (fun _ _ => 1) n) : program.IsChargeBound (fun _ _ => 1) n := by
  refine IFreeM.IsRollBound.of_traverse_of_exists guarded (fun _ x => .pure x)
    (fun s n' n => s = true ∧ n' ≤ n) ?_ ?_ h ⟨rfl, le_rfl⟩
  · intro i j s a b' b hR hcan
    exact hcan.trans hR.2
  · intro i j s a b' b hR hcan answer
    refine ⟨answer, ?_, rfl, ?_⟩
    · simp only [guarded, hR.1, ↓reduceIte]
    · exact Nat.sub_le_sub_right hR.2 1

/-! ## Loops through a monad structure on a wrapper -/

/-- Programs that return to the sole state, behind a definitional wrapper. -/
def Prog (α : Type) : Type 1 := FreeM₂ Cmd () () α

/-- A monad structure on the wrapper, with `map` through `bind`. -/
instance : Monad Prog where
  pure a := FreeM₂.pure a
  bind x g := FreeM₂.bind x g
  map f x := FreeM₂.bind x fun a => FreeM₂.pure (f a)

/-- The wrapper's `pure` and `bind` are those of `FreeM₂`. -/
lemma prog_isDiagonalMonad :
    FreeM₂.IsDiagonalMonad (P := Cmd) (s := ()) (inferInstance : Monad Prog) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- One shape `a`, returning the conjunction of the accumulator with the response. -/
def step (a : Bool) (acc : Bool) : Prog Bool :=
  FreeM₂.liftBind (P := Cmd) (s := ()) a fun b => FreeM₂.pure (acc && b)

/-- Roll the `true` shape on a `true` item and return at once otherwise. -/
def check (acc : Bool) (e : Bool) : Prog Bool := if e then step true acc else pure acc

/-- Run the checks of a list in order. -/
def checkAll (l : List Bool) : Prog Bool := l.foldlM check true

/-- Roll the `true` shape once per item. -/
def stepAll (l : List Bool) : Prog Bool := l.foldlM (fun acc _ => step true acc) true

/-- Count the `true` shapes. -/
def trueCharge (_ : Unit) (a : Cmd.A ()) : ℕ := if a then 1 else 0

lemma step_isChargeBound (acc : Bool) : FreeM₂.IsChargeBound (step true acc) trueCharge 1 :=
  ⟨le_rfl, fun _ => trivial⟩

lemma check_isChargeBound (acc e : Bool) :
    FreeM₂.IsChargeBound (check acc e) trueCharge (if e then 1 else 0) := by
  cases e
  · exact trivial
  · exact step_isChargeBound acc

lemma check_isRollBound (acc e : Bool) :
    FreeM₂.IsRollBound (check acc e) () (fun _ a _ => a = true) (fun _ _ b => b) := by
  cases e
  · exact trivial
  · exact ⟨rfl, fun _ => trivial⟩

-- Only the items that roll a shape count, as in a filtered sum.
example : FreeM₂.IsChargeBound (checkAll [true, false, true]) trueCharge 2 := by
  unfold checkAll
  exact FreeM₂.isChargeBound_foldlM prog_isDiagonalMonad (fun e : Bool => if e then 1 else 0)
    check_isChargeBound _ _

-- A uniform step budget gives the length times the budget.
example (l : List Bool) : FreeM₂.IsChargeBound (stepAll l) trueCharge l.length := by
  unfold stepAll
  have h := FreeM₂.isChargeBound_foldlM_of_forall prog_isDiagonalMonad
    (fun acc (_ : Bool) => step_isChargeBound acc) l true
  rw [Nat.mul_one] at h
  exact h

-- Every shape a check rolls is `true`, so every shape of the loop is.
example (l : List Bool) :
    FreeM₂.IsRollBound (checkAll l) () (fun _ a _ => a = true) (fun _ _ b => b) := by
  unfold checkAll
  exact FreeM₂.isRollBound_foldlM_unit prog_isDiagonalMonad check_isRollBound l true

/-- A tuple prefix: position `i` holds a value below `i + 1`. -/
abbrev Prefix (i : Fin 4) : Type := Fin (i.val + 1)

/-- Roll the `true` shape and keep the value, now below one more. -/
def grow (i : Fin 3) (x : Prefix i.castSucc) : Prog (Prefix i.succ) :=
  FreeM₂.liftBind (P := Cmd) (s := ()) true fun _ => FreeM₂.pure x.castSucc

/-- Three growth steps from zero. -/
def growAll : Prog (Prefix (Fin.last 3)) := Fin.dfoldlM 3 Prefix grow 0

lemma grow_isChargeBound (i : Fin 3) (x : Prefix i.castSucc) :
    FreeM₂.IsChargeBound (grow i x) trueCharge 1 :=
  ⟨le_rfl, fun _ => trivial⟩

lemma grow_isRollBound (i : Fin 3) (x : Prefix i.castSucc) :
    FreeM₂.IsRollBound (grow i x) () (fun _ a _ => a = true) (fun _ _ b => b) :=
  ⟨rfl, fun _ => trivial⟩

-- A dependent left fold of three steps of budget one.
example : FreeM₂.IsChargeBound growAll trueCharge 3 := by
  unfold growAll
  exact FreeM₂.isChargeBound_dfoldlM_of_forall prog_isDiagonalMonad grow_isChargeBound 0

-- Per-step budgets add as a finite sum.
example : FreeM₂.IsChargeBound growAll trueCharge (∑ _ : Fin 3, 1) := by
  unfold growAll
  exact FreeM₂.isChargeBound_dfoldlM prog_isDiagonalMonad (fun _ => 1) grow_isChargeBound 0

-- The predicate on shapes is preserved by the dependent fold.
example : FreeM₂.IsRollBound growAll () (fun _ a _ => a = true) (fun _ _ b => b) := by
  unfold growAll
  exact FreeM₂.isRollBound_dfoldlM_unit prog_isDiagonalMonad grow_isRollBound 0

/-! ## A dependent tuple of programs -/

/-- Position `i` of the tuple holds a value below `i + 1`. -/
abbrev Slot (i : Fin 3) : Type := Fin (i.val + 1)

/-- Roll the `true` shape; return the top value on `true` and zero on `false`. -/
def draw (i : Fin 3) : Prog (Slot i) :=
  FreeM₂.liftBind (P := Cmd) (s := ()) true fun b =>
    FreeM₂.pure (if b then Fin.last i.val else 0)

/-- Sequence the three draws into a dependent tuple. -/
def drawAll : Prog ((i : Fin 3) → Slot i) := FreeM₂.seqPi draw

/-- Run a program, answering `true` to every shape. -/
def answerTrue {α : Type} (x : Prog α) : α :=
  IFreeM.fold (D := fun _ => α) (fun _ p => p.2) (fun _ _ k => k true) x

-- The tuple holds a value of a different type at each position.
example : answerTrue drawAll 0 = (0 : Fin 1) := rfl
example : answerTrue drawAll 1 = (1 : Fin 2) := rfl
example : answerTrue drawAll 2 = (2 : Fin 3) := rfl

-- The constructor equations.
example {β : Fin 0 → Type} (f : (i : Fin 0) → Prog (β i)) :
    FreeM₂.seqPi f = FreeM₂.pure fun i => i.elim0 :=
  FreeM₂.seqPi_zero f
example : drawAll = (draw 0).bind fun b => (FreeM₂.seqPi fun i => draw i.succ).bind fun bs =>
    FreeM₂.pure (Fin.cons b bs) :=
  FreeM₂.seqPi_succ draw

/-- A tuple sequencer written separately, through the monad structure of the wrapper. -/
def tuple : {k : ℕ} → {β : Fin k → Type} → ((i : Fin k) → Prog (β i)) →
    Prog ((i : Fin k) → β i)
  | 0, _, _ => pure fun i => i.elim0
  | _ + 1, _, f => f 0 >>= fun a => tuple (fun i => f i.succ) >>= fun as => pure (Fin.cons a as)

-- Its two equations hold by definition, so it is the generic sequencer.
example {k : ℕ} {β : Fin k → Type} (f : (i : Fin k) → Prog (β i)) :
    tuple f = FreeM₂.seqPi f :=
  FreeM₂.seqPi_unique (fun f => tuple f) (fun _ => rfl) (fun _ => rfl) f

lemma draw_isChargeBound (i : Fin 3) : FreeM₂.IsChargeBound (draw i) trueCharge 1 :=
  ⟨le_rfl, fun _ => trivial⟩

lemma draw_isRollBound (i : Fin 3) :
    FreeM₂.IsRollBound (draw i) () (fun _ a _ => a = true) (fun _ _ b => b) :=
  ⟨rfl, fun _ => trivial⟩

-- Per-position budgets add as a finite sum.
example : FreeM₂.IsChargeBound drawAll trueCharge (∑ _ : Fin 3, 1) :=
  FreeM₂.isChargeBound_seqPi (fun _ => 1) draw_isChargeBound

-- A uniform budget gives the length times the budget.
example : FreeM₂.IsChargeBound drawAll trueCharge 3 :=
  FreeM₂.isChargeBound_seqPi_of_forall draw_isChargeBound

-- The predicate on shapes holds throughout the tuple.
example : FreeM₂.IsRollBound drawAll () (fun _ a _ => a = true) (fun _ _ b => b) :=
  FreeM₂.isRollBound_seqPi_unit draw_isRollBound

end IPFunctorTraversalLoopBoundsTests
