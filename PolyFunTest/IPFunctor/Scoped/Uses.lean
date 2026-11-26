/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedPrograms
public import Mathlib.Logic.Function.Basic

/-!
# The constructors a scoped term uses

A small language reads numbers from a tape: `rand i` means the tape's value at position `i`.
A program that does not use `rand i` means the same whatever the tape holds at `i`, and a
program that uses no `rand` means the same under every tape. Both follow from
`Term.denote_congr_of_agreeOn_heads` without an induction over programs. The side conditions
are decided by `decide`, including for a `rand` below a binder. A program that reads the
position changes its meaning when the tape does, so the side condition is needed.

The scoped-program tutorial's let elimination leaves no let, and a let that binds its value's
successor changes the meaning of a program only before elimination.
-/

@[expose] public section

namespace PolyFunTest.Scoped.Uses

open IPFunctor IPFunctor.ScopedSignature

/-- Numbers and functions. -/
inductive Ty where
  | nat
  | arrow (argument result : Ty)
  deriving DecidableEq

/-- Native values interpreting each sort. -/
@[reducible] def Ty.Value : Ty → Type
  | .nat => Nat
  | .arrow a b => a.Value → b.Value

/-- Literals, addition, tape reads, functions and application. -/
inductive Op : Ty → Type where
  | literal (n : Nat) : Op .nat
  | add : Op .nat
  | rand (i : Nat) : Op .nat
  | lam (a b : Ty) : Op (.arrow a b)
  | app (a b : Ty) : Op b
  deriving DecidableEq

/-- Argument positions; literals and tape reads have none. -/
@[reducible] def Op.arity : {a : Ty} → Op a → Nat
  | _, .literal _ | _, .rand _ => 0
  | _, .lam _ _ => 1
  | _, .add | _, .app _ _ => 2

/-- Only a function body binds a variable. -/
@[reducible] def signature : ScopedSignature Ty where
  Op := Op
  Arg op := Fin op.arity
  binders op := match op with
    | .lam a _ => fun _ => [a]
    | _ => fun _ => []
  sort op := match op with
    | .literal _ | .rand _ => Fin.elim0
    | .add => fun _ => .nat
    | .lam _ b => fun _ => b
    | .app a b => Fin.cases (.arrow a b) (fun _ => a)

/-- Whether an operation reads the tape. -/
def Op.isRand : {a : Ty} → Op a → Bool
  | _, .rand _ => true
  | _, _ => false

/-- The meaning of each operation, reading tape positions from `τ`. -/
def algebra (τ : Nat → Nat) : Interpretation signature Ty.Value
  | _, .literal n, _ => n
  | _, .add, next => next 0 Env.empty + next 1 Env.empty
  | _, .rand i, _ => τ i
  | _, .lam _ _, next => fun x => next 0 (Env.cons x Env.empty)
  | _, .app _ _, next => next 0 Env.empty (next 1 Env.empty)

/-- Every head other than `rand i` is interpreted independently of the tape at `i`. -/
theorem algebra_update_of_ne (τ : Nat → Nat) (i x : Nat) (h : signature.Head)
    (hh : h ≠ ⟨.nat, .rand i⟩) : algebra (Function.update τ i x) h.op = algebra τ h.op := by
  obtain ⟨_, op⟩ := h
  cases op with
  | rand j =>
    have hj : j ≠ i := fun e => hh (e ▸ rfl)
    funext next
    exact Function.update_of_ne hj x τ
  | literal n | add | lam a b | app a b => rfl

/-- Heads other than tape reads are interpreted independently of the tape. -/
theorem algebra_eq_of_isRand_eq_false (τ τ' : Nat → Nat) (h : signature.Head)
    (hh : h.op.isRand = false) : algebra τ h.op = algebra τ' h.op := by
  obtain ⟨_, op⟩ := h
  cases op with
  | rand j => cases hh
  | literal n | add | lam a b | app a b => rfl

variable {Γ : List Ty} {a : Ty}

/-- A program that does not read tape position `i` means the same whatever the tape holds
there. -/
theorem denote_update_of_notMem (t : signature.Term Γ a) {i : Nat}
    (ht : ⟨.nat, .rand i⟩ ∉ t.heads) (τ : Nat → Nat) (x : Nat) :
    t.denote (algebra (Function.update τ i x)) = t.denote (algebra τ) :=
  Term.denote_congr_of_agreeOn_heads t fun h hh =>
    algebra_update_of_ne τ i x h fun e => ht (e ▸ hh)

/-- A program that reads no tape position means the same under every tape. -/
theorem denote_eq_of_heads_subset (t : signature.Term Γ a)
    (ht : t.heads ⊆ {h | h.op.isRand = false}) (τ τ' : Nat → Nat) :
    t.denote (algebra τ) = t.denote (algebra τ') :=
  Term.denote_congr_of_heads_subset t ht fun h hh => algebra_eq_of_isRand_eq_false τ τ' h hh

/-! ## Concrete programs -/

/-- A tape read. -/
def rand (i : Nat) : signature.Term Γ .nat := .node (.rand i) (fun p => nomatch p)

/-- A literal. -/
def literal (n : Nat) : signature.Term Γ .nat :=
  .node (.literal n) (fun p => nomatch p)

/-- `(fun x => x + rand 1) 3`: the read of position `1` is below a binder. -/
def readOne : signature.Term [] .nat :=
  .node (.app .nat .nat) (Fin.cases
    (.node (.lam .nat .nat) fun _ => .node .add (Fin.cases (.var .zero) fun _ => rand 1))
    fun _ => literal 3)

/-- `(fun x => x + 2) 3`: no tape reads. -/
def readNone : signature.Term [] .nat :=
  .node (.app .nat .nat) (Fin.cases
    (.node (.lam .nat .nat) fun _ => .node .add (Fin.cases (.var .zero) fun _ => literal 2))
    fun _ => literal 3)

/-- The read of position `1` is found below the binder. -/
example : ⟨.nat, .rand 1⟩ ∈ readOne.heads := by decide

example : ⟨.nat, .rand 0⟩ ∉ readOne.heads := by decide

example : ¬ readOne.heads ⊆ {h | h.op.isRand = false} := by decide

example : readNone.heads ⊆ {h | h.op.isRand = false} := by decide


/-- The side condition is decided, and no induction is needed to use it. -/
example (τ : Nat → Nat) (x : Nat) :
    readOne.denote (algebra (Function.update τ 0 x)) = readOne.denote (algebra τ) :=
  denote_update_of_notMem readOne (by decide) τ x

example (τ τ' : Nat → Nat) : readNone.denote (algebra τ) = readNone.denote (algebra τ') :=
  denote_eq_of_heads_subset readNone (by decide) τ τ'

/-- The program that reads position `1` changes its meaning with the tape at `1`, so the side
condition of `denote_update_of_notMem` cannot be dropped. -/
example : readOne.denote (algebra fun _ => 0) Env.empty = 3 := rfl

example : readOne.denote (algebra (Function.update (fun _ => 0) 1 5)) Env.empty = 8 := rfl

/-- Substitution can add heads: closing a variable with a tape read uses the read. -/
example : ⟨.nat, .rand 0⟩ ∈ ((Term.var .zero : signature.Term [.nat] .nat).substOne
    (rand 0)).heads := by decide

/-- Closing a body by a term keeps out a head that neither uses. -/
example {i : Nat} (body : signature.Term (.nat :: Γ) a) (value : signature.Term Γ .nat)
    (hb : ⟨.nat, .rand i⟩ ∉ body.heads) (hv : ⟨.nat, .rand i⟩ ∉ value.heads) :
    ⟨.nat, .rand i⟩ ∉ (body.substOne value).heads := fun h =>
  (Term.heads_substOne_subset body value h).elim hb hv

/-- Renaming keeps the heads. -/
example (t : signature.Term Γ a) (b : Ty) : (t.weaken b).heads = t.heads := by simp

end PolyFunTest.Scoped.Uses

/-! ## Let elimination in the scoped-program tutorial -/

namespace PolyFunTest.Scoped.UsesLets

open IPFunctor IPFunctor.ScopedSignature Examples.ScopedPrograms

/-- A let at sort `nat` that binds its value's successor; every other operation as in
`algebra`. -/
def shiftedLets : Interpretation signature Ty.Value
  | _, .letE .nat _, next => next 1 (Env.cons (Nat.succ (next 0 Env.empty)) Env.empty)
  | _, op, next => algebra op next

theorem shiftedLets_agree (h : signature.Head) (hh : h.op.isLet = false) :
    shiftedLets h.op = algebra h.op := by
  obtain ⟨_, op⟩ := h
  cases op with
  | letE a b => cases hh
  | literal n | add | lam a b | app a b | loop a n => rfl

example : (eliminateLets captureExample).heads ⊆ {h | h.op.isLet = false} := by decide

example : ¬ captureExample.heads ⊆ {h | h.op.isLet = false} := by decide

/-- The shifted let changes the meaning of a program with a let. -/
example : captureExample.denote shiftedLets Env.empty 3 = 11 := rfl

/-- After let elimination, the meaning does not depend on the let interpretation. -/
example : (eliminateLets captureExample).denote shiftedLets Env.empty 3 = 10 := by
  rw [eliminateLets_denote_of_agree shiftedLets_agree]
  rfl

end PolyFunTest.Scoped.UsesLets
