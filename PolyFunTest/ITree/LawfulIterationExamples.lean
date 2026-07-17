/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Bisim.Iter
public import PolyFun.ITree.Do

/-!
# Lawful iteration examples

Compile-time examples for the generic lawful interface and the relational,
universe-polymorphic iteration congruence theorem.
-/

@[expose] public section

universe uFA uFB uα uβ uγ uδ

namespace ITree.LawfulIterationExamples

open scoped ITree

variable {F : PFunctor.{uFA, uFB}}

@[reducible] def EmptySpec : PFunctor :=
  ⟨PEmpty, PEmpty.elim⟩

def oneRestart : Bool → ITree EmptySpec (Bool ⊕ Nat)
  | false => ITree.pure (.inl true)
  | true => ITree.pure (.inr 7)

/-- The concrete computation distinguishes the continue and terminate
branches: one restart contributes exactly one productivity guard. -/
example : ITree.iter oneRestart false =
    ITree.step (ITree.pure (F := EmptySpec) 7) := by
  rw [ITree.iter_unfold, oneRestart, ITree.bind_pure_left]
  change ITree.step (ITree.iter oneRestart true) =
    ITree.step (ITree.pure (F := EmptySpec) 7)
  congr 1
  rw [ITree.iter_unfold, oneRestart, ITree.bind_pure_left]

example {α β : Type uα}
    (body : β → ITree F (β ⊕ α)) (init : β) :
    LawfulMonadIter.Eqv (m := ITree F) (iterM body init)
      (body init >>= fun
        | Sum.inl next => iterM body next
        | Sum.inr result => pure result) :=
  LawfulMonadIter.iter_unfold (m := ITree F) body init

example {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    {RI : β → δ → Prop} {RR : α → γ → Prop}
    {body₁ : β → ITree F (β ⊕ α)} {body₂ : δ → ITree F (δ ⊕ γ)}
    (hbody : ∀ i j, RI i j →
      WeakBisimRel (Sum.LiftRel RI RR) (body₁ i) (body₂ j))
    {init₁ : β} {init₂ : δ} (hinit : RI init₁ init₂) :
    WeakBisimRel RR (iter body₁ init₁) (iter body₂ init₂) :=
  iter_weakBisimRel hbody hinit

example {α β : Type uα}
    (body : α → ITree F (α ⊕ (α ⊕ β))) (init : α) :
    LawfulMonadIter.Eqv (m := ITree F) (iterM (iterM body) init)
      (iterM (fun a => body a >>= fun
        | Sum.inl next => pure (Sum.inl next)
        | Sum.inr (Sum.inl next) => pure (Sum.inl next)
        | Sum.inr (Sum.inr result) => pure (Sum.inr result)) init) :=
  LawfulMonadIter.iter_codiagonal (m := ITree F) body init

/-! ## Productive `while` notation -/

/-- Immediate `break` elaborates through the scoped `ITree` loop instance. -/
def whileBreak : ITree EmptySpec Nat := do
  let mut value := 7
  while true do
    break
  return value

/-- Reassigned variables are threaded through several productive iterations. -/
def whileCount : ITree EmptySpec Nat := do
  let mut count := 0
  while count < 3 do
    count := count + 1
  return count

/-- `continue` uses the continuing branch of `ITree.iter`. -/
def whileContinue : ITree EmptySpec Nat := do
  let mut count := 0
  while count < 3 do
    count := count + 1
    if count < 3 then
      continue
  return count

/-- An early `return` is preserved by Lean's loop-state elaboration. -/
def whileReturn : ITree EmptySpec Nat := do
  while true do
    return 11
  return 0

/-- Compile-time canary for the explicit bridge from `while` elaboration to
the productive `ITree.iter` implementation. -/
example (body : Unit → Nat → ITree EmptySpec (ForInStep Nat)) (init : Nat) :=
  ITree.forInLoop_eq_iter (F := EmptySpec) Lean.Loop.mk init body

end ITree.LawfulIterationExamples
