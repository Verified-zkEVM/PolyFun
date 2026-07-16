/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Bisim.Bind

/-!
# Relational weak-bisimulation examples

These examples pin the independent universes of the event signature, both
source return types, and both continuation return types. The concrete example
checks that a silent step can be ignored while a non-equality relation compares
distinct return representations, and that the relation is transported through
two-sided `bind` congruence.
-/

@[expose] public section

universe uFA uFB uα uβ uγ uδ

namespace ITree.RelationalBisimExamples

variable {F : PFunctor.{uFA, uFB}} {α : Type uα} {β : Type uβ}
  {γ : Type uγ} {δ : Type uδ}

/-- Relational weak bisimulation accepts return types whose universes are
independent of each other and of both event universes. -/
def separated (RR : α → β → Prop) (left : ITree F α) (right : ITree F β) :
    Prop :=
  WeakBisimRel RR left right

example (RR : α → β → Prop) {a : α} {b : β} (h : RR a b) :
    WeakBisimRel RR (ITree.pure (F := F) a) (ITree.pure (F := F) b) :=
  WeakBisimRel.pure h

example (RR : α → β → Prop) (SS : β → γ → Prop)
    {left : ITree F α} {middle : ITree F β} {right : ITree F γ}
    (h₁ : WeakBisimRel RR left middle)
    (h₂ : WeakBisimRel SS middle right) :
    WeakBisimRel (Relation.Comp RR SS) left right :=
  h₁.comp h₂

/-- The equality-specialized API is definitionally the relational one. -/
example (left right : ITree F α) :
    WeakBisim left right = WeakBisimRel Eq left right :=
  rfl

/-- Finite silent-step stripping must not collapse termination into silent
divergence, in either orientation. -/
example (r : α) :
    ¬ WeakBisim (ITree.pure (F := F) r) (ITree.diverge (F := F)) :=
  WeakBisim.pure_not_diverge r

example (r : α) :
    ¬ WeakBisim (ITree.diverge (F := F)) (ITree.pure (F := F) r) := by
  intro h
  exact WeakBisim.pure_not_diverge r h.symm

example (RR : α → β → Prop) (SS : γ → δ → Prop)
    {left : ITree F α} {right : ITree F β}
    {f : α → ITree F γ} {g : β → ITree F δ}
    (hTree : WeakBisimRel RR left right)
    (hCont : ∀ a b, RR a b → WeakBisimRel SS (f a) (g b)) :
    WeakBisimRel SS (ITree.bind left f) (ITree.bind right g) :=
  ITree.bind_weakBisimRel hTree hCont

example (RR : α → β → Prop) (SS : γ → δ → Prop)
    (f : α → γ) (g : β → δ) {left : ITree F α} {right : ITree F β}
    (hTree : WeakBisimRel RR left right)
    (hMap : ∀ a b, RR a b → SS (f a) (g b)) :
    WeakBisimRel SS (ITree.map f left) (ITree.map g right) :=
  ITree.map_weakBisimRel f g hTree hMap

/-! ## Observable heterogeneous return relation -/

@[reducible] def EmptySpec : PFunctor :=
  ⟨PEmpty, PEmpty.elim⟩

def SourceRel (flag : Bool) (code : Nat) : Prop :=
  flag = true ∧ code = 1

def OutputRel (label : String) (accepted : Bool) : Prop :=
  label = "accepted" ∧ accepted = true

def leftTree : ITree EmptySpec Bool :=
  ITree.step (ITree.pure true)

def rightTree : ITree EmptySpec Nat :=
  ITree.pure 1

theorem leftTree_rightTree : WeakBisimRel SourceRel leftTree rightTree := by
  exact WeakBisimRel.step_left (WeakBisimRel.pure ⟨rfl, rfl⟩)

def leftCont (flag : Bool) : ITree EmptySpec String :=
  ITree.pure (if flag then "accepted" else "rejected")

def rightCont (code : Nat) : ITree EmptySpec Bool :=
  ITree.pure (decide (code = 1))

example : WeakBisimRel OutputRel
    (ITree.bind leftTree leftCont) (ITree.bind rightTree rightCont) := by
  apply ITree.bind_weakBisimRel leftTree_rightTree
  intro flag code h
  rcases h with ⟨rfl, rfl⟩
  exact WeakBisimRel.pure ⟨rfl, rfl⟩

end ITree.RelationalBisimExamples
