/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Free

/-!
# Ordinary-import canaries for handler composition

VCVio's `QueryImpl.compose` implements one interface by free programs over another and then runs
those programs in an arbitrary monad; it is `PFunctor.Handler.comp`. These examples check through
ordinary imports that composition targets a monad other than `FreeM`, that its laws hold when the
three interfaces have different position universes, and that a concrete composite into the state
monad computes by `rfl`.
-/

@[expose] public section

universe u v uA₁ uA₂ uA₃

namespace PolyFunTest.ModuleAPI.HandlerComposition

open _root_.PFunctor

section Generic

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
variable {P : PFunctor.{uA₁, u}} {Q : PFunctor.{uA₂, u}} {R : PFunctor.{uA₃, u}}

example (second : Handler m Q) (first : Handler (FreeM Q) P) (a : P.A) :
    second.comp first a = (first a).liftM second := rfl

example (second : Handler m P) : second.comp (Handler.id P) = second := by simp

example (first : Handler (FreeM Q) P) : (Handler.id Q).comp first = first := by simp

example (second : Handler m Q) (first : Handler (FreeM Q) P) {α : Type u} (x : FreeM P α) :
    x.liftM (second.comp first) = (x.liftM first).liftM second := by simp

example (third : Handler m R) (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P) :
    (third.comp second).comp first = third.comp (second.comp first) :=
  Handler.comp_assoc third second first

end Generic

/-! ### A concrete composite into the state monad -/

/-- One request, answered by a number. -/
abbrev counter : PFunctor.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- Answer one request by asking the counter twice and adding the two answers. -/
def twice : Handler (FreeM counter) counter :=
  fun _ => FreeM.liftBind () fun a => FreeM.liftBind () fun b => FreeM.pure (a + b)

/-- A counter in the state monad: answer with the count, then increment it. -/
def tick : Handler (StateM Nat) counter :=
  fun _ => modifyGet fun n => (n, n + 1)

/-- Ask for two answers and return both, in order. -/
def twoQueries : FreeM counter (Nat × Nat) :=
  FreeM.liftBind () fun a => FreeM.liftBind () fun b => pure (a, b)

/-- One composite request reads the counter twice: `3 + 4`, and the count advances by two. -/
example : ((tick.comp twice) ()).run 3 = (7, 5) := rfl

/-- Two composite requests read the counter four times: `0 + 1` and `2 + 3`. -/
example : (twoQueries.liftM (tick.comp twice)).run 0 = ((1, 5), 4) := rfl

/-- The same run, factored through the intermediate free program. -/
example : (twoQueries.liftM (tick.comp twice)).run 0 =
    ((twoQueries.liftM twice).liftM tick).run 0 := by
  rw [Handler.liftM_comp]

end PolyFunTest.ModuleAPI.HandlerComposition
