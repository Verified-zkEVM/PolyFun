/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Sum

/-!
# Ordinary-import canaries for handler sums

VCVio's `QueryImpl.add` and its routing laws are `PFunctor.Handler.sum` and the
`liftM_sum_*` family. These examples check, through ordinary imports, that a sum handler
routes requests by summand, that relabelled programs are interpreted by one component, and that
the laws hold when the two interfaces have different position universes.
-/

@[expose] public section

universe u uA₁ uA₂

namespace PolyFunTest.ModuleAPI.Handler

open _root_.PFunctor

section Generic

variable {P : PFunctor.{uA₁, u}} {Q : PFunctor.{uA₂, u}} {m : Type u → Type u} [Monad m]
  [LawfulMonad m] {α : Type u} (f : Handler m P) (g : Handler m Q)

example (a : P.A) : Handler.sum f g (.inl a) = f a := by simp

example (b : Q.A) : Handler.sum f g (.inr b) = g b := by simp

example (a : P.A) :
    (FreeM.lift (P := (P + Q : PFunctor.{max uA₁ uA₂, u})) (.inl a)).liftM (Handler.sum f g) =
      f a := by
  simp

/-- A program over the left summand, relabelled into the sum, is interpreted by the left
handler alone. -/
example (x : FreeM P α) : (x.mapLens Lens.inl).liftM (Handler.sum f g) = x.liftM f :=
  Handler.liftM_sum_mapLens_inl f g x

/-- The routing laws only inspect the handler's values on the injection. -/
example (h : Handler m (P + Q : PFunctor.{max uA₁ uA₂, u})) (hf : ∀ a, h (.inl a) = f a)
    (x : FreeM P α) : (x.mapLens Lens.inl).liftM h = x.liftM f :=
  Handler.liftM_mapLens_inl_eq_of_apply h f hf x

end Generic

/-! ### A concrete sum: counters and flags in the state monad -/

/-- One interface with a single request answered by a number. -/
abbrev counter : PFunctor.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- One interface with a single request answered by a Boolean. -/
abbrev flag : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- Answer the counter request with the current state and increment it. -/
def tick : Handler (StateM Nat) counter := fun _ =>
  (modifyGet fun n : Nat => (n, n + 1) : StateM Nat Nat)

/-- Answer the flag request by whether the state is even. -/
def isEven : Handler (StateM Nat) flag := fun _ =>
  ((fun n : Nat => n % 2 == 0) <$> get : StateM Nat Bool)

/-- Read the counter twice, then the flag. -/
def program : FreeM (counter + flag) (Nat × Nat × Bool) := do
  let a ← FreeM.lift (P := counter + flag) (.inl ())
  let b ← FreeM.lift (P := counter + flag) (.inl ())
  let c ← FreeM.lift (P := counter + flag) (.inr ())
  pure (a, b, c)

example : Id.run ((program.liftM (Handler.sum tick isEven)).run' 5) = (5, 6, false) := rfl

/-- Lifting both handlers into a shared target and summing agrees with summing after lifting. -/
example : Handler.sumLift (r := StateT Nat Id) tick isEven = Handler.sum tick isEven := rfl

end PolyFunTest.ModuleAPI.Handler
