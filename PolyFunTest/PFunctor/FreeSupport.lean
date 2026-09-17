/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Support

/-!
# Ordinary-import support boundaries

Free support respects independent result universes and depends on the available answer types.
Continuation congruence uses only weak attachment laws, including for indexed transformers.
-/

public section

open PFunctor MonadAttach

universe uA uB v w

namespace PolyFunTest.PFunctor.FreeSupport

example {P : PFunctor.{uA, uB}} {α : Type v} {β : Type w}
    (f : α → β) (program : FreeM P α) :
    support (FreeM.map f program) = f '' support program := by simp

example {P : PFunctor.{uA, uB}} {α : Type v} (object : P.Obj α) :
    support (FreeM.liftObj object) = Set.range (PFunctor.Obj.snd object) := by simp

example {P : PFunctor.{uA, uB}} [∀ a, Nonempty (P.B a)] {α : Type v}
    (program : FreeM P α) : (support program).Nonempty :=
  FreeM.support_nonempty program

example {P : PFunctor.{uA, uB}} [∀ a, Finite (P.B a)] {α : Type v}
    (program : FreeM P α) : (support program).Finite := by simp

example {m : Type v → Type w} [Monad m] [LawfulMonad m] [MonadAttach m]
    [WeaklyLawfulMonadAttach m] {α β : Type v} (x : m α) {f g : α → m β}
    (h : ∀ a, CanReturn x a → f a = g a) : x >>= f = x >>= g :=
  bind_congr_of_canReturn x h

example (x : StateT Bool Id Nat) {f g : Nat → StateT Bool Id Nat}
    (h : ∀ a ∈ support x, f a = g a) : x >>= f = x >>= g :=
  bind_congr_of_forall_mem_support x h

abbrev emptyP : PFunctor := ⟨Unit, fun _ ↦ Empty⟩

example : support (FreeM.lift (P := emptyP) ()) = ∅ := by
  ext result
  exact result.elim

abbrev infiniteP : PFunctor := ⟨Unit, fun _ ↦ Nat⟩

example : (support (FreeM.lift (P := infiniteP) ())).Infinite := by
  rw [FreeM.support_lift]
  exact Set.infinite_univ

end PolyFunTest.PFunctor.FreeSupport
