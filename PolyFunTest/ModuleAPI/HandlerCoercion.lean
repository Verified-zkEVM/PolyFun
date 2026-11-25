/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Sum
public import PolyFun.PFunctor.Handler.Free
import Mathlib.Data.Multiset.Functor
import Mathlib.Algebra.Order.Group.Multiset

/-!
# Function coercion of handlers

`PFunctor.Handler` is a structure that applies like a function. These examples fix, through
ordinary imports, what that coercion does and what it refuses to do:

* a handler is accepted wherever a raw answer function is expected, and no raw function is accepted
  where a handler is expected;
* application lemmas fire at abstract, literal and sum interfaces;
* `+` on handlers is the sum over the sum interface, and `+` on plain functions stays pointwise.
-/

@[expose] public section

namespace PFunctor
namespace HandlerCoercionTest

variable {m n : Type → Type} {P Q : PFunctor.{0, 0}} {ι κ : Type} {B : ι → Type} {C : κ → Type}
variable {σ α : Type}

/-- A consumer of a raw answer function. -/
def wantsFun (_f : (a : P.A) → m (P.B a)) : Unit := ()

/-- A consumer of a family of raw answer functions. -/
def wantsFamily {I : Type} (_f : I → (a : P.A) → m (P.B a)) : Unit := ()

/-! ## Handler to function -/

-- The coercion is inserted, and is the projection itself.
example (h : Handler m P) : wantsFun h = wantsFun h.toFun := rfl

-- CSLib's interpreter takes a raw function, and accepts handlers and their sums.
example [Monad m] (h : Handler m P) (x : FreeM P α) : m α := x.liftM h
example [Monad m] (h : Handler m P) (k : Handler m Q) (x : FreeM (P + Q) α) : m α :=
  x.liftM (h + k)

-- A family of handlers is not a function type, so each member is coerced by hand.
example {I : Type} (h : I → Handler m P) : True := by
  fail_if_success have := wantsFamily h
  have := wantsFamily fun i => ⇑(h i)
  trivial

-- Over-application runs through `StateT`.
example (h : Handler (StateT σ m) P) (a : P.A) (s : σ) : h a s = (h a).run s := rfl

/-! ## Function to handler -/

-- There is no coercion back: a function must be wrapped.
example (f : (a : P.A) → m (P.B a)) : True := by
  fail_if_success have : Handler m P := f
  fail_if_success have : Handler m P := fun a => f a
  have : Handler m P := ⟨f⟩
  trivial

-- Wrapping and coercing are inverse by definition.
example (h : Handler m P) : (⟨fun a => h a⟩ : Handler m P) = h := by with_reducible rfl
example (f : (a : P.A) → m (P.B a)) (a : P.A) : (⟨f⟩ : Handler m P) a = f a := by
  with_reducible rfl

/-! ## Application lemmas -/

example (f : (a : P.A) → m (P.B a)) (a : P.A) : (⟨f⟩ : Handler m P) a = f a := by simp
example (f : (a : ι) → m (B a)) (a : ι) : (⟨f⟩ : Handler m ⟨ι, B⟩) a = f a := by simp
example (t : ∀ {α}, m α → n α) (h : Handler m P) (a : P.A) : h.mapTarget t a = t (h a) := by simp
example (t : ∀ {α}, m α → n α) (h : Handler m ⟨ι, B⟩) (a : ι) : h.mapTarget t a = t (h a) := by simp
example (h k : Handler m ⟨ι, B⟩) (w : ∀ a, h a = k a) (a : ι) : h a = k a := by simp [w]
example (h k : Handler m P) (w : ∀ a, h a = k a) : h = k := by ext a; exact w a
example (h k : Handler m P) (w : ∀ a, h a = k a) (a : P.A) : h a = k a := by grind
example (h k : Handler m P) (w : h = k) (a : P.A) : h a = k a := by grind
example (h k : Handler m P) (w : h = k) (a : P.A) : h a = k a := by rw [w]

/-! ## Sums -/

example (h : Handler m P) (k : Handler m Q) (a : P.A) : (h + k) (.inl a) = h a := by simp
example (h : Handler m P) (k : Handler m Q) (b : Q.A) : (h + k) (.inr b) = k b := by simp
example (h : Handler m P) (k : Handler m Q) (a : P.A) : (h + k) (.inl a) = h a := by grind
example (h : Handler m P) (k : Handler m Q) (l : Handler m P) (b : Q.A) :
    (h + k + l) (.inl (.inr b)) = k b := by grind
example (h : Handler m P) (k : Handler m Q) (l : Handler m P) (b : Q.A) :
    (h + k + l) (.inl (.inr b)) = k b := by rw [Handler.add_inl, Handler.add_inr]

-- The same handler on both sides is a sum over two copies of the interface.
example (h : Handler m P) : Handler m (P + P) := h + h

-- A handler and a raw function do not add.
example (h : Handler m P) (f : (a : Q.A) → m (Q.B a)) : True := by
  have := h
  have := f
  fail_if_success have := h + f
  trivial

-- Plain functions keep pointwise addition, also into a monad with an `Add`.
example (f g : ℕ → Multiset ℕ) : (f + g) 0 = f 0 + g 0 := rfl
example (f g : ℕ → Multiset ℕ) : ℕ → Multiset ℕ := f + g

/-- An interface whose answers can be added. -/
abbrev natPFunctor : PFunctor.{0, 0} := ⟨ℕ, fun _ => ℕ⟩

-- Two handlers still give a sum handler when their answers can be added.
example (h k : Handler Multiset natPFunctor) : Handler Multiset (natPFunctor + natPFunctor) := h + k

-- At an expected function type the elaborator coerces the summands, so `+` is pointwise there.
example (h k : Handler Multiset natPFunctor) (a : ℕ) :
    (h + k : ℕ → Multiset ℕ) a = h a + k a := rfl

/-! ## Kernel reduction

A handler built by its constructor is compared without reducing its answers. -/

/-- A handler whose answers are expensive to reduce. -/
def expensive (n : ℕ) : Handler Id natPFunctor where
  toFun a := if 2 ^ n = 0 then a + 1 else a

/-- A handler that unfolds to `expensive` in one step. -/
def expensive' : Handler Id natPFunctor := expensive (2 ^ 32)

example (a : ℕ) : expensive' a = expensive (2 ^ 32) a := rfl
example : expensive' = expensive (2 ^ 32) := rfl

/-! ## Display -/

/-- info: fun h a ↦ h a : Handler m P → (a : P.A) → m (P.B a) -/
#guard_msgs in
#check fun (h : Handler m P) (a : P.A) ↦ h a

/-- info: fun h ↦ wantsFun ⇑h : Handler m P → Unit -/
#guard_msgs in
#check fun (h : Handler m P) ↦ wantsFun h

end HandlerCoercionTest
end PFunctor
