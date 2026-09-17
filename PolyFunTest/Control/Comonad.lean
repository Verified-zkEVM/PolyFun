/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Comonad.Instances
import PolyFun.PFunctor.Cofree

/-! # Comonads and independent choices of context pairing

Generic comonad consumers and transformers need no pairing policy. Concrete
pairing instances retain their chosen behavior and share the functor operations.
-/

@[expose] public section

universe u v

example (w : Type u → Type v) [Comonad w] : True := by
  fail_if_success have : Coapplicative w := inferInstance
  trivial

example (w : Type u → Type v) [Comonad w] [LawfulComonad w] (ε : Type u) :
    LawfulComonad (EnvT ε w) := inferInstance

example (w : Type u → Type v) [Comonad w] [LawfulComonad w] (σ : Type u) :
    LawfulComonad (StoreT σ w) := inferInstance

example (w : Type u → Type v) [Coapplicative w] [LawfulCoapplicative w] (σ : Type u) :
    LawfulCoapplicative (StoreT σ w) := inferInstance

/-- A consumer can request pairing without choosing a second functor or extraction. -/
example (w : Type u → Type v) [Comonad w] [Coseq w] (σ : Type u) :
    Coseq (StoreT σ w) := inferInstance

example (w : Type u → Type u) [Comonad w] [LawfulComonad w]
    {α : Type u} (x : w α) :
    extract (duplicate x) = x ∧
      Functor.map extract (duplicate x) = x ∧
      duplicate (duplicate x) = Functor.map duplicate (duplicate x) :=
  ⟨extract_duplicate_eq_id x, map_extract_duplicate_eq_id x,
    duplicate_duplicate_eq_map_duplicate x⟩

/-- Stream pairing observes both streams at the same index. -/
example {α β : Type u} (xs : Stream' α) (ys : Stream' β) (n : Nat) :
    Stream'.get (xs <@> ys) n = (Stream'.get xs n, Stream'.get ys n) := rfl

/-- The independent hierarchy paths share exactly the same mapping operation. -/
example {α β : Type u} (f : α → β) (xs : Stream' α) :
    @Functor.map Stream' (Comonad.toFunctor (w := Stream')) α β f xs =
      @Functor.map Stream' (Coapplicative.toFunctor (w := Stream')) α β f xs := rfl

example {P : PFunctor.{u, u}} {α β : Type u} (f : α → β) (x : PFunctor.CofreeC P α) :
    @Functor.map (PFunctor.CofreeC P) (Comonad.toFunctor) α β f x =
      @Functor.map (PFunctor.CofreeC P) (Coapplicative.toFunctor) α β f x := rfl

namespace ComonadExamples

/-- Retaining the right root is a lawful alternative to pointwise stream pairing. -/
@[instance_reducible]
def rootPairing : Coapplicative Stream' where
  toFunctor := inferInstance
  toExtract := inferInstance
  coseq xs ys := fun n => (xs n, ys 0)
  coseqLeft xs _ := xs
  coseqRight _ ys := fun _ => ys 0

section RootPairing

local instance : Coapplicative Stream' := rootPairing

example : LawfulCoapplicative Stream' where
  coseqLeft_eq := by intros; rfl
  coseqRight_eq := by intros; rfl
  coseq_assoc := by intros; rfl
  map_coseq := by intros; rfl

end RootPairing

/-- The two lawful policies disagree away from the root. -/
example : Stream'.get ((fun n => n) <@> (fun n => n)) 1 ≠
    Stream'.get (rootPairing.coseq (fun n => n) (fun n => n)) 1 := by
  decide

/-- Cofree pairing keeps the left shape and pairs its labels with the right root. -/
example {P : PFunctor.{u, u}} {α β : Type u}
    (xs : PFunctor.CofreeC P α) (ys : PFunctor.CofreeC P β) :
    PFunctor.CofreeC.head (xs <@> ys) =
      (PFunctor.CofreeC.head xs, PFunctor.CofreeC.head ys) := by
  change PFunctor.CofreeC.head (PFunctor.CofreeC.extend xs _) = _
  rw [PFunctor.CofreeC.head_extend]
  rfl

example {P : PFunctor.{u, u}} {α β : Type u}
    (xs : PFunctor.CofreeC P α) (ys : PFunctor.CofreeC P β) :
    PFunctor.CofreeC.tail (xs <@> ys) =
      P.map (fun child => child <@> ys) (PFunctor.CofreeC.tail xs) := by
  exact PFunctor.CofreeC.tail_extend xs _

/-- Both transformer hierarchy paths preserve the base mapping and extraction. -/
example (ε : Type u) :
    (Comonad.toFunctor (w := EnvT ε Stream')) = Coapplicative.toFunctor ∧
      (Comonad.toExtract (w := EnvT ε Stream')) = Coapplicative.toExtract := ⟨rfl, rfl⟩

example (σ : Type u) :
    (Comonad.toFunctor (w := StoreT σ Stream')) = Coapplicative.toFunctor ∧
      (Comonad.toExtract (w := StoreT σ Stream')) = Coapplicative.toExtract := ⟨rfl, rfl⟩

end ComonadExamples
