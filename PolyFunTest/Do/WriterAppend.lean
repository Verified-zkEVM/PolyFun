/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.WriterT.WP

/-!
# Append-based writer interpretation

A list log uses Mathlib's empty/append writer operations. The explicit interpretation
preserves a nonempty incoming log and its output order without installing a monoid
on lists or changing the writer's monad instance.
-/

public section

namespace PolyFunTest.Do.WriterAppend

open Std.Internal.Do

local instance : LawfulMonad (WriterT (List Nat) Id) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by
    apply WriterT.ext
    simp [WriterT.run_map, WriterT.run_bind, WriterT.run_pure])
  (id_map := fun _ => by apply WriterT.ext; simp [WriterT.run_map])
  (pure_bind := fun _ _ => by apply WriterT.ext; simp [WriterT.run_bind, WriterT.run_pure])
  (bind_assoc := fun _ _ _ => by apply WriterT.ext; simp [WriterT.run_bind, List.append_assoc])

local instance : WPMonad (WriterT (List Nat) Id) (List Nat → Prop) EPost.Nil :=
  WriterT.wpMonadOf [] (· ++ ·) List.append_nil List.append_assoc

/-- Record two values around a lifted computation. -/
def logPair (a b : Nat) : WriterT (List Nat) Id Nat := do
  tell [a]
  let result ← (pure (a + b) : Id Nat)
  tell [b]
  pure result

example (a b : Nat) :
    ⦃ fun log => log = [99] ⦄ logPair a b
      ⦃ fun result log => result = a + b ∧ log = [99, a, b] ⦄ := by
  apply Triple.intro
  intro log hlog
  subst log
  exact ⟨rfl, rfl⟩

example (a b : Nat) :
    (logPair a b).run = (a + b, [a, b]) := rfl

example (out : List Nat) (post : PUnit.{1} → List Nat → Prop) (epost : EPost.Nil) :
    Triple (tell out : WriterT (List Nat) Id PUnit)
      (fun log => post ⟨⟩ (log ++ out)) post epost :=
  Triple.intro (WriterT.le_wp_tell_of (· ++ ·) out post epost)

end PolyFunTest.Do.WriterAppend
