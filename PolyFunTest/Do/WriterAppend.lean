/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Do.Spec

/-!
# Append-based writer interpretation

A list log uses Mathlib's empty/append writer operations. The explicit interpretation
preserves a nonempty incoming log and its output order without installing a monoid
on lists or changing the writer's monad instance. The scoped interpretation
`WriterT.AppendWP` installs the same reading from core's `Std.Associative (· ++ ·)` and
`Std.LawfulIdentity (· ++ ·) ∅`, and `vcgen` steps through `tell`, lifted base computations,
`WriterT.mk` and `run` with the rules of `PolyFun.Control.Do.Spec`.
-/

public section

namespace PolyFunTest.Do.WriterAppend

open Std.WP

local instance : LawfulMonad (WriterT (List Nat) Id) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by
    apply WriterT.ext
    simp [WriterT.run_map, WriterT.run_bind, WriterT.run_pure])
  (id_map := fun _ => by apply WriterT.ext; simp [WriterT.run_map])
  (pure_bind := fun _ _ => by apply WriterT.ext; simp [WriterT.run_bind, WriterT.run_pure])
  (bind_assoc := fun _ _ _ => by apply WriterT.ext; simp [WriterT.run_bind, List.append_assoc])

local instance : WPMonad (WriterT (List Nat) Id) (List Nat → Prop) EStack⟨⟩ :=
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

example (out : List Nat) (post : PUnit.{1} → List Nat → Prop) (epost : EStack⟨⟩) :
    Triple (tell out : WriterT (List Nat) Id PUnit)
      (fun log => post ⟨⟩ (log ++ out)) post epost :=
  Triple.intro (WriterT.le_wp_tell_of (· ++ ·) out post epost)

end PolyFunTest.Do.WriterAppend

namespace PolyFunTest.Do.WriterAppendWP

open Std.WP

set_option experimental.vcgen true

/- Importing the interpretation leaves it unselected. -/
example : True := by
  fail_if_success
    have := inferInstanceAs (WPMonad (WriterT (List Nat) Id) (List Nat → Prop) EStack⟨⟩)
  trivial

open scoped WriterT.AppendWP

/-- Record two values around a lifted computation. -/
def logPair (a b : Nat) : WriterT (List Nat) Id Nat := do
  tell [a]
  let result ← (pure (a + b) : Id Nat)
  tell [b]
  pure result

/- From a nonempty incoming log, `tell` extends the log on the right, in order. -/
example (a b : Nat) :
    ⦃ fun log => log = [99] ⦄ logPair a b
      ⦃ fun result log => result = a + b ∧ log = [99, a, b] ⦄ := by
  vcgen [logPair]
  simp_all

/- `run` starts from the empty log. -/
example (a b : Nat) : ⦃ True ⦄ (logPair a b).run ⦃ fun p => p = (a + b, [a, b]) ⦄ := by
  vcgen [logPair]
  simp_all

/- `WriterT.mk` appends the log its body returns. -/
example : ⦃ fun log => log = [1] ⦄ (WriterT.mk (pure (true, [2])) : WriterT (List Nat) Id Bool)
    ⦃ fun b log => b = true ∧ log = [1, 2] ⦄ := by
  vcgen
  simp_all

/- Over an exact base the interpretation is exact, so `wp` computes by `simp`. -/
example (a b : Nat) (log : List Nat) (epost : EStack⟨⟩) :
    wp (logPair a b) (fun r w => r = a + b ∧ w = log ++ [a, b]) epost log := by
  simp [logPair]

end PolyFunTest.Do.WriterAppendWP
