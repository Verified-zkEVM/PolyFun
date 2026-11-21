/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Scoped

/-!
# Admissibility under a binder

Represent natural numbers by the basepoint zero. A local assignment binds the second input.
The body applies a binary operation to the first input and the fresh variable. Addition and
subtraction give different results on the same term and both preserve the basepoint.
-/

public section

namespace PolyFunTest.Realizability.Scoped

open IPFunctor IPFunctor.ScopedSignature

/-- Admissible maps take the designated source point to the designated target point. -/
abbrev pointed : PFunctor.StepClass.{0, 0} where
  Str A := A
  Hom a b f := f a = b
  id_mem _ := rfl
  comp_mem h₁ h₂ := by simpa [Function.comp_apply, h₁] using h₂

local instance : pointed.HasProd where
  prod a b := (a, b)
  fst_mem _ _ := rfl
  snd_mem _ _ := rfl
  pair_mem hx hy := Prod.ext hx hy

/-- Local assignment and a binary arithmetic operation. -/
inductive Op where
  | letE
  | binary

/-- Only the body of the local assignment enters a new scope. -/
abbrev sig : ScopedSignature Unit where
  Op _ := Op
  Arg _ := Bool
  binders
    | .letE, true => [()]
    | _, _ => []
  sort _ _ := ()

/-- The choice of binary operation changes how the same syntax evaluates. -/
@[expose] def algebra (combine : Nat → Nat → Nat) : Interpretation sig (fun _ => Nat)
  | _, .letE, args => args true (Env.single (args false Env.empty))
  | _, .binary, args => combine (args false Env.empty) (args true Env.empty)

private theorem preserves {combine : Nat → Nat → Nat} (h : combine 0 0 = 0) :
    Interpretation.PreservesAdmissible (σ := sig) (algebra combine) pointed (fun _ => 0) := by
  intro ι base s op args hargs
  cases op with
  | letE =>
    apply hargs true (fun i => Env.single (args false i Env.empty))
    intro a x
    cases x with
    | zero => exact hargs false (fun _ => Env.empty) (fun x => nomatch x)
    | succ x => nomatch x
  | binary =>
    change combine (args false base Env.empty) (args true base Env.empty) = 0
    have hf : args false base Env.empty = 0 := hargs false (fun _ => Env.empty) (fun x => nomatch x)
    have ht : args true base Env.empty = 0 := hargs true (fun _ => Env.empty) (fun x => nomatch x)
    rw [hf, ht, h]

/-- Bind the second input, then use the first input and the freshly bound value in order. -/
@[expose] def term : sig.Term [(), ()] () :=
  Term.node Op.letE fun
    | false => .var (.succ .zero)
    | true => .node Op.binary fun
      | false => .var (.succ .zero)
      | true => .var .zero

example : term.denote (algebra Nat.sub) (Binary.pairEnv (9, 4)) = 5 := rfl
example : term.denote (algebra Nat.add) (Binary.pairEnv (9, 4)) = 13 := rfl

example (combine : Nat → Nat → Nat) (h : combine 0 0 = 0) :
    pointed.Hom (0, 0) 0 (fun p => term.denote (algebra combine) (Binary.pairEnv p)) :=
  term.denote_admissible (preserves h) (Binary.pairEnv_admissible (C := pointed))

/-- Use the second variable once at each level of a nested operation. -/
private def nested : (Binary.signature Unit).Term [(), ()] () :=
  Binary.app () Binary.snd (Binary.app () Binary.fst Binary.snd)

example : nested.denote (Binary.algebra (fun _ => Nat.sub)) (Binary.pairEnv (7, 5)) = 3 := rfl

example (combine : Nat → Nat → Nat) (p : Nat × Nat) :
    nested.denote (Binary.algebra (fun _ => combine)) (Binary.pairEnv p) =
      combine p.2 (combine p.1 p.2) := by
  simp only [nested, Binary.denote_app, Binary.denote_fst, Binary.denote_snd]

example (combine : Nat → Nat → Nat) (h : combine 0 0 = 0) :
    pointed.Hom (0, 0) 0 (fun p => combine p.2 (combine p.1 p.2)) :=
  Binary.denote_admissible (C := pointed) (repr := 0) (applyOp := fun _ : Unit => combine)
    (fun _ => h) nested

end PolyFunTest.Realizability.Scoped
