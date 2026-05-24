/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Notation
public import PolyFun.IPFunctor.Notation.Indexed
public import PolyFun.IPFunctor.Notation.Deterministic

/-!
# Cross-flavor `do`-notation sanity tests

When all three notation files are imported together, three `@[doElem_elab]`
overrides are registered for both `doLetArrow` and `doExpr`. Lean tries
them in *most-recently-registered first* order; each override checks the
expected monad type and throws `unsupportedSyntax` when it doesn't match,
which falls through to the next override (and finally to the builtin).

This file holds tests that exercise every flavor in the same compilation
unit, so any silent drift in the override priority — e.g. an import
reordering that puts `IPFunctor.FreeM₂`'s override behind
`IPFunctor.FreeM`'s — would surface as a type-checking failure here
rather than at downstream call sites.
-/

@[expose] public section

set_option backward.do.legacy false

namespace IPFunctorMixedNotationTests

/-- Shared demo `IPFunctor.Endo` over `Bool`, identical to the per-file
fixtures so the tests below stay self-contained. -/
@[expose] def demoP : IPFunctor.Endo Bool where
  A
    | false => Unit
    | true  => Unit
  B
    | false, _ => Unit
    | true,  _ => Nat
  src
    | false, _, _ => true
    | true,  _, _ => true

@[expose] instance : IPFunctor.DeterministicTransitions demoP where
  next _ _ := true
  spec s a b := by cases s <;> rfl

@[reducible, expose] def flip : IPFunctor.FreeM demoP false Unit :=
  IPFunctor.FreeM.liftA false ()

@[reducible, expose] def read : IPFunctor.FreeM demoP true Nat :=
  IPFunctor.FreeM.liftA true ()

@[expose] def flip₂ : IPFunctor.FreeM₂ demoP false true Unit :=
  IPFunctor.FreeM₂.roll () (fun _ => IPFunctor.FreeM₂.pure ())

@[expose] def read₂ : IPFunctor.FreeM₂ demoP true true Nat :=
  IPFunctor.FreeM₂.roll () (fun n => IPFunctor.FreeM₂.pure n)

/-! ### Single-index `IPFunctor.FreeM` with the polymorphic-tail restriction. -/

-- The basic `FreeM`-notation elaborator handles this: terminal `pure ()`
-- is polymorphic in the post-state.
example : IPFunctor.FreeM demoP false Unit := do
  let _ ← flip
  pure ()

/-! ### Single-index `IPFunctor.FreeM` with a `DeterministicTransitions` instance.

A chain that would *fail* under the basic elaborator (because `read`'s
pre-state is the concrete `true`, not polymorphic) succeeds here because
the deterministic-override fires first and specializes the post-state
to `next s a = true`. -/

example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  let n ← read
  pure n

example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  let a ← read
  let b ← read
  pure (a + b)

/-! ### `IPFunctor.FreeM₂` — handled by the indexed-notation elaborator. -/

example : IPFunctor.FreeM₂ demoP false true Nat := do
  let _ ← flip₂
  let n ← read₂
  let m ← read₂
  pure (n + m)

/-! ### Non-`IPFunctor.FreeM` monads — none of our elaborators claim them. -/

example : Id Nat := do
  let x := 1
  pure (x + 1)

example : Option Nat := do
  let x ← some 5
  pure (x + 1)

example : List Nat := do
  let x ← [1, 2, 3]
  pure (x + 1)

end IPFunctorMixedNotationTests
