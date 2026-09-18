/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cursor.Fork
import PolyFun.PFunctor.Free.Path.Bounded
import PolyFun.PFunctor.Free.WP
import PolyFun.PFunctor.Display.Free
public import PolyFun.Interaction.Basic.TypeTree

/-!
# Dependent free-program consumers without transparency overrides

Paths use both constructor and monadic node spellings. Explicitly aligning an
index before rewriting tests the public equations under the default module
boundary. The replay examples extract structural consumers from VCVio's
`CryptoFoundations/ReplayFork` without choosing probability semantics.
-/

@[expose] public section

universe uA uB v w z uC uD uF

namespace PolyFunTest.ModuleAPI.DependentPaths

open PFunctor

example {P : PFunctor.{uA, uB}} {α : Type v} (a : P.A)
    (next : P.B a → FreeM P α) (path : FreeM.Path (FreeM.liftBind a next)) :
    FreeM.Path.cons a next (FreeM.Path.head a next path)
        (FreeM.Path.tail a next path) = path :=
  FreeM.Path.cons_head_tail a next path

example {P : PFunctor.{uA, uB}} {α : Type v} (a : P.A)
    (next : P.B a → FreeM P α) (path : FreeM.Path (FreeM.liftBind a next)) :
    FreeM.Path.cons a next (FreeM.Path.head a next path)
        (FreeM.Path.tail a next path) = path := by
  change FreeM.Path ((FreeM.lift a).bind next) at path
  rw [FreeM.Path.cons_head_tail]

example {P : PFunctor.{uA, uB}} {α : Type v} (a : P.A)
    (next : P.B a → FreeM P α) (path : FreeM.Path ((FreeM.lift a).bind next)) :
    FreeM.Path.cons a next (FreeM.Path.head a next path)
        (FreeM.Path.tail a next path) = path := by
  simp only [FreeM.Path.cons_head_tail]

/-- Index alignment also works for an arbitrary family, independently of the Path API. -/
example {P : PFunctor.{uA, uB}} {α : Type v}
    (F : FreeM P α → Type w) (a : P.A) (next : P.B a → FreeM P α)
    (observe : F ((FreeM.lift a).bind next) → Nat)
    (value : F (FreeM.liftBind a next)) (h : ∀ x, observe x = 0) :
    observe value = 0 := by
  change F ((FreeM.lift a).bind next) at value
  rw [h]

example {P : PFunctor.{uA, uB}} {α : Type v} {β : Type w}
    (first : FreeM P α) (next : FreeM.Path first → FreeM P β)
    (prefixPath : FreeM.Path first) (suffix : FreeM.Path (next prefixPath)) :
    FreeM.Path.split first next (FreeM.Path.append first next prefixPath suffix) =
      ⟨prefixPath, suffix⟩ := by
  rw [FreeM.Path.split_append]

example {P : PFunctor.{uA, uB}} {α : Type v} {β : Type w}
    (first : FreeM P α) (next : FreeM.Path first → FreeM P β)
    (path : FreeM.Path (FreeM.append first next)) :
    FreeM.Path.append first next (FreeM.Path.split first next path).1
      (FreeM.Path.split first next path).2 = path := by
  rw [FreeM.Path.append_split]

example {P : PFunctor.{uA, uB}} {α : Type v}
    (S : Display.{uA, uB, uC, uD} P) (F : α → Type uF)
    (program : FreeM P α) (data : FreeM.Displayed (S.toDisplayedAlgebra F) program) :
    S.transport F (FreeM.bind_pure program)
      (S.bind program data FreeM.pure (fun x dx => S.leaf F x dx)) = data :=
  S.bind_leaf program data

/-- Replay logging followed by erasing the path recovers the original program. -/
example {P : PFunctor.{uA, uB}} {α : Type v} (program : FreeM P α) :
    FreeM.map (FreeM.output program) (FreeM.withPath program) = program :=
  FreeM.map_output_withPath program

/-- The dynamic replay interface keeps selector and observer universes independent. -/
def replayOutputs {P : PFunctor.{uA, uB}} [DecidableEq P.A] {α : Type v}
    {κ : Type w} {β : Type z} (target : P.A) (program : FreeM P α)
    (select : α → Option κ) (ordinal : κ → Nat)
    (observe : (k : κ) → FreeM.Cursor.ForkView target program (ordinal k) → β) :
    FreeM P (Option β) :=
  FreeM.Cursor.locateAndForkBy target program select ordinal observe

example {P : PFunctor.{uA, uB}} [DecidableEq P.A] {α : Type v}
    (target : P.A) (program : FreeM P α) (path : FreeM.Path program) (n : Nat) :
    (FreeM.Cursor.locateAt? target program path n).isSome ↔
      n < TraceList.occurrences target (FreeM.Path.trace program path) := by
  rw [FreeM.Cursor.locateAt?_isSome_iff_lt_occurrences]

example {P : PFunctor.{uA, uB}} (a : P.A) (post : P.B a → Prop) :
    FreeM.wpFold (OpSpec.demonic P) (FreeM.lift a) post = ∀ b, post b := by
  rw [FreeM.wpFold_lift]
  rfl

/-- Public TypeTree constructors remain usable as patterns. -/
def rootIsDone : Interaction.TypeTree.{v} → Bool
  | .done => true
  | .node _ _ => false

example : rootIsDone Interaction.TypeTree.done = true := rfl

example (X : Type v) (next : X → Interaction.TypeTree.{v}) :
    rootIsDone (Interaction.TypeTree.node X next) = false := rfl

example (X : Type v) (next : X → Interaction.TypeTree.{v}) :
    Interaction.TypeTree.node X next = FreeM.liftBind X next := rfl

end PolyFunTest.ModuleAPI.DependentPaths
