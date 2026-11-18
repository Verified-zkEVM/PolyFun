/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support.Loops
public import PolyFun.Control.Monad.Support.Instances
public import ToCslib.Control.Loop.Basic

/-!
# Invariant rules for loops in `Id`

`Id.run do` code elaborates its `for` loops to `forIn` in `Id`, and the only possible output of an
`Id` computation is its value (`MonadAttach.Id.canReturn_iff`). The support loop rules of
`PolyFun.Control.Monad.Support.Loops`, which are core's `Std.WP.Spec.forIn_list` and
`Std.WP.Spec.forIn_pure` read through the demonic interpretation, therefore specialize to
invariant rules about the value `Id.run (forIn xs init f)`. This module states them in that form.

Invariants follow core's shape: a predicate on the elements consumed so far, the elements
remaining, and the loop state. A step obligation reads the step's result: a `.yield b'` must
re-establish the invariant one element further on, and a `.done b'` must establish it for the
whole list, which is how an early exit is handled.

* `Id.run_forIn_list_of_inv`, `Id.run_forIn'_list_of_inv` and `Id.run_forIn_of_pureForIn` are the
  invariant rules for lists and for every `Std.Internal.PureForIn` container.
* `Id.run_forIn_list_eq_foldl_of_inv` and `Id.run_forIn_eq_foldl_of_pureForIn_of_inv` identify the
  loop with a left fold when the body only yields as long as an invariant holds, as a decoder does
  on valid input.
* `Id.run_forIn_list_earlyReturn_of_inv` and `Id.run_forIn_earlyReturn_of_pureForIn` handle
  `return` inside a loop.
* `Id.run_bind_forIn_of_pureForIn` and `Id.run_bind_forIn_earlyReturn_of_pureForIn` conclude a
  postcondition of a loop followed by the rest of its `do` block, so that a proof applies them to
  the elaborated definition and never restates the loop body. Core's `do` elaborator
  threads an `Option ρ × σ` state through such a loop: the first component becomes `some r` when
  the body returns `r` early, and the loop then stops. The rule takes an invariant for the
  iterations that continue and a postcondition for a value returned early, the `Prop` reading of
  core's `Std.WP.Invariant.withEarlyReturnNewDo`.
-/

@[expose] public section

universe u w w'

namespace Id

variable {ι : Type w} {β : Type u}

/-! ## Invariant rules -/

theorem run_forIn_list_of_inv {xs : List ι} {init : β} {f : ι → β → Id (ForInStep β)}
    (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff, xs = pref ++ cur :: suff → ∀ b, inv pref (cur :: suff) b →
      match (f cur b).run with
      | .yield b' => inv (pref ++ [cur]) suff b'
      | .done b' => inv xs [] b')
    (hinit : inv [] xs init) : inv xs [] (forIn xs init f).run :=
  MonadAttach.allOutputs_forIn_list_of_inv inv
    (fun pref cur suff h b hb _ hr =>
      (MonadAttach.Id.canReturn_iff.1 hr) ▸ step pref cur suff h b hb)
    hinit _ (MonadAttach.Id.canReturn_iff.2 rfl)

theorem run_forIn'_list_of_inv {xs : List ι} {init : β}
    {f : (a : ι) → a ∈ xs → β → Id (ForInStep β)} (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b, inv pref (cur :: suff) b →
      match (f cur (by simp [h]) b).run with
      | .yield b' => inv (pref ++ [cur]) suff b'
      | .done b' => inv xs [] b')
    (hinit : inv [] xs init) : inv xs [] (forIn' xs init f).run :=
  MonadAttach.allOutputs_forIn'_list_of_inv inv
    (fun pref cur suff h b hb _ hr =>
      (MonadAttach.Id.canReturn_iff.1 hr) ▸ step pref cur suff h b hb)
    hinit _ (MonadAttach.Id.canReturn_iff.2 rfl)

/-- `run_forIn_list_of_inv` with an invariant on the loop state alone. -/
theorem run_forIn_list_of_const_inv {xs : List ι} {init : β} {f : ι → β → Id (ForInStep β)}
    (inv : β → Prop) (step : ∀ cur ∈ xs, ∀ b, inv b → inv (f cur b).run.value)
    (hinit : inv init) : inv (forIn xs init f).run :=
  run_forIn_list_of_inv (fun _ _ b => inv b)
    (fun _ cur _ h b hb => by
      have := step cur (by rw [h]; exact List.mem_append_right _ List.mem_cons_self) b hb
      revert this
      cases (f cur b).run <;> exact id)
    hinit

theorem run_forIn_of_pureForIn {ρ : Type w'} [ForIn Id.{u} ρ ι] [ForIn Id.{w} ρ ι]
    [Std.Internal.PureForIn Id.{u} ρ ι] (xs : ρ) {init : β} {f : ι → β → Id (ForInStep β)}
    (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff, ForIn.toList xs = pref ++ cur :: suff → ∀ b,
      inv pref (cur :: suff) b →
      match (f cur b).run with
      | .yield b' => inv (pref ++ [cur]) suff b'
      | .done b' => inv (ForIn.toList xs) [] b')
    (hinit : inv [] (ForIn.toList xs) init) : inv (ForIn.toList xs) [] (forIn xs init f).run :=
  MonadAttach.allOutputs_forIn_of_pureForIn xs inv
    (fun pref cur suff h b hb _ hr =>
      (MonadAttach.Id.canReturn_iff.1 hr) ▸ step pref cur suff h b hb)
    hinit _ (MonadAttach.Id.canReturn_iff.2 rfl)

/-! ## Loops that only yield under an invariant -/

/-- A loop whose body, as long as `inv` holds, yields `g b cur` and re-establishes `inv`, is the
left fold of `g`. -/
theorem run_forIn_list_eq_foldl_of_inv {xs : List ι} {init : β} {f : ι → β → Id (ForInStep β)}
    (g : β → ι → β) (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff, xs = pref ++ cur :: suff → ∀ b, inv pref (cur :: suff) b →
      f cur b = pure (.yield (g b cur)) ∧ inv (pref ++ [cur]) suff (g b cur))
    (hinit : inv [] xs init) : (forIn xs init f).run = xs.foldl g init := by
  have := run_forIn_list_of_inv (f := f)
    (fun pref suff b => inv pref suff b ∧ b = pref.foldl g init)
    (fun pref cur suff h b ⟨hb, hbeq⟩ => by
      obtain ⟨hf, hinv⟩ := step pref cur suff h b hb
      rw [hf]
      exact ⟨hinv, by rw [List.foldl_append, ← hbeq]; rfl⟩)
    ⟨hinit, rfl⟩
  exact this.2

/-- `run_forIn_list_eq_foldl_of_inv` for every container whose loop is the loop over
`ForIn.toList`. -/
theorem run_forIn_eq_foldl_of_pureForIn_of_inv {ρ : Type w'} [ForIn Id.{u} ρ ι]
    [ForIn Id.{w} ρ ι] [Std.Internal.PureForIn Id.{u} ρ ι] (xs : ρ) {init : β}
    {f : ι → β → Id (ForInStep β)} (g : β → ι → β) (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff, ForIn.toList xs = pref ++ cur :: suff → ∀ b,
      inv pref (cur :: suff) b →
      f cur b = pure (.yield (g b cur)) ∧ inv (pref ++ [cur]) suff (g b cur))
    (hinit : inv [] (ForIn.toList xs) init) :
    (forIn xs init f).run = (ForIn.toList xs).foldl g init := by
  rw [Std.Internal.PureForIn.forIn_eq]
  exact run_forIn_list_eq_foldl_of_inv g inv step hinit

/-! ## Early return -/

/-- The invariant rule for a loop with `return` inside, over the `Option ρ × σ` state that core's
`do` elaborator threads through it. While the first component is `none`, `onContinue` holds of the
mutable variables `σ`. A step that returns `r` early, `.done (some r, b')`, must establish
`onReturn r b'`; a step that leaves the loop by `break`, `.done (none, b')`, must establish
`onContinue` for the whole list. The rule concludes `onContinue` of the final state when the loop
did not return early, and `onReturn` of the returned value when it did. -/
theorem run_forIn_list_earlyReturn_of_inv {ρ σ : Type u} {xs : List ι} {init : σ}
    {f : ι → Option ρ × σ → Id (ForInStep (Option ρ × σ))}
    (onContinue : List ι → List ι → σ → Prop) (onReturn : ρ → σ → Prop)
    (step : ∀ pref cur suff, xs = pref ++ cur :: suff → ∀ b, onContinue pref (cur :: suff) b →
      match (f cur (none, b)).run with
      | .yield (none, b') => onContinue (pref ++ [cur]) suff b'
      | .yield (some r, b') => suff = [] ∧ onReturn r b'
      | .done (none, b') => onContinue xs [] b'
      | .done (some r, b') => onReturn r b')
    (hinit : onContinue [] xs init) :
    match (forIn xs (none, init) f).run with
    | (none, b) => onContinue xs [] b
    | (some r, b) => onReturn r b := by
  have := run_forIn_list_of_inv (f := f) (init := (none, init))
    (fun pref suff s => match s with
      | (none, b) => onContinue pref suff b
      | (some r, b) => suff = [] ∧ onReturn r b)
    (fun pref cur suff h s hs => by
      obtain ⟨x, b⟩ := s
      cases x with
      | some r => exact absurd hs.1 (List.cons_ne_nil _ _)
      | none =>
        have hstep := step pref cur suff h b hs
        revert hstep
        cases (f cur (none, b)).run with
        | yield s' => obtain ⟨_ | r, b'⟩ := s' <;> exact id
        | done s' =>
          obtain ⟨_ | r, b'⟩ := s'
          · exact id
          · exact fun h => ⟨rfl, h⟩)
    hinit
  revert this
  rcases (forIn xs (none, init) f).run with ⟨_ | r, b⟩
  · exact id
  · exact fun h => h.2

/-- `run_forIn_list_earlyReturn_of_inv` for every container whose loop is the loop over
`ForIn.toList`. -/
theorem run_forIn_earlyReturn_of_pureForIn {ρ σ : Type u} {γ : Type w'} [ForIn Id.{u} γ ι]
    [ForIn Id.{w} γ ι] [Std.Internal.PureForIn Id.{u} γ ι] (xs : γ) {init : σ}
    {f : ι → Option ρ × σ → Id (ForInStep (Option ρ × σ))}
    (onContinue : List ι → List ι → σ → Prop) (onReturn : ρ → σ → Prop)
    (step : ∀ pref cur suff, ForIn.toList xs = pref ++ cur :: suff → ∀ b,
      onContinue pref (cur :: suff) b →
      match (f cur (none, b)).run with
      | .yield (none, b') => onContinue (pref ++ [cur]) suff b'
      | .yield (some r, b') => suff = [] ∧ onReturn r b'
      | .done (none, b') => onContinue (ForIn.toList xs) [] b'
      | .done (some r, b') => onReturn r b')
    (hinit : onContinue [] (ForIn.toList xs) init) :
    match (forIn xs (none, init) f).run with
    | (none, b) => onContinue (ForIn.toList xs) [] b
    | (some r, b) => onReturn r b := by
  rw [Std.Internal.PureForIn.forIn_eq]
  exact run_forIn_list_earlyReturn_of_inv onContinue onReturn step hinit

/-! ## A loop followed by the rest of the `do` block

`Id.run do` code continues after a loop with the loop's final state, and after a loop with
`return` inside with a `match` on the first component of that state. The rules below conclude a
postcondition of the whole block from the loop's invariant and a fact about the continuation `k`,
so they apply to the elaborated block without restating the loop body. -/

/-- A postcondition of a loop followed by a continuation `k`, from a loop invariant whose final
form makes `k` establish the postcondition. -/
theorem run_bind_forIn_of_pureForIn {τ : Type u} {γ : Type w'} [ForIn Id.{u} γ ι]
    [ForIn Id.{w} γ ι] [Std.Internal.PureForIn Id.{u} γ ι] (xs : γ) {init : β}
    {f : ι → β → Id (ForInStep β)} {k : β → Id τ} (P : τ → Prop)
    (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff, ForIn.toList xs = pref ++ cur :: suff → ∀ b,
      inv pref (cur :: suff) b →
      match (f cur b).run with
      | .yield b' => inv (pref ++ [cur]) suff b'
      | .done b' => inv (ForIn.toList xs) [] b')
    (hinit : inv [] (ForIn.toList xs) init)
    (hk : ∀ b, inv (ForIn.toList xs) [] b → P (k b).run) :
    P (forIn xs init f >>= k).run :=
  hk _ (run_forIn_of_pureForIn xs inv step hinit)

/-- A postcondition of a loop with `return` inside followed by a continuation `k`: a value `r`
returned early reaches `k (some r, b)`, and a loop that runs to the end or leaves by `break`
reaches `k (none, b)`. Core's `do` elaborator makes `k (some r, b)` return `r`. -/
theorem run_bind_forIn_earlyReturn_of_pureForIn {ρ σ τ : Type u} {γ : Type w'}
    [ForIn Id.{u} γ ι] [ForIn Id.{w} γ ι] [Std.Internal.PureForIn Id.{u} γ ι] (xs : γ)
    {init : σ} {f : ι → Option ρ × σ → Id (ForInStep (Option ρ × σ))} {k : Option ρ × σ → Id τ}
    (P : τ → Prop) (onContinue : List ι → List ι → σ → Prop) (onReturn : ρ → σ → Prop)
    (step : ∀ pref cur suff, ForIn.toList xs = pref ++ cur :: suff → ∀ b,
      onContinue pref (cur :: suff) b →
      match (f cur (none, b)).run with
      | .yield (none, b') => onContinue (pref ++ [cur]) suff b'
      | .yield (some r, b') => suff = [] ∧ onReturn r b'
      | .done (none, b') => onContinue (ForIn.toList xs) [] b'
      | .done (some r, b') => onReturn r b')
    (hinit : onContinue [] (ForIn.toList xs) init)
    (hreturn : ∀ r b, onReturn r b → P (k (some r, b)).run)
    (hcontinue : ∀ b, onContinue (ForIn.toList xs) [] b → P (k (none, b)).run) :
    P (forIn xs (none, init) f >>= k).run := by
  have h := run_forIn_earlyReturn_of_pureForIn xs onContinue onReturn step hinit
  change P (k (forIn xs (none, init) f).run).run
  revert h
  rcases (forIn xs (none, init) f).run with ⟨_ | r, b⟩
  · exact hcontinue b
  · exact hreturn r b

end Id
