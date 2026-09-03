/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Std.Tactic.Do
public import Std.Internal.Do

/-!
# Additional Specifications and Normal Forms for `vcgen`

Core's `Std.Internal.Do.Triple.SpecLemmas` covers `forIn'` / `forIn` / `foldlM` over lists,
ranges, arrays, and iterators; this file adds the `@[spec]` rule for `List.forM`, the one list
loop that core does not specify, and registers core's own `Spec.tryCatch_MonadExcept` — the
lifting rule `try … catch` elaborates to (`MonadExcept.tryCatch`, not `MonadExceptOf.tryCatch`)
— which core states but does not tag, so that a `try … catch` block on a transformer stack no
longer stops `vcgen` with "no spec found". The wrappers the `do` elaborator uses to tunnel
`return`, `break`, and `continue` through non-algebraic combinators (`EarlyReturn.runK`,
`Break.runK`, `Continue.runK`) need no rules here: they are `abbrev`s, and both `simp` and
`grind` reduce them on a constructor scrutinee unaided.

The specification lives in the namespace it will have upstream, next to core's `Spec.forIn_list`
in `SpecLemmas.lean`; the v4.35 rename of `Std.Internal.Do` to `Std.WP` moves it in lockstep.
This module imports `Std.Tactic.Do` for the `@[spec]` attribute syntax and is therefore part of
the tactic tier of the `Std.Do` quarantine.
-/

@[expose] public section

universe u v w z

open Std.Internal.Do

-- upstream: lean4 `SpecLemmas.lean` tags `Spec.throw_MonadExcept` but not this twin.
attribute [spec] Std.Internal.Do.Spec.tryCatch_MonadExcept

namespace Std.Internal.Do

variable {α : Type w} {m : Type u → Type v} {Pred : Type z} {EPred : Type z}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

-- upstream candidate: `Std.Internal.Do.Triple.SpecLemmas` (`Std.WP` from Lean v4.35).
/-- Invariant rule for `forM` over a list: the invariant relates the elements consumed so far to
those remaining (its accumulator is `PUnit`, so `vcgen`'s `invariants` clause applies to it), and
each body step advances it by one element. Stated on the class method `forM`, the simp normal
form of `List.forM`. -/
@[spec]
theorem Spec.forM_list {xs : List α} {f : α → m PUnit} (inv : Invariant α PUnit.{u + 1} Pred)
    {epost : EPred}
    (step : ∀ pref cur suff, xs = pref ++ cur :: suff →
      Triple (f cur) (inv pref (cur :: suff) ⟨⟩) (fun _ => inv (pref ++ [cur]) suff ⟨⟩) epost) :
    Triple (forM xs f) (inv [] xs ⟨⟩) (fun _ => inv xs [] ⟨⟩) epost := by
  suffices h : ∀ pref suff, xs = pref ++ suff →
      Triple (forM suff f) (inv pref suff ⟨⟩) (fun _ => inv xs [] ⟨⟩) epost from h [] xs rfl
  intro pref suff
  induction suff generalizing pref with
  | nil =>
    intro hxs
    simp only [List.forM_nil]
    refine Triple.pure _ ?_
    simp only [List.append_nil] at hxs
    subst hxs
    exact Lean.Order.PartialOrder.rel_refl
  | cons x suff ih =>
    intro hxs
    simp only [List.forM_cons]
    exact Triple.bind (f x) (fun _ => forM suff f) (fun _ => inv (pref ++ [x]) suff ⟨⟩)
      (step pref x suff hxs) (fun _ => ih (pref ++ [x]) (by simp [hxs]))

end Std.Internal.Do
