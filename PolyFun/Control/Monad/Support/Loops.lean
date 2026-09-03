/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support.WP

/-!
# Loop Rules for Exact Support

`for` loops elaborate to `forIn` / `forIn'` over the iterated container, and `forM` / `foldlM`
are their common special cases. Under the demonic interpretation `wp x post = AllOutputs post x`
(`MonadAttach.toWPMonadDemonic`), core's list-loop specifications `Spec.forIn'_list`,
`Spec.forIn_list`, and `Spec.foldlM_list` *are* invariant rules for the "always" judgment, and
the angelic interpretation gives their "sometimes" twins; this file states them in that form so
that support reasoning about loops needs no `vcgen` and no `Triple`. Containers whose loop is
the loop over the list `ForIn.toList` computes (`Std.Internal.PureForIn`: lists, arrays,
ranges, slices, iterators, and `Option` / `Vector` via `ToCslib.Control.ForIn`) reduce to the
list rules. `forM` has no core specification and is proved by induction.

Invariants follow core's shape: a predicate on the elements consumed so far, the elements
remaining, and the accumulator. The rules are directed reasoning steps, not equations, and are
therefore untagged.
-/

@[expose] public section

universe u v w w'

open Std.Internal.Do

namespace MonadAttach

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
  {ι : Type w} {β : Type u}

/-! ## Lists -/

theorem allOutputs_forIn'_list_of_inv {xs : List ι} {init : β}
    {f : (a : ι) → a ∈ xs → β → m (ForInStep β)} (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b, inv pref (cur :: suff) b →
      AllOutputs (fun r => match r with
        | .yield b' => inv (pref ++ [cur]) suff b'
        | .done b' => inv xs [] b') (f cur (by simp [h]) b))
    (hinit : inv [] xs init) : AllOutputs (inv xs []) (forIn' xs init f) := by
  let inst := toWPMonadDemonic (m := m)
  exact (Spec.forIn'_list (m := m) inv (epost := Lean.Order.bot)
    fun pref cur suff h b => ⟨fun hpre => step pref cur suff h b hpre⟩).le_wp hinit

theorem allOutputs_forIn_list_of_inv {xs : List ι} {init : β} {f : ι → β → m (ForInStep β)}
    (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff, xs = pref ++ cur :: suff → ∀ b, inv pref (cur :: suff) b →
      AllOutputs (fun r => match r with
        | .yield b' => inv (pref ++ [cur]) suff b'
        | .done b' => inv xs [] b') (f cur b))
    (hinit : inv [] xs init) : AllOutputs (inv xs []) (forIn xs init f) := by
  let inst := toWPMonadDemonic (m := m)
  exact (Spec.forIn_list (m := m) inv (epost := Lean.Order.bot)
    fun pref cur suff h b => ⟨fun hpre => step pref cur suff h b hpre⟩).le_wp hinit

/-- `allOutputs_forIn_list_of_inv` with an invariant on the accumulator alone. -/
theorem allOutputs_forIn_list_of_const_inv {xs : List ι} {init : β} {f : ι → β → m (ForInStep β)}
    (inv : β → Prop)
    (step : ∀ cur ∈ xs, ∀ b, inv b →
      AllOutputs (fun r => match r with | .yield b' => inv b' | .done b' => inv b') (f cur b))
    (hinit : inv init) : AllOutputs inv (forIn xs init f) :=
  allOutputs_forIn_list_of_inv (fun _ _ b => inv b)
    (fun _ cur _ h b hb =>
      step cur (by rw [h]; exact List.mem_append_right _ (List.Mem.head _)) b hb)
    hinit

theorem allOutputs_foldlM_list_of_inv {xs : List ι} {init : β} {f : β → ι → m β}
    (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff, xs = pref ++ cur :: suff → ∀ b, inv pref (cur :: suff) b →
      AllOutputs (fun b' => inv (pref ++ [cur]) suff b') (f b cur))
    (hinit : inv [] xs init) : AllOutputs (inv xs []) (xs.foldlM f init) := by
  let inst := toWPMonadDemonic (m := m)
  exact (Spec.foldlM_list (m := m) inv (epost := Lean.Order.bot)
    fun pref cur suff h b => ⟨fun hpre => step pref cur suff h b hpre⟩).le_wp hinit

theorem allOutputs_forM_list_of_inv {xs : List ι} {f : ι → m PUnit}
    (inv : List ι → List ι → Prop)
    (step : ∀ pref cur suff, xs = pref ++ cur :: suff → inv pref (cur :: suff) →
      AllOutputs (fun _ => inv (pref ++ [cur]) suff) (f cur))
    (hinit : inv [] xs) : AllOutputs (fun _ => inv xs []) (xs.forM f) := by
  suffices h : ∀ pref suff, xs = pref ++ suff → inv pref suff →
      AllOutputs (fun _ => inv xs []) (suff.forM f) from h [] xs rfl hinit
  intro pref suff
  induction suff generalizing pref with
  | nil =>
    intro hxs hinv
    simp only [List.forM_eq_forM, List.forM_nil, allOutputs_pure]
    simpa [hxs] using hinv
  | cons x suff ih =>
    intro hxs hinv
    simp only [List.forM_eq_forM, List.forM_cons, allOutputs_bind]
    intro u hu
    exact ih (pref ++ [x]) (by simp [hxs]) (step pref x suff hxs hinv u hu)

/-! ## Angelic twins -/

theorem someOutput_forIn'_list_of_inv {xs : List ι} {init : β}
    {f : (a : ι) → a ∈ xs → β → m (ForInStep β)} (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b, inv pref (cur :: suff) b →
      SomeOutput (fun r => match r with
        | .yield b' => inv (pref ++ [cur]) suff b'
        | .done b' => inv xs [] b') (f cur (by simp [h]) b))
    (hinit : inv [] xs init) : SomeOutput (inv xs []) (forIn' xs init f) := by
  let inst := toWPMonadAngelic (m := m)
  exact (Spec.forIn'_list (m := m) inv (epost := Lean.Order.bot)
    fun pref cur suff h b => ⟨fun hpre => step pref cur suff h b hpre⟩).le_wp hinit

theorem someOutput_forIn_list_of_inv {xs : List ι} {init : β} {f : ι → β → m (ForInStep β)}
    (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff, xs = pref ++ cur :: suff → ∀ b, inv pref (cur :: suff) b →
      SomeOutput (fun r => match r with
        | .yield b' => inv (pref ++ [cur]) suff b'
        | .done b' => inv xs [] b') (f cur b))
    (hinit : inv [] xs init) : SomeOutput (inv xs []) (forIn xs init f) := by
  let inst := toWPMonadAngelic (m := m)
  exact (Spec.forIn_list (m := m) inv (epost := Lean.Order.bot)
    fun pref cur suff h b => ⟨fun hpre => step pref cur suff h b hpre⟩).le_wp hinit

/-! ## Containers iterating over a list -/

theorem allOutputs_forIn_of_pureForIn {ρ : Type w'} [ForIn m ρ ι] [ForIn Id ρ ι]
    [Std.Internal.PureForIn m ρ ι] (xs : ρ) {init : β} {f : ι → β → m (ForInStep β)}
    (inv : List ι → List ι → β → Prop)
    (step : ∀ pref cur suff, ForIn.toList xs = pref ++ cur :: suff → ∀ b,
      inv pref (cur :: suff) b →
      AllOutputs (fun r => match r with
        | .yield b' => inv (pref ++ [cur]) suff b'
        | .done b' => inv (ForIn.toList xs) [] b') (f cur b))
    (hinit : inv [] (ForIn.toList xs) init) :
    AllOutputs (inv (ForIn.toList xs) []) (forIn xs init f) := by
  rw [Std.Internal.PureForIn.forIn_eq]
  exact allOutputs_forIn_list_of_inv inv step hinit

end MonadAttach
