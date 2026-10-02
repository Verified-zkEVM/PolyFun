/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Std.Tactic.Do
public import Std.WP
public import PolyFun.Control.Monad.WriterT.WP

/-!
# Additional Specifications and Normal Forms for `vcgen`

Core's `Std.WP.Triple.SpecLemmas` covers `forIn'` / `forIn` / `foldlM` over lists,
ranges, arrays, and iterators, and the operations of core's own transformers; this file adds:

* the `@[spec]` rule for `List.forM`, the one list loop that core does not specify;
* the registration of core's own `Spec.tryCatch_MonadExcept` — the lifting rule `try … catch`
  elaborates to (`MonadExcept.tryCatch`, not `MonadExceptOf.tryCatch`) — which core states but
  does not tag, so that a `try … catch` block on a transformer stack no longer stops `vcgen`
  with "no spec found";
* the rules for `WriterT` (Mathlib's transformer, interpreted by
  `PolyFun.Control.Monad.WriterT.WP`): `tell`, `monadLift`, `mk`, and `run`;
* the `OptionT` rules core does not state: `failure` and `OptionT.lift` for every assertion
  carrier, and `guard` for `Prop`-valued readings, stated with lattice connectives so that
  `vcgen` splits it into its two outcomes, with `guard` for every assertion carrier below it;
* the transformers' constructors, lifts and runners that programs also write: `StateT.mk`,
  `StateT.lift`, running a `StateT` at a state with the state discarded, `OptionT.mk`,
  `ExceptT.mk`, `ExceptT.lift`, and running an `OptionT` or `ExceptT` into a postcondition of the
  option or the result, which outrank core's `Spec.run_OptionT` and `Spec.run_ExceptT`;
* `List.mapM` with a loop invariant over the elements consumed, the elements remaining and the
  outputs so far, and the sequence combinators `<*` and `*>`.

`StateT.run x s` is `x s` once `vcgen` has unfolded the reducible constants of its goal, so no
rule can be keyed on it; a `StateT` program run at a state is reasoned about as a triple of the
program itself, with state-passing assertions (`StateT.wp_apply_eq`).

The wrappers the `do` elaborator uses to tunnel `return`, `break`, and `continue` through
non-algebraic combinators (`EarlyReturn.runK`, `Break.runK`, `Continue.runK`) need no rules
here: they are `abbrev`s, and both `simp` and `grind` reduce them on a constructor scrutinee
unaided.

The core-shaped specifications live in the namespace they would have upstream, next to core's
`Spec.forIn_list` in `Std.WP.Triple.SpecLemmas`. This module imports `Std.Tactic.Do` for the
`@[spec]` attribute syntax and is therefore part of the tactic tier of the `Std.WP` quarantine.
-/

@[expose] public section

universe u v w w' z

open Std.WP

-- upstream: lean4 `SpecLemmas.lean` tags `Spec.throw_MonadExcept` but not this twin.
attribute [spec] Std.WP.Spec.tryCatch_MonadExcept

namespace Std.WP

variable {α : Type w} {m : Type u → Type v} {Pred : Type z} {EPred : Type z}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

-- upstream candidate: `Std.WP.Triple.SpecLemmas`.
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

/-! ## `WriterT` -/

section WriterTSpec

open scoped WriterT.MonoidWP

variable {ω : Type u} [Monoid ω] {Pred : Type z} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

@[spec]
theorem Spec.tell_WriterT (out : ω) (post : PUnit → ω → Pred) {epost : EPred} :
    Triple (MonadWriter.tell out : WriterT ω m PUnit) (fun w => post ⟨⟩ (w * out)) post epost :=
  Triple.intro (WriterT.le_wp_tell out post epost)

@[spec]
theorem Spec.monadLift_WriterT {α : Type u} (x : m α) (post : α → ω → Pred) {epost : EPred} :
    Triple (MonadLift.monadLift x : WriterT ω m α)
      (fun w => wp x (fun a => post a w) epost) post epost :=
  Triple.intro (WriterT.le_wp_monadLift x post epost)

@[spec]
theorem Spec.mk_WriterT {α : Type u} (x : m (α × ω)) (post : α → ω → Pred) {epost : EPred} :
    Triple (WriterT.mk x : WriterT ω m α)
      (fun w => wp x (fun p => post p.1 (w * p.2)) epost) post epost :=
  Triple.intro fun _ => Lean.Order.PartialOrder.rel_refl

@[spec]
theorem Spec.run_WriterT {α : Type u} (x : WriterT ω m α) (post : α × ω → Pred)
    {epost : EPred} :
    Triple (x.run : m (α × ω)) (wp x (fun a w => post (a, w)) epost 1) post epost :=
  Triple.intro (by rw [WriterT.wp_run_eq])

end WriterTSpec

end Std.WP

namespace Std.WP

section OptionTSpec

variable {m : Type u → Type v} {Pred EPred : Type u} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] {α : Type u}

/-- `failure` in `OptionT` establishes the failure postcondition. -/
@[spec]
theorem Spec.failure_OptionT (post : α → Pred) (epost : (Unit → Pred) × EPred) :
    Triple (failure : OptionT m α) (epost.fst ()) post epost :=
  ⟨by
    rw [OptionT.wp_apply_eq]
    exact WPMonad.pure_le_wp_pure (m := m) none (Lean.Order.pushOption post epost.fst)
      epost.snd⟩

/-- `OptionT.lift` runs the base computation and succeeds. -/
@[spec]
theorem Spec.lift_OptionT (x : m α) (post : α → Pred) (epost : (Unit → Pred) × EPred) :
    Triple (OptionT.lift x) (wp x post epost.snd) post epost :=
  Spec.monadLift_OptionT x post epost

/-- `guard p` in `OptionT` over a `Prop`-valued reading: the success postcondition when `p`
holds and the failure postcondition when it does not, as a meet of two implications. -/
@[spec]
theorem Spec.guard_OptionT {m : Type → Type} {EPred : Type} [Monad m] [Assertion EPred]
    [WPMonad m Prop EPred] (p : Prop) [Decidable p] (post : Unit → Prop)
    (epost : (Unit → Prop) × EPred) :
    Triple (guard p : OptionT m Unit)
      (Lean.Order.meet (Lean.Order.himp (Lean.Order.CompleteLattice.ofProp p) (post ()))
        (Lean.Order.himp (Lean.Order.CompleteLattice.ofProp (¬ p)) (epost.fst ())))
      post epost := by
  refine ⟨fun h => ?_⟩
  simp only [Lean.Order.meet_prop_eq_and, Lean.Order.himp_prop_eq_imp,
    Lean.Order.CompleteLattice.ofProp, Lean.Order.top_prop_eq, Lean.Order.bot_prop_eq] at h
  unfold _root_.guard
  split
  · exact (Spec.pure (post := post) ()).le_wp (h.1 (by simp [*]))
  · exact (Spec.failure_OptionT post epost).le_wp (h.2 (by simp [*]))

end OptionTSpec

open Lean.Order

/-! ## `StateT`

Core's transformer interpretations keep the assertion languages in the universe of the monad's
values. -/

section StateT

variable {m : Type u → Type v} {Pred EPred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {σ α : Type u}

/-- `StateT.lift x` is `monadLift x`: the base computation runs at the incoming state. -/
@[spec]
theorem Spec.lift_StateT (x : m α) (post : α → σ → Pred) {epost : EPred} :
    ⦃ fun s => wp x (fun a => post a s) epost ⦄ (StateT.lift x : StateT σ m α) ⦃ post; epost ⦄ :=
  Spec.monadLift_StateT x post

/-- `StateT.mk f` runs `f` at the incoming state. -/
@[spec]
theorem Spec.mk_StateT (f : σ → m (α × σ)) (post : α → σ → Pred) {epost : EPred} :
    ⦃ fun s => wp (f s) (fun p => post p.1 p.2) epost ⦄ (StateT.mk f : StateT σ m α)
      ⦃ post; epost ⦄ :=
  ⟨fun _ => PartialOrder.rel_refl⟩

/-- Running a `StateT` computation at a state and discarding the final state. -/
@[spec]
theorem Spec.run'_StateT (x : StateT σ m α) (s : σ) (post : α → Pred) {epost : EPred} :
    ⦃ wp x (fun a _ => post a) epost s ⦄ x.run' s ⦃ post; epost ⦄ :=
  ⟨by
    rw [StateT.wp_apply_eq]
    exact WPMonad.map_le_wp_map (fun p : α × σ => p.1) (x.run s) post epost⟩

end StateT

/-! ## `OptionT`

Running an `OptionT` computation into a postcondition of the option: core's `Spec.run_OptionT`
states the postcondition it pushes, so it applies when the goal's postcondition has that shape;
the rule here takes any postcondition and outranks it. -/

section OptionT

variable {m : Type u → Type v} {Pred EPred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type u}

/-- `OptionT.mk x` is the base computation `x`, read through the option it returns. -/
@[spec]
theorem Spec.mk_OptionT (x : m (Option α)) (post : α → Pred) (epost : (Unit → Pred) × EPred) :
    ⦃ wp x (pushOption post epost.fst) epost.snd ⦄ OptionT.mk x ⦃ post; epost ⦄ :=
  ⟨by rw [OptionT.wp_apply_eq]; exact PartialOrder.rel_refl⟩

/-- Running an `OptionT` computation into a postcondition of the returned option: success
establishes it at `some`, failure at `none`. -/
@[spec high]
theorem Spec.run_OptionT' (x : OptionT m α) (post : Option α → Pred) {epost : EPred} :
    ⦃ wp x (fun a => post (some a)) (fun _ => post none, epost) ⦄ x.run ⦃ post; epost ⦄ :=
  ⟨by
    rw [OptionT.wp_apply_eq]
    have h : pushOption (fun a => post (some a)) (fun _ => post none) = post := by
      funext o; cases o <;> rfl
    rw [h]⟩

end OptionT

/-! ## `ExceptT` -/

section ExceptT

variable {m : Type u → Type v} {Pred EPred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {ε α : Type u}

/-- `ExceptT.lift x` is `monadLift x`: the base computation runs and succeeds. -/
@[spec]
theorem Spec.lift_ExceptT (x : m α) (post : α → Pred) (epost : (ε → Pred) × EPred) :
    ⦃ wp x post epost.snd ⦄ (ExceptT.lift x : ExceptT ε m α) ⦃ post; epost ⦄ :=
  Spec.monadLift_ExceptT x post epost

/-- `ExceptT.mk x` is the base computation `x`, read through the result it returns. -/
@[spec]
theorem Spec.mk_ExceptT (x : m (Except ε α)) (post : α → Pred) (epost : (ε → Pred) × EPred) :
    ⦃ wp x (pushExcept post epost.fst) epost.snd ⦄ ExceptT.mk x ⦃ post; epost ⦄ :=
  ⟨by rw [ExceptT.wp_apply_eq]; exact PartialOrder.rel_refl⟩

/-- Running an `ExceptT` computation into a postcondition of the returned result: success
establishes it at `ok`, an exception at `error`. -/
@[spec high]
theorem Spec.run_ExceptT' (x : ExceptT ε m α) (post : Except ε α → Pred) {epost : EPred} :
    ⦃ wp x (fun a => post (.ok a)) (fun e => post (.error e), epost) ⦄ x.run ⦃ post; epost ⦄ :=
  ⟨by
    rw [ExceptT.wp_apply_eq]
    have h : pushExcept (fun a => post (.ok a)) (fun e => post (.error e)) = post := by
      funext r; cases r <;> rfl
    rw [h]⟩

end ExceptT

/-! ## `guard` -/

section guard

variable {m : Type → Type v} {Pred EPred : Type}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- `guard p` in `OptionT` for every assertion carrier: the postcondition when `p` holds and the
failure assertion when it does not, stated with lattice connectives so that every reading
decomposes it. `Spec.guard_OptionT` above is stated for `Prop` assertions and takes precedence
there. -/
@[spec low]
theorem Spec.guard_OptionT_iInf (p : Prop) [Decidable p] (post : Unit → Pred)
    (epost : (Unit → Pred) × EPred) :
    ⦃ (Lean.Order.iInf fun _ : PLift p => post ()) ⊓
        (Lean.Order.iInf fun _ : PLift ¬p => epost.1 ()) ⦄ (guard p : OptionT m Unit)
      ⦃ post; epost ⦄ := by
  rw [Triple.iff]
  unfold guard
  split_ifs with hp
  · exact PartialOrder.rel_trans (meet_le_left _ _)
      (PartialOrder.rel_trans (iInf_le _ ⟨hp⟩) (Spec.pure ()).le_wp)
  · exact PartialOrder.rel_trans (meet_le_right _ _)
      (PartialOrder.rel_trans (iInf_le _ ⟨hp⟩) (Spec.failure_OptionT post epost).le_wp)

end guard

/-! ## `List.mapM` -/

section mapM

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type w'} {β : Type u}

/-- `List.mapM` with a loop invariant over the elements consumed so far, the elements remaining,
and the outputs so far; each step maps one element and appends its output. -/
@[spec]
theorem Spec.mapM_list {xs : List α} {f : α → m β} (inv : Invariant α (List β) Pred)
    {epost : EPred}
    (step : ∀ pref cur suff bs, xs = pref ++ cur :: suff →
      ⦃ inv pref (cur :: suff) bs ⦄ f cur
        ⦃ fun b => inv (pref ++ [cur]) suff (bs ++ [b]); epost ⦄) :
    ⦃ inv [] xs [] ⦄ xs.mapM f ⦃ fun bs => inv xs [] bs; epost ⦄ := by
  suffices h : ∀ pref suff bs, xs = pref ++ suff →
      ⦃ inv pref suff bs ⦄ suff.mapM f ⦃ fun bs' => inv xs [] (bs ++ bs'); epost ⦄ by
    simpa using h [] xs [] rfl
  intro pref suff
  induction suff generalizing pref with
  | nil =>
    intro bs hxs
    simp only [List.mapM_nil]
    refine Triple.pure _ ?_
    simp only [List.append_nil] at hxs
    subst hxs
    simp only [List.append_nil]
    exact PartialOrder.rel_refl
  | cons x suff ih =>
    intro bs hxs
    simp only [List.mapM_cons]
    refine Triple.bind (f x) _ (fun b => inv (pref ++ [x]) suff (bs ++ [b]))
      (step pref x suff bs hxs) fun b => ?_
    refine Triple.bind (suff.mapM f) _ (fun bs' => inv xs [] (bs ++ [b] ++ bs'))
      (ih (pref ++ [x]) (bs ++ [b]) (by simp [hxs])) fun bs' => ?_
    refine Triple.pure _ ?_
    simp only [List.append_assoc, List.singleton_append]
    exact PartialOrder.rel_refl

end mapM

/-! ## Sequencing -/

section seq

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α β : Type u}

/-- `x <* y` runs both and keeps the first value. -/
@[spec]
theorem Spec.seqLeft (x : m α) (y : m β) (post : α → Pred) {epost : EPred} :
    ⦃ wp x (fun a => wp y (fun _ => post a) epost) epost ⦄ (x <* y) ⦃ post; epost ⦄ :=
  ⟨by
    rw [seqLeft_eq]
    refine PartialOrder.rel_trans ?_ (Spec.seq (Function.const β <$> x) y).le_wp
    exact WPMonad.map_le_wp_map (Function.const β) x
      (fun f => wp y (fun a => post (f a)) epost) epost⟩

/-- `x *> y` runs both and keeps the second value. -/
@[spec]
theorem Spec.seqRight (x : m α) (y : m β) (post : β → Pred) {epost : EPred} :
    ⦃ wp x (fun _ => wp y post epost) epost ⦄ (x *> y) ⦃ post; epost ⦄ :=
  ⟨by
    rw [seqRight_eq]
    refine PartialOrder.rel_trans ?_ (Spec.seq (Function.const α id <$> x) y).le_wp
    exact WPMonad.map_le_wp_map (Function.const α id) x
      (fun f => wp y (fun a => post (f a)) epost) epost⟩

end seq

end Std.WP
