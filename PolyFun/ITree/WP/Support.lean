/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Support
public import PolyFun.ITree.WP.Basic

/-!
# Weakest preconditions and possible outputs of interaction trees

The two canonical `Prop` specs of `PolyFun.PFunctor.Free.WP` read the support of an interaction
tree. The demonic spec asks something of every answer; the angelic spec, of some answer.
* Partial correctness under the demonic spec is the always judgment `MonadAttach.AllOutputs`.
  Every possible output satisfies the postcondition, and divergence imposes nothing
  (`ITree.wpPartial_demonic_iff_allOutputs`).
* Total correctness under the angelic spec is the sometimes judgment `MonadAttach.SomeOutput`.
  Some finite run returns a value that satisfies the postcondition
  (`ITree.wpTotal_angelic_iff_someOutput`).

These mirror `PFunctor.FreeM.wpFold_demonic_iff_allOutputs` and
`PFunctor.FreeM.wpFold_angelic_iff_someOutput`. On a finite program the readings coincide, while
an interaction tree separates them.
-/

@[expose] public section

universe uA uB uα

namespace ITree

open PFunctor MonadAttach

variable {F : PFunctor.{uA, uB}} {α : Type uα}

/-- Partial correctness under the demonic spec is the always judgment: every possible output
satisfies the postcondition. Divergence and infinite query paths impose nothing. -/
theorem wpPartial_demonic_iff_allOutputs {t : ITree F α} {post : α → Prop} :
    wpPartial (OpSpec.demonic F) t post ↔ AllOutputs post t := by
  constructor
  · intro h r hr
    change CanReturn t r at hr
    induction hr with
    | pure hs => rwa [eq_pure_of_dest hs, wpPartial_pure OpSpec.demonic_mono] at h
    | step hs _ ih =>
      rw [eq_step_of_dest hs, wpPartial_step OpSpec.demonic_mono] at h
      exact ih h
    | query hs b _ ih =>
      rw [eq_query_of_dest hs, wpPartial_query OpSpec.demonic_mono] at h
      exact ih (h b)
  · intro h
    refine le_wpPartial_of_le_wpStepFun (X := fun t => AllOutputs post t) ?_ t h
    intro t ht
    induction t using shape_cases with
    | pure r =>
      rw [wpStepFun_pure]
      exact ht r (CanReturn.of_pure r)
    | step t =>
      rw [wpStepFun_step]
      exact fun r hr => ht r (CanReturn.of_step hr)
    | query a k =>
      rw [wpStepFun_query]
      exact fun b r hr => ht r (CanReturn.of_query b hr)

/-- Total correctness under the demonic spec implies the always judgment. -/
theorem allOutputs_of_wpTotal_demonic {t : ITree F α} {post : α → Prop}
    (h : wpTotal (OpSpec.demonic F) t post) : AllOutputs post t :=
  wpPartial_demonic_iff_allOutputs.mp (wpTotal_le_wpPartial OpSpec.demonic_mono t h)

/-- Total correctness under the angelic spec is the sometimes judgment: some finite run returns a
value that satisfies the postcondition. A tree that never returns satisfies nothing. -/
theorem wpTotal_angelic_iff_someOutput {t : ITree F α} {post : α → Prop} :
    wpTotal (OpSpec.angelic F) t post ↔ SomeOutput post t := by
  constructor
  · intro h
    refine wpTotal_le_of_wpStepFun_le (X := fun t => SomeOutput post t) ?_ t h
    intro t ht
    induction t using shape_cases with
    | pure r =>
      rw [wpStepFun_pure] at ht
      exact ⟨r, CanReturn.of_pure r, ht⟩
    | step t =>
      rw [wpStepFun_step] at ht
      obtain ⟨r, hr, hp⟩ := ht
      exact ⟨r, CanReturn.of_step hr, hp⟩
    | query a k =>
      rw [wpStepFun_query] at ht
      obtain ⟨b, r, hr, hp⟩ := ht
      exact ⟨r, CanReturn.of_query b hr, hp⟩
  · rintro ⟨r, hr, hp⟩
    change CanReturn t r at hr
    induction hr with
    | pure hs => rwa [eq_pure_of_dest hs, wpTotal_pure OpSpec.angelic_mono]
    | step hs _ ih =>
      rw [eq_step_of_dest hs, wpTotal_step OpSpec.angelic_mono]
      exact ih hp
    | query hs b _ ih =>
      rw [eq_query_of_dest hs, wpTotal_query OpSpec.angelic_mono]
      exact ⟨b, ih hp⟩

end ITree
