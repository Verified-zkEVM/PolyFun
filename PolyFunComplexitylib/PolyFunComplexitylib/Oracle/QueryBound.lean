/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Complexity.Languages.Probabilistic.Transcript
public import PolyFun.PFunctor.Bound

/-!
# Structural and semantic query bounds

complexitylib's `Cslib.OracleComp` is `PFunctor.FreeM` of the polynomial `⟨ι, spec⟩`, so PolyFun's
structural roll bounds apply to its programs without translation. This file compares them with
complexitylib's semantic `Cslib.OracleComp.HasQueryBounds`, which bounds every transcript that any
stateful probabilistic oracle can produce.

The structural budget used throughout is the `PFunctor.FreeM.IsRollBound` instance that charges
one unit per query and admits a query only while budget remains and its size is at most
`maxSize`.

## Main results

* `Cslib.OracleComp.hasQueryBounds_of_isRollBound`: a structural budget is a semantic one.
* `Cslib.OracleComp.isRollBound_of_hasQueryBounds`: the converse, when every query is answerable.
* `Cslib.OracleComp.hasQueryBounds_iff_isRollBound`: the two coincide under that hypothesis.
* `Cslib.OracleComp.hasQueryBounds_of_isEmpty`: when some query has no answer, no oracle exists
  and the semantic predicate holds for every budget, so the hypothesis of the converse is needed.
-/

public section

universe u

namespace Cslib.OracleComp

open PFunctor

variable {Query : Type u} {Response : Query → Type u} {α : Type u}

/-- A structural query budget bounds every transcript of every stateful probabilistic oracle. -/
theorem hasQueryBounds_of_isRollBound {program : OracleComp Response α} {size : Query → ℕ}
    {calls maxSize : ℕ}
    (h : FreeM.IsRollBound program calls (fun q n => 0 < n ∧ size q ≤ maxSize)
      (fun _ n => n - 1)) :
    program.HasQueryBounds size calls maxSize := by
  induction program using PFunctor.FreeM.induction generalizing calls with
  | pure a => exact (HasQueryBounds.pure a size maxSize).mono (Nat.zero_le _) le_rfl
  | lift_bind q cont ih =>
    rw [FreeM.isRollBound_lift_bind_iff] at h
    obtain ⟨⟨hpos, hsize⟩, hcont⟩ := h
    have hbind := (HasQueryBounds.query (Response := Response) q size hsize).bind
      fun y => ih y (hcont y)
    exact hbind.mono (by omega) le_rfl

/-- If any query has no answer, no stateful probabilistic oracle exists, so every program
satisfies every semantic query bound. -/
theorem hasQueryBounds_of_isEmpty (q₀ : Query) [IsEmpty (Response q₀)]
    (program : OracleComp Response α) (size : Query → ℕ) (calls maxSize : ℕ) :
    program.HasQueryBounds size calls maxSize := by
  intro State oracle s
  obtain ⟨⟨a, _⟩, -⟩ := (oracle q₀ s).support_nonempty
  exact isEmptyElim a

section Converse

/-- Every transcript of a continuation, extended by the first query and its answer, is a
transcript of the whole program. The witnessing oracle answers the first query with `y` and then
behaves as `oracle`. -/
theorem HasQueryBounds.extend_query {q : Query} {cont : Response q → OracleComp Response α}
    {size : Query → ℕ} {calls maxSize : ℕ}
    (h : (OracleComp.query (spec := Response) q >>= cont).HasQueryBounds size calls maxSize)
    (y : Response q) {State : Type u} (oracle : (q : Query) → StateT State PMF (Response q))
    {s s' : State} {result : α} {transcript : Transcript Response}
    (hmem : (result, s', transcript) ∈
      ((interpret (withTranscript oracle) (cont y)).run (s, [])).support) :
    (transcript ++ ([⟨q, y⟩] : Transcript Response)).length ≤ calls ∧
      ∀ entry ∈ transcript ++ ([⟨q, y⟩] : Transcript Response), size entry.1 ≤ maxSize := by
  classical
  let first : (q' : Query) → StateT (State × Bool) PMF (Response q') := fun q' st =>
    if st.2 then
      if hq : q' = q then PMF.pure (cast (congrArg Response hq).symm y, (st.1, false))
      else (oracle q' st.1).map fun p => (p.1, (p.2, false))
    else (oracle q' st.1).map fun p => (p.1, (p.2, false))
  let represent : State × Transcript Response → (State × Bool) × Transcript Response :=
    fun x => ((x.1, false), x.2)
  have hsim := run_interpret_map_state (withTranscript oracle) (withTranscript first) represent
    (fun q' x => by
      obtain ⟨st, log⟩ := x
      simp [withTranscript, first, represent, PMF.map_comp, Function.comp_def])
    (cont y) (s, [])
  have hstep : (withTranscript first q).run ((s, true), []) =
      PMF.pure (y, ((s, false), ([⟨q, y⟩] : Transcript Response))) := by
    change (first q (s, true)).map _ = _
    simp [first]
  have hrun : (interpret (withTranscript first) (OracleComp.query q >>= cont)).run
      ((s, true), []) = (interpret (withTranscript first) (cont y)).run ((s, false), [⟨q, y⟩]) := by
    rw [interpret_bind, interpret_query, StateT.run_bind, hstep]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
  have hmem' : (result, (s', false), transcript ++ ([⟨q, y⟩] : Transcript Response)) ∈
      ((interpret (withTranscript first) (OracleComp.query q >>= cont)).run
        ((s, true), [])).support := by
    rw [hrun, run_interpret_withTranscript_append, PMF.mem_support_map_iff]
    refine ⟨(result, (s', false), transcript), ?_, rfl⟩
    change (result, represent (s', transcript)) ∈ _
    rw [show ((s, false), ([] : Transcript Response)) = represent (s, []) from rfl, ← hsim,
      PMF.mem_support_map_iff]
    exact ⟨_, hmem, rfl⟩
  exact h (State × Bool) first (s, true) (s', false) result _ hmem'

/-- A semantic bound on `query q >>= cont` bounds each continuation by one fewer call. -/
theorem HasQueryBounds.of_query_bind {q : Query} {cont : Response q → OracleComp Response α}
    {size : Query → ℕ} {calls maxSize : ℕ}
    (h : (OracleComp.query (spec := Response) q >>= cont).HasQueryBounds size calls maxSize)
    (y : Response q) : (cont y).HasQueryBounds size (calls - 1) maxSize := by
  intro State oracle s s' result transcript hmem
  obtain ⟨hlength, hsize⟩ := h.extend_query y oracle hmem
  simp only [List.length_append, List.length_singleton] at hlength
  exact ⟨by omega, fun entry hentry => hsize entry (List.mem_append_left _ hentry)⟩

/-- A semantic bound on `query q >>= cont` admits its first query, provided every query can be
answered. -/
theorem HasQueryBounds.first_query [∀ q, Nonempty (Response q)] {q : Query}
    {cont : Response q → OracleComp Response α} {size : Query → ℕ} {calls maxSize : ℕ}
    (h : (OracleComp.query (spec := Response) q >>= cont).HasQueryBounds size calls maxSize) :
    0 < calls ∧ size q ≤ maxSize := by
  let oracle : (q : Query) → StateT PUnit.{u + 1} PMF (Response q) :=
    fun q s => PMF.pure (Classical.choice inferInstance, s)
  let y : Response q := Classical.choice inferInstance
  obtain ⟨⟨result, s', transcript⟩, hmem⟩ :=
    ((interpret (withTranscript oracle) (cont y)).run (PUnit.unit, [])).support_nonempty
  obtain ⟨hlength, hsize⟩ := h.extend_query y oracle hmem
  simp only [List.length_append, List.length_singleton] at hlength
  exact ⟨by omega, hsize ⟨q, y⟩ (by simp)⟩

/-- When every query is answerable, a semantic query bound is a structural one. -/
theorem isRollBound_of_hasQueryBounds [∀ q, Nonempty (Response q)]
    {program : OracleComp Response α} {size : Query → ℕ} {calls maxSize : ℕ}
    (h : program.HasQueryBounds size calls maxSize) :
    FreeM.IsRollBound program calls (fun q n => 0 < n ∧ size q ≤ maxSize) (fun _ n => n - 1) := by
  induction program using PFunctor.FreeM.induction generalizing calls with
  | pure a => trivial
  | lift_bind q cont ih =>
    rw [FreeM.isRollBound_lift_bind_iff]
    exact ⟨h.first_query, fun y => ih y (h.of_query_bind y)⟩

/-- When every query is answerable, complexitylib's semantic query bounds are exactly PolyFun's
structural roll bounds. -/
theorem hasQueryBounds_iff_isRollBound [∀ q, Nonempty (Response q)]
    {program : OracleComp Response α} {size : Query → ℕ} {calls maxSize : ℕ} :
    program.HasQueryBounds size calls maxSize ↔
      FreeM.IsRollBound program calls (fun q n => 0 < n ∧ size q ≤ maxSize)
        (fun _ n => n - 1) :=
  ⟨isRollBound_of_hasQueryBounds, hasQueryBounds_of_isRollBound⟩

end Converse

end Cslib.OracleComp
