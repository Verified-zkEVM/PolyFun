/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunComplexitylib.Oracle.QueryBound
public import PolyFun.PFunctor.Handler.Stateful

/-!
# complexitylib oracle programs are PolyFun free programs

The definitional identities below are the whole oracle-layer bridge: complexitylib's programs,
calls, interpreters and stateful runs are PolyFun's, so PolyFun's free-monad API applies without
translation. The query-bound bridge is then exercised on probabilistic programs, whose uniform
sampling interface answers every query.
-/

@[expose] public section

open Cslib PFunctor

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

example : OracleComp spec α = (PFunctor.mk ι spec).FreeM α := rfl

example (q : ι) :
    OracleComp.query (spec := spec) q = FreeM.lift (P := PFunctor.mk ι spec) q := rfl

example {m : Type → Type} [Monad m] (oracle : (q : ι) → m (spec q)) (p : OracleComp spec α) :
    OracleComp.interpret oracle p = p.liftM oracle := rfl

/-- A complexitylib stateful oracle is a PolyFun stateful handler, with the same run. -/
example {State : Type} (oracle : (q : ι) → StateT State PMF (spec q)) (p : OracleComp spec α)
    (s : State) :
    (OracleComp.interpret oracle p).run s = Handler.Stateful.run oracle p s := rfl

/-- PolyFun's structural bound lemmas apply to complexitylib programs directly. -/
example (q : ι) (k : spec q → OracleComp spec α) (hk : ∀ y, FreeM.IsTotalRollBound (k y) 2) :
    FreeM.IsTotalRollBound (OracleComp.query q >>= k) 3 :=
  (FreeM.isTotalRollBound_lift_bind_iff' (P := PFunctor.mk ι spec) q k 3).mpr ⟨by decide, hk⟩

/-- Two uniform samples: two calls, each of size at most `5`. -/
def twoSamples : ProbComp (Fin 4 × Fin 6) := do
  let a ← ProbComp.unifFin 3
  let b ← ProbComp.unifFin 5
  pure (a, b)

/-- The structural budget of `twoSamples` gives complexitylib's semantic query bound. -/
example : twoSamples.HasQueryBounds id 2 5 :=
  OracleComp.hasQueryBounds_of_isRollBound (by
    simp only [twoSamples, ProbComp.unifFin, OracleComp.query, bind_pure_comp,
      FreeM.isRollBound_lift_bind_iff']
    refine ⟨by decide, fun _ => ?_⟩
    exact (FreeM.isRollBound_map_iff _ _ _ _ _).mpr ⟨by decide, fun _ => trivial⟩)

/-- Uniform sampling answers every query, so the semantic and structural bounds agree. -/
example (p : ProbComp α) (calls maxSize : ℕ) :
    p.HasQueryBounds id calls maxSize ↔
      FreeM.IsRollBound p calls (fun q n => 0 < n ∧ q ≤ maxSize) (fun _ n => n - 1) :=
  OracleComp.hasQueryBounds_iff_isRollBound
