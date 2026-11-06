/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunComplexitylib.Backend.StepClass
import Complexity.Tactic.PPT
import Complexity.Computability.Probabilistic.Oracle.Composition

/-!
# Coverage of complexitylib's certificate automation

complexitylib certifies programs with `polytime` (deterministic tidy machines), `ppt` (closed
probabilistic programs) and `fun_prop` (oracle clients). This file records which program shapes
that automation closes at the pinned revision.

The first section holds shapes it certifies. The second holds shapes it does not, each wrapped in
`fail_if_success`. When complexitylib's automation learns one of them, the corresponding example
fails to build, and the wrapper should be removed (and any hand-written lemma it falls back to
reconsidered).
-/

open Cslib Cslib.Probability Turing.MultiTapeTM PFunctor

variable {α β γ ε : Type} {left : α ↪ List Bool} {right : β ↪ List Bool} {encC : γ ↪ List Bool}
  {encE : ε ↪ List Bool}

/-! ## Certified shapes -/

/-- Pair plumbing around a certified map. -/
example {f : α → β} (hf : ComputableTidilyInPolyTime f left right) :
    ComputableTidilyInPolyTime (fun p : α × ε => (f p.1, p.2))
      (encPair left encE) (encPair right encE) := by
  polytime

/-- A fair coin in `do` notation. -/
example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then word.reverse else word)) := by
  ppt

/-- The same program written with the free monad's `bind`. -/
example : IsPPTOn encBits encBits (fun word =>
    FreeM.bind (ProbComp.uniform Bool) fun bit => pure (if bit then word.reverse else word)) := by
  ppt

/-- A typed (paired) input. -/
example : IsPPTOn (encPair encBits encBits) encBits (fun p => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then p.1 else p.2)) := by
  ppt

/-- One external query whose reply is read through a bounded prefix. -/
example : IsOraclePPTOn (Operation := Unit) encBits encBits (fun word =>
    List.take 1 <$> ProbOracleComp.query ((), word)) := by
  fun_prop

/-- Adaptive queries, each reply read through a bounded prefix at its query site. -/
example : IsOraclePPTOn (Operation := Unit) encBits encBits (fun word => do
    let r ← List.take 1 <$> ProbOracleComp.query ((), word)
    let r' ← List.take 1 <$> ProbOracleComp.query ((), r)
    pure r') := by
  fun_prop

/-- Private randomness followed by a query. -/
example : IsOraclePPTOn (Operation := Unit) encBits encBits (fun word => do
    let bit ← ProbOracleComp.sample (spec := fun _ : Unit × List Bool => List Bool)
      (ProbComp.uniform Bool)
    List.take 1 <$> ProbOracleComp.query ((), if bit then word else word.reverse)) := by
  fun_prop

/-! ## Uncertified shapes -/

/-- Case analysis on a sum needs the hand-written `sumElim`. -/
example {f : α → γ} {g : β → γ} (hf : ComputableTidilyInPolyTime f left encC)
    (hg : ComputableTidilyInPolyTime g right encC) :
    ComputableTidilyInPolyTime (Sum.elim f g) (encSum left right) encC := by
  fail_if_success polytime
  exact ComputableTidilyInPolyTime.sumElim hf hg

/-- Mapping an optional value needs the hand-written `optionMap`. -/
example {f : α → β} (hf : ComputableTidilyInPolyTime f left right) :
    ComputableTidilyInPolyTime (Option.map f) (encOption left) (encOption right) := by
  fail_if_success polytime
  exact ComputableTidilyInPolyTime.optionMap hf

/-- Binding an optional value with a retained context needs the hand-written `optionBindCtx`. -/
example {k : α × ε → Option β}
    (hk : ComputableTidilyInPolyTime k (encPair left encE) (encOption right)) :
    ComputableTidilyInPolyTime (fun y : Option α × ε => y.1.bind fun j => k (j, y.2))
      (encPair (encOption left) encE) (encOption right) := by
  fail_if_success polytime
  exact ComputableTidilyInPolyTime.optionBindCtx hk

/-- `ppt` does not prove oracle goals; `fun_prop` does. -/
example : IsOraclePPTOn (Operation := Unit) encBits encBits (fun word => do
    let r ← List.take 1 <$> ProbOracleComp.query ((), word)
    let r' ← List.take 1 <$> ProbOracleComp.query ((), r)
    pure r') := by
  fail_if_success ppt
  fun_prop

/-- Uniform sampling from `Fin (n + 1)` has no certificate; only `ProbComp.uniform Bool` does. -/
example : True := by
  fail_if_success
    have : IsPPTOn encBits encBits (fun word => do
        let i ← ProbComp.unifFin 1
        pure (if i = 0 then word.reverse else word)) := by
      ppt
  trivial

/-- A raw query node, as PolyFun's free-monad API builds it, is not recognized as sampling. -/
example : True := by
  fail_if_success
    have : IsPPTOn encBits encBits (fun word =>
        FreeM.liftBind (P := PFunctor.mk ℕ unifSpec) 1 fun i =>
          pure (if i = 0 then word.reverse else word)) := by
      ppt
  trivial

/-- An adaptive client that binds a whole reply and truncates it later is not certified. -/
example : True := by
  fail_if_success
    have : IsOraclePPTOn (Operation := Unit) encBits encBits (fun word => do
        let r ← ProbOracleComp.query ((), word)
        let r' ← ProbOracleComp.query ((), List.take 1 r)
        pure (List.take 1 r')) := by
      fun_prop
  trivial
