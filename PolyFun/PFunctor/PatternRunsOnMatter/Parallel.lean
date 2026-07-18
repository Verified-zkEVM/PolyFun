/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Compatibility
public import PolyFun.PFunctor.PatternRunsOnMatter.Display

/-!
# Parallel Pattern-Runs-on-Matter reconstruction

G5 identifies categorical Pattern-Runs-on-Matter reconstruction with ordinary
responder reindexing.  Since G6 parallel reindexing is componentwise, the same
is true directly for `reindexViaRunAgainst`.
-/

@[expose] public section

universe uA uB uS₁ uS₂

namespace PFunctor
namespace Responder

/-- Pattern-Runs-on-Matter reconstruction commutes with parallel handlers and
parallel responders. -/
theorem reindexViaRunAgainst_parallel
    {P Q R V : PFunctor.{uA, uB}}
    {State₁ : Type uS₁} {State₂ : Type uS₂}
    (leftHandler : Handler (FreeM P) R)
    (rightHandler : Handler (FreeM Q) V)
    (left : Responder State₁ P) (right : Responder State₂ Q) :
    reindexViaRunAgainst (Handler.parallel leftHandler rightHandler)
        (Responder.parallel left right) =
      Responder.parallel
        (reindexViaRunAgainst leftHandler left)
        (reindexViaRunAgainst rightHandler right) := by
  rw [reindexViaRunAgainst_eq_reindex, reindex_parallel,
    reindexViaRunAgainst_eq_reindex, reindexViaRunAgainst_eq_reindex]

end Responder
end PFunctor
