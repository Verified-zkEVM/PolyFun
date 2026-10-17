/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Resumption
public import ToCslib.Order.OmegaCompletePartialOrder

/-!
# Continuous interpretations of resumptions

A continuous algebra interprets a query from the meanings of its answer
branches. The least solution of these equations gives a meaning to infinite
trees without assuming termination, finite branching, or a uniform depth
bound. Cutoffs denote bottom; a visible operation can itself contribute
information even when all its continuations denote bottom.
-/

public section

open OmegaCompletePartialOrder

namespace PFunctor.Resumption

universe uA uB uα uD

variable {P : PFunctor.{uA, uB}} {α : Type uα} {D : Type uD}
  [OmegaCompletePartialOrder D] [OrderBot D]

/-- A query algebra continuous in the family of continuation meanings. -/
abbrev ContinuousAlgebra (P : PFunctor.{uA, uB}) (D : Type uD)
    [OmegaCompletePartialOrder D] := ∀ a : P.A, (P.B a → D) →𝒄 D

/-- One unfolding of the interpretation equations. -/
@[expose] def domainStep (ret : α → D) (alg : ContinuousAlgebra P D) :
    (Resumption P α → D) →𝒄 (Resumption P α → D) :=
  .ofFun (fun meaning tree => match dest tree with
    | .inl value => ret value
    | .inr ⟨operation, next⟩ => alg operation (fun answer => meaning (next answer))) (by
      apply ωScottContinuous.of_apply₂
      intro tree
      cases dest tree with
      | inl value => exact ωScottContinuous.const
      | inr node =>
          exact (alg node.1).ωScottContinuous.comp
            (ωScottContinuous.of_apply₂ fun answer => ωScottContinuous.apply (node.2 answer)))

/-- The least continuous-algebra interpretation of a possibly infinite tree. -/
@[expose] def denote (ret : α → D) (alg : ContinuousAlgebra P D) : Resumption P α → D :=
  (domainStep ret alg).fix

/-- The interpretation satisfies its one-step equations. -/
theorem denote_eq (ret : α → D) (alg : ContinuousAlgebra P D) (tree : Resumption P α) :
    denote ret alg tree = match dest tree with
      | .inl value => ret value
      | .inr ⟨operation, next⟩ => alg operation (fun answer => denote ret alg (next answer)) :=
  (congrFun (domainStep ret alg).map_fix tree).symm

@[simp] theorem denote_pure (ret : α → D) (alg : ContinuousAlgebra P D) (value : α) :
    denote ret alg (pure value) = ret value := by
  rw [denote_eq, dest_pure]

@[simp] theorem denote_query (ret : α → D) (alg : ContinuousAlgebra P D) (operation : P.A)
    (next : P.B operation → Resumption P α) :
    denote ret alg (query operation next) =
      alg operation (fun answer => denote ret alg (next answer)) := by
  rw [denote_eq, dest_query]

/-- Any upper solution of the equations bounds the interpretation. -/
theorem denote_le (ret : α → D) (alg : ContinuousAlgebra P D) (meaning : Resumption P α → D)
    (h : ∀ tree, (match dest tree with
      | .inl value => ret value
      | .inr ⟨operation, next⟩ => alg operation (fun answer => meaning (next answer))) ≤
        meaning tree) :
    denote ret alg ≤ meaning :=
  (domainStep ret alg).fix_le h

/-- The infinite-tree interpretation agrees with the ordinary fold on every
well-founded tree, including trees without a uniform finite depth bound. -/
theorem denote_toResumption (ret : α → D) (alg : ContinuousAlgebra P D)
    (program : FreeM P α) :
    denote ret alg (FreeM.toResumption program) =
      FreeM.foldFreeM ret (fun a => alg a) program := by
  induction program with
  | pure value => simp
  | lift_bind operation next ih =>
      change denote ret alg (FreeM.toResumption (.liftBind operation next)) =
        FreeM.foldFreeM ret (fun a => alg a) (.liftBind operation next)
      rw [FreeM.toResumption_liftBind, denote_query, FreeM.foldFreeM_liftBind]
      exact congrArg (alg operation) (funext ih)

/-- A lens transports a continuous algebra by reindexing its answer family. -/
@[expose] def ContinuousAlgebra.comap {Q : PFunctor} (alg : ContinuousAlgebra Q D)
    (lens : Lens P Q) : ContinuousAlgebra P D := fun a =>
  .ofFun (fun k => alg (lens.toFunA a) (fun b => k (lens.toFunB a b))) (by
    exact (alg (lens.toFunA a)).ωScottContinuous.comp
      (ωScottContinuous.of_apply₂ fun b => ωScottContinuous.apply (lens.toFunB a b)))

/-- Interpretations are invariant under transporting an operation signature
and its algebra along a polynomial lens. -/
theorem denote_mapLens {Q : PFunctor} (ret : α → D) (alg : ContinuousAlgebra Q D)
    (lens : Lens P Q) (tree : Resumption P α) :
    denote ret alg (mapLens lens tree) = denote ret (alg.comap lens) tree := by
  let pre : (Resumption Q α → D) →𝒄 (Resumption P α → D) :=
    .ofFun (fun f t => f (mapLens lens t))
  have comm (f : Resumption Q α → D) :
      pre (domainStep ret alg f) = domainStep ret (alg.comap lens) (pre f) := by
    funext t
    simp only [pre, ContinuousHom.ofFun_apply, domainStep, dest_mapLens]
    cases dest t <;> rfl
  exact congrFun ((domainStep ret alg).fix_fusion
    (domainStep ret (alg.comap lens)) pre rfl comm) tree

end PFunctor.Resumption
