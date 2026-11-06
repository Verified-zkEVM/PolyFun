/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Free.Code
public import PolyFun.PFunctor.Free.Cost.Value

/-!
# The cost fold over codes

For a code `c` (`PolyFun.PFunctor.Free.Code`), the cost fold `PFunctor.FreeM.cost`
(`PolyFun.PFunctor.Free.Cost.Value`) over `Code.interp c` is the third interpretation of `c`,
beside the container and the relational lift `FreeRel`.

## Main results

* `PFunctor.FreeRel.cost_eq` — programs related by the relational lift have the same cost;
* `cost_freeMCongr_toLensEquiv` — the cost along an equivalence of polynomial functors;
* `wpFold_demonic_mapLens_iff`, `wpFold_demonic_freeMCongr_toLensEquiv_iff` — the invariant on
  returns along a lens with surjective maps of directions and along an equivalence.
-/

@[expose] public section

universe u v u' v' w w' x

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{u, v}} {α : Type w}

/-- Every return of a program satisfies the trivial invariant. -/
theorem wpFold_demonic_true (x : P.FreeM α) : wpFold (OpSpec.demonic P) x fun _ => True :=
  (wpFold_demonic_iff_allOutputs x _).2 (by simp)

end FreeM

/-- **Invariance under the relational lift.** Programs related by the lift of any relation have
the same cost. -/
theorem FreeRel.cost_eq {P : PFunctor.{u, v}} {α : Type w} {β : Type w'} {ω : Type x} [Add ω]
    [CompleteLattice ω] [Zero ω] {R : α → β → Prop} (c : P.A → ω) {x : P.FreeM α} {y : P.FreeM β}
    (h : FreeRel P R x y) : FreeM.cost c x = FreeM.cost c y := by
  induction h with
  | pure _ => rfl
  | liftBind a _ ih => rw [FreeM.cost_liftBind, FreeM.cost_liftBind, iSup_congr ih]

namespace FreeM

variable {P : PFunctor.{u, v}} {Q : PFunctor.{u', v'}} {α : Type w}

/-- Along a lens whose maps of directions are surjective, the invariant on returns of a mapped
program is the invariant on returns of the program. -/
theorem wpFold_demonic_mapLens_iff (l : Lens P Q) (hl : ∀ a, Function.Surjective (l.toFunB a))
    (x : P.FreeM α) (I : α → Prop) :
    wpFold (OpSpec.demonic Q) (x.mapLens l) I ↔ wpFold (OpSpec.demonic P) x I := by
  induction x with
  | pure a => exact Iff.rfl
  | lift_bind a k ih =>
    change (∀ d, wpFold (OpSpec.demonic Q) ((k (l.toFunB a d)).mapLens l) I) ↔
      ∀ b, wpFold (OpSpec.demonic P) (k b) I
    simp only [ih]
    exact ((hl a).forall (p := fun b => wpFold (OpSpec.demonic P) (k b) I)).symm

/-- The cost along an equivalence of polynomial functors is the cost at the charge pulled back
along the equivalence of positions. -/
theorem cost_freeMCongr_toLensEquiv {ω : Type x} [AddMonoid ω] [CompleteLattice ω] (e : P ≃ₚ Q)
    (c : Q.A → ω) (x : P.FreeM α) :
    cost c (freeMCongr (PFunctor.Equiv.toLensEquiv e) x) = cost (c ∘ e.equivA) x :=
  cost_mapLens_of_surjective _ (fun a => (e.equivB a).symm.surjective) c x

/-- The invariant on returns along an equivalence of polynomial functors. -/
theorem wpFold_demonic_freeMCongr_toLensEquiv_iff (e : P ≃ₚ Q) (x : P.FreeM α)
    (I : α → Prop) :
    wpFold (OpSpec.demonic Q) (freeMCongr (PFunctor.Equiv.toLensEquiv e) x) I ↔
      wpFold (OpSpec.demonic P) x I :=
  wpFold_demonic_mapLens_iff _ (fun a => (e.equivB a).symm.surjective) x I

end FreeM

end PFunctor
