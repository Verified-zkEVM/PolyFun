/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Free.Code
public import PolyFun.PFunctor.Free.WP.Charge

/-!
# The cost fold of a charge

A charge `χ : P.A → ℕ` on the operations of a polynomial functor `P` gives the cost fold
`cost χ : P.FreeM α → ℕ∞`, the worst-case charge of a program tree: a leaf costs `0`, and a node
at `a` costs `χ a` plus the supremum of the costs of its continuations. It is the charge fold
`wpFold (OpSpec.charge χ) x (fun _ => 0)`. For a code `c` (`PolyFun.PFunctor.Free.Code`), the cost
fold over `Code.interp c` is the third interpretation of `c`, beside the container and the
relational lift `FreeRel`.

## Main definitions

* `PFunctor.FreeM.cost` — the cost fold of a charge.

## Main results

* `cost_pure`, `cost_liftBind` — the equations of the fold;
* `cost_bind_le_of_wpFold`, `cost_bind_le` — the cost of a bind is at most the cost of the
  program plus the supremum of the costs of the continuation at the returns satisfying an
  invariant of the program;
* `cost_mono` — monotonicity in the charge;
* `PFunctor.FreeRel.cost_eq` — programs related by the relational lift have the same cost;
* `cost_mapLens_le`, `cost_mapLens_of_surjective`, `cost_freeMCongr_toLensEquiv` — the cost
  along a lens and along an equivalence of polynomial functors;
* `wpFold_demonic_mapLens_iff`, `wpFold_demonic_freeMCongr_toLensEquiv_iff` — the invariant on
  returns along a lens with surjective maps of directions and along an equivalence.

The fold is `noncomputable`: it takes suprema in `ℕ∞`, whose complete-lattice structure is
classical.
-/

@[expose] public section

universe u v u' v' w w'

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{u, v}} {Q : PFunctor.{u', v'}} {α : Type w} {β : Type w'}

/-- The cost fold of the charge `χ`: the worst-case charge of a program tree, `0` at a leaf and
`χ a` plus the supremum over the directions of the continuations at a node at `a`. -/
noncomputable def cost (χ : P.A → ℕ) (x : P.FreeM α) : ℕ∞ :=
  wpFold (OpSpec.charge fun a => (χ a : ℕ∞)) x fun _ => 0

/-- A leaf costs nothing. -/
@[simp] theorem cost_pure (χ : P.A → ℕ) (a : α) : cost χ (pure a : P.FreeM α) = 0 := rfl

/-- A node costs its charge plus the supremum of the costs of its continuations. -/
theorem cost_liftBind (χ : P.A → ℕ) (a : P.A) (k : P.B a → P.FreeM α) :
    cost χ (FreeM.liftBind a k) = χ a + ⨆ d, cost χ (k d) := rfl

/-- Every return of a program satisfies the trivial invariant. -/
theorem wpFold_demonic_true (x : P.FreeM α) : wpFold (OpSpec.demonic P) x fun _ => True :=
  (wpFold_demonic_iff_allOutputs x _).2 (by simp)

/-- **Cost of a bind.** When every return of `x` satisfies `I`, the cost of `x >>= f` is at most
the cost of `x` plus the supremum of the costs of `f a` over the returns `a` satisfying `I`. -/
theorem cost_bind_le_of_wpFold (χ : P.A → ℕ) {x : P.FreeM α} {f : α → P.FreeM β}
    {I : α → Prop} (hI : wpFold (OpSpec.demonic P) x I) :
    cost χ (x.bind f) ≤ cost χ x + ⨆ (a : α) (_ : I a), cost χ (f a) := by
  induction x with
  | pure a => simpa using le_iSup₂ (f := fun a (_ : I a) => cost χ (f a)) a hI
  | lift_bind a k ih =>
    change (χ a : ℕ∞) + ⨆ d, cost χ ((k d).bind f) ≤ ((χ a : ℕ∞) + ⨆ d, cost χ (k d)) + _
    rw [add_assoc]
    refine add_le_add le_rfl (iSup_le fun d => (ih d (hI d)).trans ?_)
    exact add_le_add (le_iSup (fun d => cost χ (k d)) d) le_rfl

/-- The cost of a bind is at most the cost of the program plus the supremum of the costs of the
continuation. -/
theorem cost_bind_le (χ : P.A → ℕ) (x : P.FreeM α) (f : α → P.FreeM β) :
    cost χ (x.bind f) ≤ cost χ x + ⨆ a, cost χ (f a) :=
  (cost_bind_le_of_wpFold χ (wpFold_demonic_true x)).trans (by simp)

/-- The cost fold is monotone in the charge. -/
theorem cost_mono {χ χ' : P.A → ℕ} (h : ∀ a, χ a ≤ χ' a) (x : P.FreeM α) :
    cost χ x ≤ cost χ' x := by
  induction x with
  | pure a => exact le_rfl
  | lift_bind a k ih =>
    change (χ a : ℕ∞) + ⨆ d, cost χ (k d) ≤ (χ' a : ℕ∞) + ⨆ d, cost χ' (k d)
    exact add_le_add (by exact_mod_cast h a) (iSup_mono ih)

end FreeM

/-- **Invariance under the relational lift.** Programs related by the lift of any relation have
the same cost. -/
theorem FreeRel.cost_eq {P : PFunctor.{u, v}} {α : Type w} {β : Type w'} {R : α → β → Prop}
    (χ : P.A → ℕ) {x : P.FreeM α} {y : P.FreeM β} (h : FreeRel P R x y) :
    FreeM.cost χ x = FreeM.cost χ y := by
  induction h with
  | pure _ => rfl
  | liftBind a _ ih => rw [FreeM.cost_liftBind, FreeM.cost_liftBind, iSup_congr ih]

namespace FreeM

variable {P : PFunctor.{u, v}} {Q : PFunctor.{u', v'}} {α : Type w}

/-! ## Cost along lenses -/

/-- The cost of a program mapped along a lens is at most the cost of the program at the charge
pulled back along the lens. -/
theorem cost_mapLens_le (l : Lens P Q) (χ : Q.A → ℕ) (x : P.FreeM α) :
    cost χ (x.mapLens l) ≤ cost (χ ∘ l.toFunA) x := by
  induction x with
  | pure a => exact le_rfl
  | lift_bind a k ih =>
    change (χ (l.toFunA a) : ℕ∞) + ⨆ d, cost χ ((k (l.toFunB a d)).mapLens l) ≤
      ((χ ∘ l.toFunA) a : ℕ∞) + ⨆ b, cost (χ ∘ l.toFunA) (k b)
    exact add_le_add le_rfl
      (iSup_le fun d => (ih _).trans (le_iSup (fun b => cost (χ ∘ l.toFunA) (k b)) _))

/-- Along a lens whose maps of directions are surjective, the cost of a mapped program is the
cost of the program at the charge pulled back along the lens. -/
theorem cost_mapLens_of_surjective (l : Lens P Q) (hl : ∀ a, Function.Surjective (l.toFunB a))
    (χ : Q.A → ℕ) (x : P.FreeM α) : cost χ (x.mapLens l) = cost (χ ∘ l.toFunA) x := by
  induction x with
  | pure a => rfl
  | lift_bind a k ih =>
    change (χ (l.toFunA a) : ℕ∞) + ⨆ d, cost χ ((k (l.toFunB a d)).mapLens l) =
      ((χ ∘ l.toFunA) a : ℕ∞) + ⨆ b, cost (χ ∘ l.toFunA) (k b)
    simp only [ih]
    rw [(hl a).iSup_comp (fun b => cost (χ ∘ l.toFunA) (k b))]
    rfl

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
theorem cost_freeMCongr_toLensEquiv (e : P ≃ₚ Q) (χ : Q.A → ℕ) (x : P.FreeM α) :
    cost χ (freeMCongr (PFunctor.Equiv.toLensEquiv e) x) = cost (χ ∘ e.equivA) x :=
  cost_mapLens_of_surjective _ (fun a => (e.equivB a).symm.surjective) χ x

/-- The invariant on returns along an equivalence of polynomial functors. -/
theorem wpFold_demonic_freeMCongr_toLensEquiv_iff (e : P ≃ₚ Q) (x : P.FreeM α)
    (I : α → Prop) :
    wpFold (OpSpec.demonic Q) (freeMCongr (PFunctor.Equiv.toLensEquiv e) x) I ↔
      wpFold (OpSpec.demonic P) x I :=
  wpFold_demonic_mapLens_iff _ (fun a => (e.equivB a).symm.surjective) x I

end FreeM

end PFunctor
