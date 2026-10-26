/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.IPFunctor.Free.Bound
public import PolyFun.IPFunctor.Free.Traversal

/-!
# Resource bounds under traversals

A traversal chooses each target constructor from the source constructor and the current
traversal state, and that state changes along every branch. The target check and cost therefore
cannot be read through a fixed function of the source index and shape, as in
`IFreeM.IsRollBound.reindex`. The transport laws here instead relate source and target budgets
by a relation that may depend on the traversal state, and ask the constructor-local conditions
at every state.

* `IsRollBound.traverse`: related budgets stay related through each translated constructor,
  and every translated leaf is bounded at the related target budget.
* `IsRollBound.of_traverse`: when every response map is surjective, a target bound reflects
  to the source; translated leaves impose no condition.
* `IsRollBound.of_traverse_of_exists`: reflection only needs a compatible preimage of each
  source response at related budgets where the translated roll is allowed.

For charge bounds, `IsChargeBound.traverse` allows translated constructors that cost at most
their source constructors and translated leaves bounded by a common `m`, and adds `m` to the
budget; `IsChargeBound.of_traverse` reflects bounds when each source constructor costs at most
its translation; `isChargeBound_traverse_iff` combines them for equal charges and leaves of
zero cost, such as pure leaves.
-/

public section

universe uI uJ uA uB uC uD uR uX uY

namespace IPFunctor.IFreeM

variable {I : Type uI} {J : Type uJ} {P : Endo.{uI, uA, uB} I} {Q : Endo.{uJ, uC, uD} J}
  {S : I → J → Type uR} {X : I → Type uX} {Y : J → Type uY}
  {B : Type*} {B' : Type*}
  {canRoll : (i : I) → P.A i → B → Prop} {cost : (i : I) → P.A i → B → B}
  {canRoll' : (j : J) → Q.A j → B' → Prop} {cost' : (j : J) → Q.A j → B' → B'}

/-- A traversal preserves a roll bound along a budget relation `R`, which may read the
traversal state:
* `h_can` — at related budgets, a source roll allowed by `canRoll` has an allowed translation;
* `h_cost` — after an allowed source roll, the updated budgets are related at every next state;
* `h_leaf` — every translated leaf is bounded at any target budget related to a source one. -/
theorem IsRollBound.traverse (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j)
    (R : ∀ {i j}, S i j → B → B' → Prop)
    (h_can : ∀ {i j} (s : S i j) (a : P.A i) b b', R s b b' → canRoll i a b →
      canRoll' j (f.op s a) b')
    (h_cost : ∀ {i j} (s : S i j) (a : P.A i) b b', R s b b' → canRoll i a b →
      ∀ y, R (f.next s a y) (cost i a b) (cost' j (f.op s a) b'))
    (h_leaf : ∀ {i j} (s : S i j) (x : X i) b b', R s b b' →
      (leaf s x).IsRollBound b' canRoll' cost')
    {i j} {s : S i j} {x : IFreeM P X i} {b : B} {b' : B'}
    (hx : x.IsRollBound b canRoll cost) (hR : R s b b') :
    (x.traverse f leaf s).IsRollBound b' canRoll' cost' := by
  induction x using IFreeM.inductionOn generalizing j b b' with
  | pure _ x => exact h_leaf s x b b' hR
  | liftBind i a next ih =>
      rw [traverse_liftBind, isRollBound_liftBind_iff]
      exact ⟨h_can s a b b' hR hx.1,
        fun y => ih _ (hx.2 _) (h_cost s a b b' hR hx.1 y)⟩

/-- Reflect a roll bound using one compatible target response for each source response.
The witness condition is needed only at related budgets with an allowed translated roll;
other target responses and unrelated traversal states impose no condition. -/
theorem IsRollBound.of_traverse_of_exists (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j)
    (R : ∀ {i j}, S i j → B' → B → Prop)
    (h_can : ∀ {i j} (s : S i j) (a : P.A i) b' b, R s b' b → canRoll' j (f.op s a) b' →
      canRoll i a b)
    (h_next : ∀ {i j} (s : S i j) (a : P.A i) b' b, R s b' b →
      canRoll' j (f.op s a) b' → ∀ answer, ∃ y, f.arg s a y = answer ∧
        R (f.next s a y) (cost' j (f.op s a) b') (cost i a b))
    {i j} {s : S i j} {x : IFreeM P X i} {b' : B'} {b : B}
    (hx : (x.traverse f leaf s).IsRollBound b' canRoll' cost') (hR : R s b' b) :
    x.IsRollBound b canRoll cost := by
  induction x using IFreeM.inductionOn generalizing j b b' with
  | pure _ _ => trivial
  | liftBind i a next ih =>
      rw [traverse_liftBind, isRollBound_liftBind_iff] at hx
      refine ⟨h_can s a b' b hR hx.1, fun answer => ?_⟩
      obtain ⟨y, rfl, hy⟩ := h_next s a b' b hR hx.1 answer
      exact ih _ (hx.2 y) hy

/-- A traversal whose response maps are all surjective reflects a roll bound along a budget
relation `R` from target to source budgets, which may read the traversal state:
* `h_can` — at related budgets, an allowed translated roll comes from an allowed source roll;
* `h_cost` — after an allowed translated roll, the updated budgets are related at every next
  state.

Translated leaves impose no condition, since source leaves satisfy every bound. -/
theorem IsRollBound.of_traverse (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j)
    (hargs : ∀ {i j} (s : S i j) (a : P.A i), Function.Surjective (f.arg s a))
    (R : ∀ {i j}, S i j → B' → B → Prop)
    (h_can : ∀ {i j} (s : S i j) (a : P.A i) b' b, R s b' b → canRoll' j (f.op s a) b' →
      canRoll i a b)
    (h_cost : ∀ {i j} (s : S i j) (a : P.A i) b' b, R s b' b → canRoll' j (f.op s a) b' →
      ∀ y, R (f.next s a y) (cost' j (f.op s a) b') (cost i a b))
    {i j} {s : S i j} {x : IFreeM P X i} {b' : B'} {b : B}
    (hx : (x.traverse f leaf s).IsRollBound b' canRoll' cost') (hR : R s b' b) :
    x.IsRollBound b canRoll cost := by
  apply IsRollBound.of_traverse_of_exists f leaf R h_can ?_ hx hR
  intro i j s a b' b hR hcan answer
  obtain ⟨y, hy⟩ := hargs s a answer
  exact ⟨y, hy, h_cost s a b' b hR hcan y⟩

/-! ## Charge bounds -/

variable {c : (i : I) → P.A i → ℕ} {c' : (j : J) → Q.A j → ℕ}

/-- Translated constructors that cost at most their source constructors, at every traversal
state, and translated leaves bounded by `m` give the traversed tree the source budget plus
`m`. Pure translated leaves have `m = 0`. -/
theorem IsChargeBound.traverse (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j)
    {m : ℕ} (hc : ∀ {i j} (s : S i j) (a : P.A i), c' j (f.op s a) ≤ c i a)
    (hleaf : ∀ {i j} (s : S i j) (x : X i), (leaf s x).IsChargeBound c' m)
    {i j} (s : S i j) {x : IFreeM P X i} {n : ℕ} (hx : x.IsChargeBound c n) :
    (x.traverse f leaf s).IsChargeBound c' (n + m) :=
  IsRollBound.traverse f leaf (fun _ n n' => n + m ≤ n')
    (fun s a _ _ hR hcan => (hc s a).trans (hcan.trans (by omega)))
    (fun s a _ _ hR hcan _ => by have := hc s a; omega)
    (fun s x _ _ hR => (hleaf s x).mono (by omega)) hx le_rfl

/-- A traversal whose response maps are all surjective reflects a charge bound when every
source constructor costs at most its translation, at every traversal state. -/
theorem IsChargeBound.of_traverse (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j)
    (hargs : ∀ {i j} (s : S i j) (a : P.A i), Function.Surjective (f.arg s a))
    (hc : ∀ {i j} (s : S i j) (a : P.A i), c i a ≤ c' j (f.op s a))
    {i j} {s : S i j} {x : IFreeM P X i} {n : ℕ}
    (hx : (x.traverse f leaf s).IsChargeBound c' n) : x.IsChargeBound c n :=
  IsRollBound.of_traverse f leaf hargs (fun _ n' n => n' ≤ n)
    (fun s a _ _ hR hcan => (hc s a).trans (hcan.trans hR))
    (fun s a _ _ hR hcan _ => by have := hc s a; omega) hx le_rfl

/-- With surjective response maps, charges preserved at every traversal state, and translated
leaves of zero cost, a traversal neither raises nor lowers the charge bound. -/
theorem isChargeBound_traverse_iff (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j)
    (hargs : ∀ {i j} (s : S i j) (a : P.A i), Function.Surjective (f.arg s a))
    (hc : ∀ {i j} (s : S i j) (a : P.A i), c' j (f.op s a) = c i a)
    (hleaf : ∀ {i j} (s : S i j) (x : X i), (leaf s x).IsChargeBound c' 0)
    {i j} (s : S i j) (x : IFreeM P X i) (n : ℕ) :
    (x.traverse f leaf s).IsChargeBound c' n ↔ x.IsChargeBound c n :=
  ⟨IsChargeBound.of_traverse f leaf hargs (fun s a => (hc s a).ge),
    IsChargeBound.traverse f leaf (fun s a => (hc s a).le) hleaf s⟩

end IPFunctor.IFreeM
