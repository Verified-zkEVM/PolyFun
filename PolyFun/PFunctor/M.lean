/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.PFunctor.Univariate.M
public import PolyFun.PFunctor.Obj

/-! # Auxiliary lemmas for `PFunctor.M`

Small extensions to `Mathlib.Data.PFunctor.Univariate.M` used by the
`PolyFun.ITree` port of the Coq `InteractionTrees` library.

The Mathlib file already supplies `M.mk`, `M.dest`, `M.corec`, `M.dest_mk`,
`M.mk_dest`, `M.dest_corec`, `M.corec_unique`, and the bisimulation principle
`M.bisim`. We add a few rewriting helpers that come up repeatedly when
defining and reasoning about ITrees:

* `M.dest_inj` / `M.eq_of_dest_eq` — `M.dest` is injective on `M P` (since
  it has a left inverse `M.mk`).
* `M.dest_corec_apply` — `M.dest_corec` through the polynomial-object constructor.
* `M.dest_corec_eq` — reformulation of `M.dest_corec` that lets `simp` see the
  result as an explicit polynomial object.
* `M.corec_eq_corec` — bisimulation principle for two `corec`s, the workhorse
  for `bind`/`iter` rewriting.
* `M.corec_dest` — `M.corec dest = id`. The corecursive identity.
-/

@[expose] public section

universe u uA uB v w

namespace PFunctor

namespace M

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-! ### Injectivity of `dest` -/

/-- `M.dest` is injective: equal destructions imply equal `M`-values, since
`M.mk` is a left inverse of `M.dest` (see `M.mk_dest`). -/
theorem eq_of_dest_eq {u v : M P} (h : M.dest u = M.dest v) : u = v := by
  rw [← M.mk_dest u, ← M.mk_dest v, h]

@[simp] theorem dest_inj {u v : M P} : M.dest u = M.dest v ↔ u = v :=
  ⟨eq_of_dest_eq, fun h => h ▸ rfl⟩

/-! ### Corec helpers -/

/-- The shape and children of a corecursive polynomial tree. -/
theorem dest_corec_apply (g : α → P α) (x : α) :
    M.dest (M.corec g x) = .mk ((g x).fst) (fun b => M.corec g ((g x).snd b)) := by
  rw [M.dest_corec]
  rfl

/-- Pointwise version of `dest_corec_apply` with an explicit shape and child family,
convenient when the right-hand side of a `corec` step is already known
explicitly. -/
theorem dest_corec_eq {a : P.A} {h : P.B a → α} (g : α → P α) (x : α) (heq : g x = .mk a h) :
    M.dest (M.corec g x) = .mk a (fun b => M.corec g (h b)) := by
  rw [dest_corec_apply, heq]
  rfl

/-- Bisimulation principle specialized to two `corec`s built from the same
shape transformer. If at every reachable state the two seed transitions agree
on shapes and yield bisimilar children, the two `corec`s are equal. -/
theorem corec_eq_corec {α : Type v} {β : Type w} (g : α → P α) (h : β → P β)
    (R : α → β → Prop) (x₀ : α) (y₀ : β)
    (hR : R x₀ y₀)
    (step : ∀ x y, R x y → ∃ a f f',
      g x = .mk a f ∧ h y = .mk a (f') ∧ ∀ i, R (f i) (f' i)) :
    M.corec g x₀ = M.corec h y₀ := by
  let S : M P → M P → Prop :=
    fun u v => ∃ x y, R x y ∧ u = M.corec g x ∧ v = M.corec h y
  refine M.bisim S ?_ _ _ ⟨x₀, y₀, hR, rfl, rfl⟩
  rintro u v ⟨x, y, hxy, rfl, rfl⟩
  obtain ⟨a, f, f', hf, hf', hR'⟩ := step x y hxy
  refine ⟨a, M.corec g ∘ f, M.corec h ∘ f', ?_, ?_, ?_⟩
  · rw [dest_corec, hf]; rfl
  · rw [dest_corec, hf']; rfl
  · intro i; exact ⟨f i, f' i, hR' i, rfl, rfl⟩

/-- `M.corec dest = id`. The corecursive identity. Together with
`M.corec_unique` it characterises `corec` as the unique solution to
`dest ∘ f = map f ∘ g`. -/
theorem corec_dest (u : M P) : M.corec M.dest u = u := by
  refine M.bisim (fun a b => a = M.corec M.dest b) ?_ _ _ rfl
  rintro a b rfl
  refine ⟨(M.dest b).fst, (fun i => M.corec M.dest ((M.dest b).snd i)),
    (M.dest b).snd, ?_, ?_, ?_⟩
  · rw [dest_corec_apply]
  · rfl
  · intro i; rfl

end M

end PFunctor
