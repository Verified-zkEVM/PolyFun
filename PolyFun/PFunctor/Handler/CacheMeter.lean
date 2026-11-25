/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import Mathlib.Data.List.Sigma
public import PolyFun.PFunctor.Handler.Charge
public import PolyFun.PFunctor.Handler.Stateful

/-!
# Where a meter sits relative to a cache

`Handler.cache` is the memoizing handler of an interface `P`: its state is a cache, a list of
answered calls `⟨a, b⟩`. A call recorded in the cache is answered from it without a call, and a new
call is forwarded once to `P` and its answer recorded. Running a client `x` through it from a cache
`c` gives a program `Handler.cache.run x c` over `P` whose calls are the forwarded ones.

A meter placed outside the cache charges the client's calls; a meter placed inside charges only
the forwarded calls, which are the paths' calls of `Handler.cache.run x c`. On every completed path
of the cached run, read together with a completed path `p` of the client with the same output:

* the outside meter `Handler.withCharge d` reads the client's charge `Path.charge d x p`: the meter
  transfers exactly;
* the inside charge is `TraceList.freshCharge e K (Path.trace x p)`, the charge of the distinct
  calls of `p` outside the keys `K` of the initial cache, each charged once;
* the final cache keys are the initial keys together with the calls of `p`, so the number of
  forwarded calls is the growth of the cache.

## Main definitions

* `Handler.cache` — the memoizing handler, a stateful handler into `FreeM P` over its cache.

## Main results

* `Handler.cache.exists_path_run` — the inside law: the charge of a path of the cached run is the
  fresh charge of a client path with the same output, and the final keys are the initial keys
  together with that path's calls;
* `Handler.cache.length_run_add_card` — the number of forwarded calls is the growth of the cache;
* `Handler.cache.exists_path_run_withCharge` — both placements on one run: on each path of the
  cached run with an outside meter, the meter reads the client's charge and the forwarded calls
  are charged the fresh charge of the same client path.
-/

@[expose] public section

universe u w

namespace PFunctor

namespace Handler

variable {P : PFunctor.{u, u}} [DecidableEq P.A]

/-- The memoizing handler: a call at `a` recorded in the cache is answered from it, and a new call
is forwarded once to `P` and its answer recorded. -/
@[simps -isSimp]
def cache : Stateful (FreeM P) (List (Σ a, P.B a)) P where
  toFun a := StateT.mk fun c =>
    match c.dlookup a with
    | some b => pure (b, c)
    | none => FreeM.liftBind a fun b => pure (b, ⟨a, b⟩ :: c)

namespace cache

/-- A recorded call is answered from the cache without a call. -/
theorem run_apply_of_dlookup_eq_some {a : P.A} {c : List (Σ a, P.B a)} {b : P.B a}
    (h : c.dlookup a = some b) : (cache a).run c = pure (b, c) := by
  simp [cache_apply, StateT.run_mk, h]

/-- A new call is forwarded once and its answer recorded. -/
theorem run_apply_of_dlookup_eq_none {a : P.A} {c : List (Σ a, P.B a)}
    (h : c.dlookup a = none) :
    (cache a).run c = FreeM.liftBind a fun b => pure (b, ⟨a, b⟩ :: c) := by
  simp [cache_apply, StateT.run_mk, h]

/-- A call recorded in the cache is charged nothing by a fresh charge relative to the keys. -/
theorem freshCharge_cons_of_mem {ω : Type w} [AddCommMonoid ω] (e : P.A → ω)
    {K : Finset P.A} (i : P.Idx) (ha : i.1 ∈ K) (t : TraceList P) :
    TraceList.freshCharge e K (FreeMonoid.of i * t) =
      TraceList.freshCharge e K t := by
  unfold TraceList.freshCharge
  rw [TraceList.positions_cons, List.toFinset_cons, Finset.insert_sdiff_of_mem _ ha]

/-- A call outside the keys is charged once, and is known for the rest of the trace. -/
theorem freshCharge_cons_of_not_mem {ω : Type w} [AddCommMonoid ω] (e : P.A → ω)
    {K : Finset P.A} (i : P.Idx) (ha : i.1 ∉ K) (t : TraceList P) :
    TraceList.freshCharge e K (FreeMonoid.of i * t) =
      e i.1 + TraceList.freshCharge e (insert i.1 K) t := by
  unfold TraceList.freshCharge
  rw [TraceList.positions_cons, List.toFinset_cons, Finset.insert_sdiff_of_notMem _ ha,
    Finset.sdiff_insert, ← Finset.erase_insert_eq_erase,
    Finset.add_sum_erase _ _ (Finset.mem_insert_self _ _)]

variable {α : Type u}

/-- **The inside law.** Every completed path `q` of the cached run of `x` from the cache `c` comes
from a completed path `p` of `x` with the same output; the charge `e` of the forwarded calls along
`q` is the fresh charge of `p` outside the keys of `c`, and the final cache keys are the keys of
`c` together with the calls of `p`. -/
theorem exists_path_run {ω : Type w} [AddCommMonoid ω] (e : P.A → ω) (x : FreeM P α)
    (c : List (Σ a, P.B a)) (q : FreeM.Path (cache.run x c)) :
    ∃ p : FreeM.Path x, (FreeM.output _ q).1 = FreeM.output x p ∧
      FreeM.Path.charge e _ q =
        TraceList.freshCharge e c.keys.toFinset (FreeM.Path.trace x p) ∧
      (FreeM.output _ q).2.keys.toFinset =
        c.keys.toFinset ∪ (FreeM.Path.positions x p).toFinset := by
  revert q
  induction x using FreeM.rec generalizing c with
  | pure v =>
    intro q
    refine ⟨⟨⟩, rfl, ?_, ?_⟩
    · change (0 : ω) = TraceList.freshCharge e c.keys.toFinset 1
      simp [TraceList.freshCharge, TraceList.positions_one]
    · change c.keys.toFinset = c.keys.toFinset ∪ ([] : List P.A).toFinset
      simp
  | liftBind a r ih =>
    rw [Stateful.run_liftBind]
    cases hc : c.dlookup a with
    | some b =>
      rw [run_apply_of_dlookup_eq_some hc, pure_bind]
      intro q
      obtain ⟨p, h1, h2, h3⟩ := ih b c q
      have ha : a ∈ c.keys.toFinset :=
        List.mem_toFinset.2 (List.dlookup_isSome.1 (by simp [hc]))
      refine ⟨⟨b, p⟩, h1, ?_, ?_⟩
      · rw [h2]
        exact (freshCharge_cons_of_mem e (⟨a, b⟩ : P.Idx) ha _).symm
      · rw [h3, FreeM.Path.positions_liftBind, List.toFinset_cons]
        grind
    | none =>
      rw [run_apply_of_dlookup_eq_none hc]
      rintro ⟨b, q⟩
      obtain ⟨p, h1, h2, h3⟩ := ih b (⟨a, b⟩ :: c) q
      have ha : a ∉ c.keys.toFinset := by
        simpa using List.dlookup_eq_none.1 hc
      refine ⟨⟨b, p⟩, h1, ?_, ?_⟩
      · change e a + FreeM.Path.charge e (cache.run (r b) (⟨a, b⟩ :: c)) q = _
        rw [h2, List.keys_cons, List.toFinset_cons]
        exact (freshCharge_cons_of_not_mem e (⟨a, b⟩ : P.Idx) ha _).symm
      · change (FreeM.output (cache.run (r b) (⟨a, b⟩ :: c)) q).2.keys.toFinset = _
        rw [h3, FreeM.Path.positions_liftBind, List.toFinset_cons, List.keys_cons,
          List.toFinset_cons]
        grind

/-- **The forwarded calls are the growth of the cache.** Along every completed path of the cached
run, the number of forwarded calls added to the number of initial keys is the number of final
keys. -/
theorem length_run_add_card (x : FreeM P α) (c : List (Σ a, P.B a))
    (q : FreeM.Path (cache.run x c)) :
    c.keys.toFinset.card + FreeM.Path.length _ q = (FreeM.output _ q).2.keys.toFinset.card := by
  obtain ⟨p, -, h2, h3⟩ := exists_path_run (fun _ => (1 : ℕ)) x c q
  rw [FreeM.Path.length_eq_charge_one, h2, h3, ← Finset.union_sdiff_self_eq_union,
    Finset.card_union_of_disjoint Finset.disjoint_sdiff]
  simp [TraceList.freshCharge, FreeM.Path.positions]

/-- One step of the cached run under an outside meter: the meter adds the charge of the call, and
the cache answers it. -/
theorem run_run_liftM_withCharge_liftBind {ω₁ : Type u} [AddMonoid ω₁] (d : P.A → ω₁) (a : P.A)
    (r : P.B a → FreeM P α) (t : ω₁) (c : List (Σ a, P.B a)) :
    (((FreeM.liftBind a r).liftM (cache.withCharge d)).run t).run c =
      (cache a).run c >>= fun z =>
        (((r z.1).liftM (cache.withCharge d)).run (t + d a)).run z.2 := by
  change (((FreeM.lift a >>= r).liftM (cache.withCharge d)).run t).run c = _
  simp [StateT.run_bind, run_withCharge, bind_map_left]

/-- **Both placements on one run.** Run `x` through the cache with an outside meter `d`, from the
amount spent `t` and the cache `c`. Every completed path `q` comes from a completed path `p` of
`x` with the same output; the outside meter ends at `t` plus the client's charge `d` along `p`,
and the charge `e` of the forwarded calls along `q` is the fresh charge of `p` outside the keys of
`c`. -/
theorem exists_path_run_withCharge {ω₁ : Type u} [AddMonoid ω₁] {ω : Type w} [AddCommMonoid ω]
    (d : P.A → ω₁) (e : P.A → ω) (x : FreeM P α) (t : ω₁) (c : List (Σ a, P.B a))
    (q : FreeM.Path (((x.liftM (cache.withCharge d)).run t).run c)) :
    ∃ p : FreeM.Path x, (FreeM.output _ q).1.1 = FreeM.output x p ∧
      (FreeM.output _ q).1.2 = t + FreeM.Path.charge d x p ∧
      FreeM.Path.charge e _ q =
        TraceList.freshCharge e c.keys.toFinset (FreeM.Path.trace x p) := by
  revert q
  induction x using FreeM.rec generalizing t c with
  | pure v =>
    intro q
    refine ⟨⟨⟩, rfl, (add_zero t).symm, ?_⟩
    change (0 : ω) = TraceList.freshCharge e c.keys.toFinset 1
    simp [TraceList.freshCharge, TraceList.positions_one]
  | liftBind a r ih =>
    rw [run_run_liftM_withCharge_liftBind]
    cases hc : c.dlookup a with
    | some b =>
      rw [run_apply_of_dlookup_eq_some hc, pure_bind]
      intro q
      obtain ⟨p, h1, h2, h3⟩ := ih b (t + d a) c q
      have ha : a ∈ c.keys.toFinset :=
        List.mem_toFinset.2 (List.dlookup_isSome.1 (by simp [hc]))
      refine ⟨⟨b, p⟩, h1, ?_, ?_⟩
      · rw [h2, add_assoc]
        rfl
      · rw [h3]
        exact (freshCharge_cons_of_mem e (⟨a, b⟩ : P.Idx) ha _).symm
    | none =>
      rw [run_apply_of_dlookup_eq_none hc]
      rintro ⟨b, q⟩
      obtain ⟨p, h1, h2, h3⟩ := ih b (t + d a) (⟨a, b⟩ :: c) q
      have ha : a ∉ c.keys.toFinset := by
        simpa using List.dlookup_eq_none.1 hc
      refine ⟨⟨b, p⟩, h1, ?_, ?_⟩
      · change (FreeM.output
          ((((r b).liftM (cache.withCharge d)).run (t + d a)).run (⟨a, b⟩ :: c)) q).1.2 = _
        rw [h2, add_assoc]
        rfl
      · change e a + FreeM.Path.charge e
          ((((r b).liftM (cache.withCharge d)).run (t + d a)).run (⟨a, b⟩ :: c)) q = _
        rw [h3, List.keys_cons, List.toFinset_cons]
        exact (freshCharge_cons_of_not_mem e (⟨a, b⟩ : P.Idx) ha _).symm

end cache

end Handler

end PFunctor
