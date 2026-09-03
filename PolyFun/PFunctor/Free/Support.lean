/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support.Instances
public import PolyFun.PFunctor.Free.Path

/-!
# Exact Support of the Free Monad

The free monad `FreeM P` carries a canonical `MonadAttach` instance: the possible outputs of
a program are the leaf payloads reachable by choosing *some* direction at every operation
node,

* `supp (pure x) = {x}`,
* `supp (liftBind a r) = ⋃ b, supp (r b)`,

and `attach` decorates each leaf with its reachability proof by structural recursion. Both
are computable and axiom-free, so `MonadAttach.pbind` is available for well-founded
recursion over free programs.

The instance is `ExactMonadAttach`: `supp` really is the strongest postcondition, proved by
induction rather than assumed. Consequently `MonadAttach.support` on `FreeM P` reduces
definitionally — `support (pure x) = {x}` and `support (liftBind a r) = ⋃ b, support (r b)`
are both `rfl` — and the judgments `AllOutputs`/`SomeOutput`/`NoOutput` recurse structurally
over trees.

Two coherence results connect this to the rest of the library:
`support_eq_range_output` identifies the support with the range of `FreeM.output` over the
canonical `FreeM.Path` type, and `support_eq_liftM_univ` identifies it with the fold of the
"every response possible" handler into the powerset monad.
-/

@[expose] public section

universe uA uB v

namespace PFunctor.FreeM

open MonadAttach

variable {P : PFunctor.{uA, uB}} {α β : Type v}

/-- The structural support of a free tree: every direction of every operation node is
possible. -/
def supp : FreeM P α → Set α
  | .pure a => {a}
  | .liftBind _ r => ⋃ b, supp (r b)

/-- Reachability at a child is reachability at the node. -/
theorem mem_supp_liftBind_of_mem {op : P.A} {r : P.B op → FreeM P α} {b : P.B op} {a : α}
    (h : a ∈ supp (r b)) : a ∈ supp (FreeM.liftBind op r) :=
  Set.mem_iUnion.mpr ⟨b, h⟩

/-- Attach the structural-support proof to every leaf, by structural recursion. -/
def attachSupp : (x : FreeM P α) → FreeM P {a : α // a ∈ supp x}
  | .pure a => .pure ⟨a, rfl⟩
  | .liftBind op r => .liftBind op fun b =>
      FreeM.map (fun z => ⟨z.1, mem_supp_liftBind_of_mem z.2⟩) (attachSupp (r b))

instance instMonadAttach : MonadAttach (FreeM P) where
  CanReturn x a := a ∈ supp x
  attach := attachSupp

/-- The structural support is the strongest postcondition: anything reachable in a tree of
refined values satisfies the refinement. -/
theorem supp_map {Q : α → Prop} (x : FreeM P {a : α // Q a}) {b : α} :
    b ∈ supp (Subtype.val <$> x) → Q b := by
  induction x with
  | pure a => intro h; cases h; exact a.2
  | lift_bind op r ih =>
      intro h
      change b ∈ supp (FreeM.liftBind op fun c => Subtype.val <$> r c) at h
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp h
      exact ih c hc

theorem map_attachSupp (x : FreeM P α) : Subtype.val <$> attachSupp x = x := by
  induction x with
  | pure a => rfl
  | lift_bind op r ih =>
      change FreeM.liftBind op (fun b => Subtype.val <$>
        (FreeM.map (fun z => ⟨z.1, mem_supp_liftBind_of_mem z.2⟩) (attachSupp (r b)))) = _
      congr 1
      funext b
      rw [show (Subtype.val <$> (FreeM.map
        (fun z : {a // a ∈ supp (r b)} =>
          (⟨z.1, mem_supp_liftBind_of_mem z.2⟩ :
            {a // a ∈ supp (FreeM.liftBind op r)}))
        (attachSupp (r b)))) = Subtype.val <$> attachSupp (r b) from
        (FreeM.comp_map _ _ _).symm]
      exact ih b

instance instExactMonadAttach : ExactMonadAttach (FreeM P) where
  map_attach := map_attachSupp _
  canReturn_map_imp h := supp_map _ h
  canReturn_pure _ := rfl
  canReturn_bind {_ _ x _ _ _} ha hb := by
    induction x with
    | pure c => cases ha; exact hb
    | lift_bind op r ih =>
        obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ha
        exact mem_supp_liftBind_of_mem (ih c hc)

/-! ## Structural equations

`MonadAttach.support` on `FreeM P` unfolds to `supp`, so the leaf and node equations hold by
`rfl`. -/

theorem support_eq_supp (x : FreeM P α) : support x = supp x := rfl

@[simp]
theorem support_pure' (a : α) : support (pure a : FreeM P α) = {a} := rfl

@[freeM_unfold]
theorem support_liftBind (a : P.A) (r : P.B a → FreeM P α) :
    support (FreeM.liftBind a r) = ⋃ b, support (r b) := rfl

@[simp]
theorem support_lift (a : P.A) :
    support (FreeM.lift (P := P) a) = Set.univ :=
  Set.eq_univ_of_forall fun c => Set.mem_iUnion.mpr ⟨c, rfl⟩

theorem mem_support_liftBind {a : P.A} {r : P.B a → FreeM P α} {c : α} :
    c ∈ support (FreeM.liftBind a r) ↔ ∃ b, c ∈ support (r b) :=
  Set.mem_iUnion

/-! ## Structural recursion for the satisfaction judgments -/

@[freeM_unfold]
theorem allOutputs_liftBind (p : α → Prop) (a : P.A) (r : P.B a → FreeM P α) :
    AllOutputs p (FreeM.liftBind a r) ↔ ∀ b, AllOutputs p (r b) := by
  constructor
  · intro h b c hc
    exact h c (mem_support_liftBind.mpr ⟨b, hc⟩)
  · intro h c hc
    obtain ⟨b, hb⟩ := mem_support_liftBind.mp hc
    exact h b c hb

@[freeM_unfold]
theorem someOutput_liftBind (p : α → Prop) (a : P.A) (r : P.B a → FreeM P α) :
    SomeOutput p (FreeM.liftBind a r) ↔ ∃ b, SomeOutput p (r b) := by
  constructor
  · rintro ⟨c, hc, hpc⟩
    obtain ⟨b, hb⟩ := mem_support_liftBind.mp hc
    exact ⟨b, c, hb, hpc⟩
  · rintro ⟨b, c, hc, hpc⟩
    exact ⟨c, mem_support_liftBind.mpr ⟨b, hc⟩, hpc⟩

@[simp]
theorem allOutputs_lift (a : P.A) (p : P.B a → Prop) :
    AllOutputs p (FreeM.lift (P := P) a) ↔ ∀ b, p b :=
  ⟨fun h b => h b (by rw [← mem_support, support_lift]; exact Set.mem_univ b), fun h c _ => h c⟩

@[simp]
theorem someOutput_lift (a : P.A) (p : P.B a → Prop) :
    SomeOutput p (FreeM.lift (P := P) a) ↔ ∃ b, p b :=
  ⟨fun ⟨c, _, hc⟩ => ⟨c, hc⟩,
    fun ⟨b, hb⟩ => ⟨b, by rw [← mem_support, support_lift]; exact Set.mem_univ b, hb⟩⟩

@[freeM_unfold]
theorem noOutput_liftBind (p : α → Prop) (a : P.A) (r : P.B a → FreeM P α) :
    NoOutput p (FreeM.liftBind a r) ↔ ∀ b, NoOutput p (r b) :=
  allOutputs_liftBind (fun a => ¬ p a) a r

/-! ## Coherence with paths and with the powerset fold -/

/-- The support is exactly the set of leaf payloads reachable along a canonical
root-to-leaf path. -/
theorem support_eq_range_output (s : FreeM P α) :
    support s = Set.range (FreeM.output s) := by
  induction s with
  | pure x =>
      ext c
      simp only [support_pure', Set.mem_singleton_iff, Set.mem_range]
      exact ⟨fun h => ⟨⟨⟩, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  | lift_bind a r ih =>
      change support (FreeM.liftBind a r) =
        Set.range (FreeM.output (FreeM.liftBind a r))
      rw [support_liftBind]
      ext c
      simp only [Set.mem_iUnion, Set.mem_range]
      constructor
      · rintro ⟨b, hb⟩
        rw [ih b, Set.mem_range] at hb
        obtain ⟨path, hpath⟩ := hb
        exact ⟨⟨b, path⟩, hpath⟩
      · rintro ⟨⟨b, path⟩, hpath⟩
        refine ⟨b, ?_⟩
        rw [ih b]
        exact ⟨path, hpath⟩

/-- The support is the powerset-monad interpretation of the "every response possible"
handler — the shape a support-as-fold presentation expects. -/
theorem support_eq_liftM_univ {γ : Type uB} (x : FreeM P γ) :
    support x = SetM.run (x.liftM (fun _ => (Set.univ : SetM _))) := by
  induction x with
  | pure a => rfl
  | lift_bind op r ih =>
      change (⋃ b, supp (r b)) = SetM.run (_ >>= _)
      change _ = ⋃ b ∈ (Set.univ : Set (P.B op)), SetM.run ((r b).liftM _)
      simp only [Set.mem_univ, Set.iUnion_true]
      exact iSup_congr ih

/-- Every possible output is witnessed by a path, and conversely. -/
theorem allOutputs_iff_forall_path (p : α → Prop) (s : FreeM P α) :
    AllOutputs p s ↔ ∀ path : FreeM.Path s, p (FreeM.output s path) := by
  rw [allOutputs_iff_forall_support, support_eq_range_output]
  simp

/-- Some possible output is witnessed by a path, and conversely. -/
theorem someOutput_iff_exists_path (p : α → Prop) (s : FreeM P α) :
    SomeOutput p s ↔ ∃ path : FreeM.Path s, p (FreeM.output s path) := by
  rw [someOutput_iff_exists_support, support_eq_range_output]
  simp

end PFunctor.FreeM
