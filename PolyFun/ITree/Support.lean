/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support
public import PolyFun.ITree.Bisim.Bind

/-!
# Possible outputs of interaction trees

`ITree.CanReturn t r` holds when some finite run of `t` returns `r`. Such a run is a path through
silent steps, and through queries at any answers, that ends at the leaf `pure r`. A diverging run
returns nothing, so `ITree.diverge` has no possible output (`ITree.not_canReturn_diverge`).

`ITree.attach` refines every leaf with the proof that it is a possible output, by corecursion. With
it, interaction trees carry `MonadAttach` and `ExactMonadAttach` instances. So the support judgments
of `PolyFun.Control.Monad.Support` (`MonadAttach.AllOutputs`, `MonadAttach.SomeOutput`), and the
readings built on them, apply to interaction trees.

## Main definitions

* `ITree.CanReturn`: the possible outputs of a tree.
* `ITree.attach`: a tree whose leaves carry the proof that they are possible outputs.

## Main results

* `ITree.canReturn_pure_iff`, `ITree.canReturn_step_iff`, `ITree.canReturn_query_iff`,
  `ITree.not_canReturn_diverge` and `ITree.canReturn_bind_iff`: the possible outputs of each
  construction.
* `ITree.map_attach`: forgetting the proofs recovers the tree.
* `ITree.instExactMonadAttach`: interaction trees as an exact `MonadAttach`.
-/

@[expose] public section

universe uA uB uα uβ

namespace ITree

variable {F : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-- `CanReturn t r`: some finite run of `t` returns `r`. The run passes through silent steps and
through queries at any answers, and ends at the leaf `pure r`. The constructors are stated on
`shape'`, so that `cases` and `induction` apply to any tree. -/
inductive CanReturn : ITree F α → α → Prop where
  /-- A leaf returns its value. -/
  | pure {t : ITree F α} {r : α} {c : (ViewPoly F α).B (.pure r) → ITree F α}
      (h : shape' t = .mk (.pure r) c) : CanReturn t r
  /-- A silent step returns what its continuation returns. -/
  | step {t : ITree F α} {r : α} {c : PUnit.{uB + 1} → ITree F α}
      (h : shape' t = .mk .step c) (hr : CanReturn (c PUnit.unit) r) : CanReturn t r
  /-- A query returns what its continuation returns at some answer. -/
  | query {t : ITree F α} {r : α} {a : F.A} {c : F.B a → ITree F α}
      (h : shape' t = .mk (.query a) c) (b : F.B a) (hr : CanReturn (c b) r) : CanReturn t r

namespace CanReturn

theorem of_pure (r : α) : CanReturn (ITree.pure (F := F) r) r :=
  .pure (shape'_pure r)

theorem of_step {t : ITree F α} {r : α} (h : CanReturn t r) : CanReturn (ITree.step t) r :=
  .step (shape'_step t) h

theorem of_query {a : F.A} {k : F.B a → ITree F α} {r : α} (b : F.B a) (h : CanReturn (k b) r) :
    CanReturn (ITree.query a k) r :=
  .query (shape'_query a k) b h

end CanReturn

@[simp] theorem canReturn_pure_iff {r a : α} : CanReturn (pure (F := F) r) a ↔ a = r := by
  refine ⟨fun h => ?_, fun h => h ▸ .of_pure r⟩
  cases h with
  | pure h => rw [shape'_pure] at h; cases h; rfl
  | step h => rw [shape'_pure] at h; cases h
  | query h => rw [shape'_pure] at h; cases h

@[simp] theorem canReturn_step_iff {t : ITree F α} {r : α} :
    CanReturn (step t) r ↔ CanReturn t r := by
  refine ⟨fun h => ?_, .of_step⟩
  cases h with
  | pure h => rw [shape'_step] at h; cases h
  | step h hr => rw [shape'_step] at h; cases h; exact hr
  | query h => rw [shape'_step] at h; cases h

@[simp] theorem canReturn_query_iff {a : F.A} {k : F.B a → ITree F α} {r : α} :
    CanReturn (query a k) r ↔ ∃ b, CanReturn (k b) r := by
  refine ⟨fun h => ?_, fun ⟨b, hb⟩ => .of_query b hb⟩
  cases h with
  | pure h => rw [shape'_query] at h; cases h
  | step h => rw [shape'_query] at h; cases h
  | query h b hr => rw [shape'_query] at h; cases h; exact ⟨b, hr⟩

/-- Silent divergence returns nothing. -/
theorem not_canReturn_diverge (r : α) : ¬ CanReturn (diverge : ITree F α) r := by
  intro h
  generalize hd : (diverge : ITree F α) = t at h
  induction h with
  | pure h => subst hd; rw [shape'_diverge] at h; cases h
  | step h _ ih => subst hd; rw [shape'_diverge] at h; cases h; exact ih rfl
  | query h => subst hd; rw [shape'_diverge] at h; cases h

/-- The possible outputs of a sequence are the possible outputs of the continuation at the
possible outputs of the first part. -/
theorem canReturn_bind_iff {t : ITree F α} {k : α → ITree F β} {b : β} :
    CanReturn (bind t k) b ↔ ∃ a, CanReturn t a ∧ CanReturn (k a) b := by
  constructor
  · intro h
    generalize hu : bind t k = u at h
    induction h generalizing t with
    | pure h =>
      subst hu
      induction t using shape_cases with
      | pure a => exact ⟨a, .of_pure a, .pure (by rwa [bind_pure_left] at h)⟩
      | step t' => rw [bind_step, shape'_step] at h; cases h
      | query a' c => rw [bind_query, shape'_query] at h; cases h
    | step h hr ih =>
      subst hu
      induction t using shape_cases with
      | pure a => exact ⟨a, .of_pure a, .step (by rwa [bind_pure_left] at h) hr⟩
      | step t' =>
        rw [bind_step, shape'_step] at h
        cases h
        obtain ⟨a, ha, hk⟩ := ih rfl
        exact ⟨a, ha.of_step, hk⟩
      | query a' c => rw [bind_query, shape'_query] at h; cases h
    | query h b' hr ih =>
      subst hu
      induction t using shape_cases with
      | pure a => exact ⟨a, .of_pure a, .query (by rwa [bind_pure_left] at h) b' hr⟩
      | step t' => rw [bind_step, shape'_step] at h; cases h
      | query a' c =>
        rw [bind_query, shape'_query] at h
        cases h
        obtain ⟨a, ha, hk⟩ := ih rfl
        exact ⟨a, .of_query b' ha, hk⟩
  · rintro ⟨a, ha, hb⟩
    induction ha with
    | pure h => rw [eq_pure_of_dest h, bind_pure_left]; exact hb
    | step h _ ih => rw [eq_step_of_dest h, bind_step]; exact (ih hb).of_step
    | query h b' _ ih => rw [eq_query_of_dest h, bind_query]; exact .of_query b' (ih hb)

/-! ## Attaching the proofs -/

/-- One layer of `attach`. The seed is a subtree whose possible outputs are possible outputs of
`t`; its leaves become refined leaves, and its children become seeds. -/
def attachStep (t : ITree F α) (u : {u : ITree F α // ∀ r, CanReturn u r → CanReturn t r}) :
    (ViewPoly F {r // CanReturn t r}).Obj {u : ITree F α // ∀ r, CanReturn u r → CanReturn t r} :=
  match h : shape' u.1 with
  | ⟨.pure r, _⟩ => ⟨.pure ⟨r, u.2 r (.pure h)⟩, PEmpty.elim⟩
  | ⟨.step, c⟩ => ⟨.step, fun _ => ⟨c PUnit.unit, fun r hr => u.2 r (.step h hr)⟩⟩
  | ⟨.query a, c⟩ => ⟨.query a, fun b => ⟨c b, fun r hr => u.2 r (.query h b hr)⟩⟩

/-- Refine every leaf of `t` with the proof that it is a possible output of `t`. -/
def attach (t : ITree F α) : ITree F {r // CanReturn t r} :=
  corec (attachStep t) ⟨t, fun _ h => h⟩

section AttachStep

variable {t : ITree F α} {u : ITree F α} {hu : ∀ r, CanReturn u r → CanReturn t r}

private theorem corec_attachStep_of_pure {r : α} {c : (ViewPoly F α).B (.pure r) → ITree F α}
    (h : shape' u = .mk (.pure r) c) :
    corec (attachStep t) ⟨u, hu⟩ = pure ⟨r, hu r (.pure h)⟩ := by
  apply eq_of_shape'_eq
  rw [shape'_corec_apply, shape'_pure]
  unfold attachStep
  split <;> rename_i heq <;> rw [h] at heq <;> cases heq
  exact PFunctor.Obj.ext rfl (heq_of_eq (funext fun d => d.elim))

private theorem corec_attachStep_of_step {c : PUnit.{uB + 1} → ITree F α}
    (h : shape' u = .mk .step c) :
    corec (attachStep t) ⟨u, hu⟩ =
      step (corec (attachStep t) ⟨c PUnit.unit, fun r hr => hu r (.step h hr)⟩) := by
  apply eq_of_shape'_eq
  rw [shape'_corec_apply, shape'_step]
  unfold attachStep
  split <;> rename_i heq <;> rw [h] at heq <;> cases heq
  rfl

private theorem corec_attachStep_of_query {a : F.A} {c : F.B a → ITree F α}
    (h : shape' u = .mk (.query a) c) :
    corec (attachStep t) ⟨u, hu⟩ =
      query a fun b => corec (attachStep t) ⟨c b, fun r hr => hu r (.query h b hr)⟩ := by
  apply eq_of_shape'_eq
  rw [shape'_corec_apply, shape'_query]
  unfold attachStep
  split <;> rename_i heq <;> rw [h] at heq <;> cases heq
  rfl

end AttachStep

/-- Forgetting the proofs recovers the tree. -/
theorem map_attach (t : ITree F α) : Subtype.val <$> attach t = t := by
  rw [← bind_pure_comp]
  change bind (attach t) (fun s => pure s.val) = t
  suffices h : ∀ u, bind (corec (attachStep t) u) (fun s => pure s.val) = u.1 from
    h ⟨t, fun _ h => h⟩
  intro u
  refine bisim (fun x y => x = y ∨
      ∃ u, x = bind (corec (attachStep t) u) (fun s => pure s.val) ∧ y = u.1) ?_ _ _
    (.inr ⟨u, rfl, rfl⟩)
  rintro x y (rfl | ⟨u, rfl, rfl⟩)
  · exact ⟨_, _, _, rfl, rfl, fun _ => .inl rfl⟩
  · obtain ⟨u, hu⟩ := u
    rcases h : shape' u with ⟨r | _ | a, c⟩
    · rw [corec_attachStep_of_pure h, bind_pure_left]
      exact ⟨.pure r, PEmpty.elim, c, shape'_pure r, rfl, fun d => d.elim⟩
    · rw [corec_attachStep_of_step h, bind_step]
      exact ⟨.step, _, c, shape'_step _, rfl, fun _ => .inr ⟨_, rfl, rfl⟩⟩
    · rw [corec_attachStep_of_query h, bind_query]
      exact ⟨.query a, _, c, shape'_query _ _, rfl, fun _ => .inr ⟨_, rfl, rfl⟩⟩

/-- Interaction trees attach their possible outputs: `MonadAttach.CanReturn` is
`ITree.CanReturn`. -/
instance instMonadAttach : MonadAttach (ITree F) where
  CanReturn := CanReturn
  attach := attach

theorem canReturn_eq : (MonadAttach.CanReturn : ITree F α → α → Prop) = CanReturn :=
  rfl

/-- Possible outputs compose exactly along `pure` and `bind`. -/
instance instExactMonadAttach : ExactMonadAttach (ITree F) where
  map_attach := map_attach _
  canReturn_map_imp {_ P x a} h := by
    change CanReturn (Subtype.val <$> x) a at h
    rw [← bind_pure_comp] at h
    obtain ⟨s, _, hs⟩ := canReturn_bind_iff.mp h
    rw [canReturn_pure_iff.mp hs]
    exact s.2
  canReturn_pure a := CanReturn.of_pure a
  canReturn_bind ha hb := canReturn_bind_iff.mpr ⟨_, ha, hb⟩

end ITree
