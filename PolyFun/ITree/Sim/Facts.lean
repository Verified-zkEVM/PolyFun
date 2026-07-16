/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Sim.Defs
public import PolyFun.ITree.Bisim.Bind

/-! # Naturality lemmas for `ITree.simulate` and `ITree.mapSpec`

The standard equational theory for the simulation operators:

* `simulate_pure`, `simulate_step`, `simulate_query` — one-step unfoldings
  recording the action of `simulate` on each `Shape` constructor.
* `simulate_weakBisimRel` — relational weak bisimulation is a congruence for
  interpretation through a common handler.
* `simulate_bind` — `simulate` distributes over `bind`.
* `simulate_id` — interpreting via the trivial handler is (weakly) the
  identity.
* `Handler.id_comp_apply`, `Handler.comp_id_apply` — the trivial handler is
  a pointwise weak identity for handler composition.
* `simulate_comp`, `Handler.comp_assoc_apply` — sequential interpretation
  agrees with composite interpretation and handler composition is pointwise
  associative, both up to weak bisimulation.
* `mapSpec_pure`, `mapSpec_step`, `mapSpec_query` — one-step unfoldings of
  `mapSpec`.
* `mapSpec_id`, `mapSpec_comp` — functoriality of `mapSpec` over the lens
  category on `PFunctor`.
* `mapSpec_bind`, `mapSpec_iter` — `mapSpec` is a monad morphism (it distributes
  over `bind` and `iter`). Both proofs are by **strong bisimulation**
  (`PFunctor.M.bisim`), in contrast to `simulate_bind` which only holds up to
  weak bisim because `simulate` inserts τ-steps. The `iter` case is factored
  through four small `dest_corec_iterStep_*` helpers that compute one M-dest
  step of `M.corec (iterStep body)` in each of the four cases for the head of
  the input ITree.
* `simulate_ofLens` — relating `simulate` and `mapSpec` on a renaming.
* `Handler.ofLens_comp_apply` — pure-renaming handler composition agrees
  pointwise with lens composition.

Each proof is built by coinduction on the shared `ITree` shape and combines
one-step `M.corec` unfoldings with the bisimulation laws of
`PolyFun.ITree.Bisim.Bind` (notably `bind_weakBisim_cont` and the bind
unfoldings), so the resulting equations hold up to weak bisimulation.

The Handler/Sim layer and its weak simulation laws are fully
universe-polymorphic: event-position, event-answer, and result universes are
independent. In particular, `simulate_weakBisimRel` permits two independent
result types, while the composition laws span three or four independently
universe-polymorphic signatures. The strong equations retain the same
universe separation as the definitions.
-/

@[expose] public section

universe u uEA uEB uFA uFB uGA uGB uHA uHB uα uβ uγ

namespace ITree

/-! ### One-step unfoldings of `simulate` -/

/-- Step transformer used internally by `simulate`. -/
private def simulateStep {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    {α : Type uα} (h : Handler E F) :
    ITree E α → ITree F (ITree E α ⊕ α) := fun t =>
  match shape' t with
  | ⟨.pure r, _⟩ => pure (.inr r)
  | ⟨.step, c⟩ => pure (.inl (c PUnit.unit))
  | ⟨.query a, c⟩ => bind (h a) (fun b => pure (.inl (c b)))

private theorem simulate_eq_iter {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (h : Handler E F) (t : ITree E α) :
    simulate h t = iter (simulateStep h) t := rfl

private theorem simulateStep_pure {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (h : Handler E F) (r : α) :
    simulateStep h (pure (F := E) r) = (pure (.inr r) : ITree F (ITree E α ⊕ α)) := by
  change (match shape' (pure (F := E) r) with
      | ⟨.pure r, _⟩ => (pure (.inr r) : ITree F (ITree E α ⊕ α))
      | ⟨.step, c⟩ => pure (.inl (c PUnit.unit))
      | ⟨.query a, c⟩ => bind (h a) (fun b => pure (.inl (c b)))) = pure (.inr r)
  rw [shape'_pure]

theorem simulate_pure {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    {α : Type uα} (h : Handler E F) (r : α) :
    simulate h (pure (F := E) r) = pure r := by
  apply PFunctor.M.eq_of_dest_eq
  rw [simulate_eq_iter, iter, PFunctor.M.dest_corec_eq _ _
      (show iterStep (simulateStep h) (simulateStep h (pure r)) =
            ⟨.pure r, PEmpty.elim⟩ by
        rw [simulateStep_pure]
        change (match PFunctor.M.dest (pure (.inr r) : ITree F (ITree E α ⊕ α)) with
          | ⟨.pure (.inl j), _⟩ => (⟨.step, fun _ => simulateStep h j⟩ :
              (Poly F α).Obj (ITree F (ITree E α ⊕ α)))
          | ⟨.pure (.inr r), _⟩ => ⟨.pure r, PEmpty.elim⟩
          | ⟨.step, c⟩ => ⟨.step, fun u => c u⟩
          | ⟨.query a, c⟩ => ⟨.query a, fun b => c b⟩) = ⟨.pure r, PEmpty.elim⟩
        rw [show PFunctor.M.dest (pure (.inr r) : ITree F (ITree E α ⊕ α)) =
          ⟨.pure (.inr r), PEmpty.elim⟩ from shape'_pure _]),
      show PFunctor.M.dest (pure (F := F) r) = ⟨.pure r, PEmpty.elim⟩
        from shape'_pure r]
  congr 1
  funext b
  exact b.elim

private theorem simulateStep_step {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (h : Handler E F) (t : ITree E α) :
    simulateStep h (step t) = (pure (.inl t) : ITree F (ITree E α ⊕ α)) := by
  change (match shape' (step t) with
      | ⟨.pure r, _⟩ => (pure (.inr r) : ITree F (ITree E α ⊕ α))
      | ⟨.step, c⟩ => pure (.inl (c PUnit.unit))
      | ⟨.query a, c⟩ => bind (h a) (fun b => pure (.inl (c b)))) = pure (.inl t)
  rw [shape'_step]

private theorem simulateStep_query {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (h : Handler E F) (a : E.A)
    (k : E.B a → ITree E α) :
    simulateStep h (query a k) =
      (bind (h a) (fun b => pure (.inl (k b))) : ITree F (ITree E α ⊕ α)) := by
  change (match shape' (query a k) with
      | ⟨.pure r, _⟩ => (pure (.inr r) : ITree F (ITree E α ⊕ α))
      | ⟨.step, c⟩ => pure (.inl (c PUnit.unit))
      | ⟨.query a, c⟩ => bind (h a) (fun b => pure (.inl (c b)))) = _
  rw [shape'_query]

/-- One-step strong unfolding: `simulate` distributes over a leading silent
step. -/
theorem simulate_step_eq {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    {α : Type uα} (h : Handler E F) (t : ITree E α) :
    simulate h (step t) = step (simulate h t) := by
  apply PFunctor.M.eq_of_dest_eq
  rw [simulate_eq_iter, iter, PFunctor.M.dest_corec_eq _ _
      (show iterStep (simulateStep h) (simulateStep h (step t)) =
            ⟨.step, fun _ => simulateStep h t⟩ by
        rw [simulateStep_step]
        change (match PFunctor.M.dest (pure (.inl t) : ITree F (ITree E α ⊕ α)) with
          | ⟨.pure (.inl j), _⟩ => (⟨.step, fun _ => simulateStep h j⟩ :
              (Poly F α).Obj (ITree F (ITree E α ⊕ α)))
          | ⟨.pure (.inr r), _⟩ => ⟨.pure r, PEmpty.elim⟩
          | ⟨.step, c⟩ => ⟨.step, fun u => c u⟩
          | ⟨.query a, c⟩ => ⟨.query a, fun b => c b⟩) =
            ⟨.step, fun _ => simulateStep h t⟩
        rw [show PFunctor.M.dest (pure (.inl t) : ITree F (ITree E α ⊕ α)) =
          ⟨.pure (.inl t), PEmpty.elim⟩ from shape'_pure _])]
  change ⟨.step, fun _ => PFunctor.M.corec _ (simulateStep h t)⟩ =
    PFunctor.M.dest (step (simulate h t))
  rw [show PFunctor.M.dest (step (simulate h t)) = ⟨.step, fun _ => simulate h t⟩
      from shape'_step _]
  rfl

theorem simulate_step {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    {α : Type uα} (h : Handler E F) (t : ITree E α) :
    WeakBisim (simulate h (step t)) (simulate h t) := by
  rw [simulate_step_eq]
  exact step_weakBisim _

/-- Auxiliary strong equation: feeding a "pure-`.inl`"-wrapped `bind u` into
the `simulate` iteration collapses to `bind u` over the step-guarded
`simulate` of the continuations.

This is the coinductive core of `simulate_query_eq_bind`, generalised over
`u` so that the `PFunctor.M.bisim` is closed under continuation subtrees. -/
private theorem corec_iter_simulateStep_bind_pureInl
    {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    {α : Type uα} {γ : Type uγ}
    (h : Handler E F) (k : γ → ITree E α) (u : ITree F γ) :
    PFunctor.M.corec (iterStep (simulateStep h))
        (bind u (fun b : γ => (pure (.inl (k b)) : ITree F (ITree E α ⊕ α)))) =
      bind u (fun b => step (simulate h (k b))) := by
  refine PFunctor.M.bisim (fun (x y : ITree F α) => x = y ∨
    ∃ u : ITree F γ,
      x = PFunctor.M.corec (iterStep (simulateStep h))
            (bind u (fun b => (pure (.inl (k b)) : ITree F (ITree E α ⊕ α)))) ∧
      y = bind u (fun b => step (simulate h (k b))))
    ?_ _ _ (Or.inr ⟨u, rfl, rfl⟩)
  rintro x y (rfl | ⟨u, rfl, rfl⟩)
  · rcases hx : PFunctor.M.dest x with ⟨sh, c⟩
    exact ⟨sh, c, c, rfl, rfl, fun _ => Or.inl rfl⟩
  rcases hu : PFunctor.M.dest u with ⟨sh, c⟩
  cases sh with
  | pure r =>
      have hu_eq : u = pure r := by
        apply PFunctor.M.eq_of_dest_eq; rw [hu]
        change (⟨.pure r, c⟩ : (Poly F γ).Obj _) = ⟨.pure r, PEmpty.elim⟩
        congr 1; funext z; exact z.elim
      subst hu_eq
      rw [bind_pure_left, bind_pure_left]
      refine ⟨.step,
        fun _ => PFunctor.M.corec (iterStep (simulateStep h)) (simulateStep h (k r)),
        fun _ => simulate h (k r), ?_, ?_, fun _ => Or.inl rfl⟩
      · rw [PFunctor.M.dest_corec_apply, iterStep,
          show PFunctor.M.dest (pure (F := F) (.inl (k r) : ITree E α ⊕ α)) =
            ⟨.pure (.inl (k r)), PEmpty.elim⟩ from PFunctor.M.dest_mk _]
      · exact shape'_step _
  | step =>
      refine ⟨.step,
        fun _ => PFunctor.M.corec (iterStep (simulateStep h))
          (bind (c PUnit.unit)
            (fun b => (pure (.inl (k b)) : ITree F (ITree E α ⊕ α)))),
        fun _ => bind (c PUnit.unit) (fun b => step (simulate h (k b))),
        ?_, ?_, fun _ => Or.inr ⟨c PUnit.unit, rfl, rfl⟩⟩
      · rw [PFunctor.M.dest_corec_apply, iterStep,
          dest_bind_step (fun b : γ =>
            (pure (.inl (k b)) : ITree F (ITree E α ⊕ α))) u c hu]
      · exact dest_bind_step _ u c hu
  | query qa =>
      refine ⟨.query qa,
        fun b => PFunctor.M.corec (iterStep (simulateStep h))
          (bind (c b) (fun b' => (pure (.inl (k b')) : ITree F (ITree E α ⊕ α)))),
        fun b => bind (c b) (fun b' => step (simulate h (k b'))),
        ?_, ?_, fun b => Or.inr ⟨c b, rfl, rfl⟩⟩
      · rw [PFunctor.M.dest_corec_apply, iterStep,
          dest_bind_query (fun b : γ =>
            (pure (.inl (k b)) : ITree F (ITree E α ⊕ α))) u qa c hu]
      · exact dest_bind_query _ u qa c hu

/-- One-step strong unfolding of `simulate` on a query: running `simulate h`
through a `query a k` is the same as binding over `h a` and then resuming
`simulate h (k b)` after a productivity-forced silent step.

This is the strong-bisimulation version of `simulate_query` and the key
lemma for rewriting `simulate` on event-headed trees. -/
theorem simulate_query_eq_bind {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (h : Handler E F) (a : E.A) (k : E.B a → ITree E α) :
    simulate h (query a k) = bind (h a) (fun b => step (simulate h (k b))) := by
  change PFunctor.M.corec (iterStep (simulateStep h)) (simulateStep h (query a k)) = _
  rw [simulateStep_query]
  exact corec_iter_simulateStep_bind_pureInl h k (h a)

theorem simulate_query {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    {α : Type uα} (h : Handler E F) (a : E.A) (k : E.B a → ITree E α) :
    WeakBisim (simulate h (query a k))
      (bind (h a) (fun b => simulate h (k b))) := by
  rw [simulate_query_eq_bind]
  exact bind_weakBisim_cont (fun b => step_weakBisim _)

/-! ### Relational congruence of simulation -/

/-- Simulation preserves finite silent-step stripping. -/
theorem TauSteps.simulate {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα} {t t' : ITree E α}
    (ht : TauSteps t t') (h : Handler E F) :
    TauSteps (ITree.simulate h t) (ITree.simulate h t') := by
  induction ht with
  | refl _ => exact .refl _
  | @step t _ c ht _ ih =>
      have ht_eq : t = ITree.step (c PUnit.unit) := by
        apply PFunctor.M.eq_of_dest_eq
        change shape' t = shape' (ITree.step (c PUnit.unit))
        rw [ht, shape'_step]
      subst t
      rw [simulate_step_eq]
      exact TauSteps.step (fun _ => ITree.simulate h (c PUnit.unit))
        (shape'_step _) ih

/-- Interpreting both sides through the same handler preserves relational
weak bisimulation. The return relation and both return universes are
unchanged; the source and target event universes are independent. -/
theorem simulate_weakBisimRel {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα} {β : Type uβ}
    {RR : α → β → Prop} (h : Handler E F) {t : ITree E α} {s : ITree E β}
    (hts : WeakBisimRel RR t s) :
    WeakBisimRel RR (simulate h t) (simulate h s) := by
  refine WeakBisimRel.coinduct RR
    (fun x y =>
      (∃ t s, WeakBisimRel RR t s ∧ x = simulate h t ∧ y = simulate h s) ∨
      (∃ (γ : Type uEB) (u : ITree F γ)
          (k : γ → ITree E α) (k' : γ → ITree E β),
        (∀ b, WeakBisimRel RR (k b) (k' b)) ∧
        x = bind u (fun b => step (simulate h (k b))) ∧
        y = bind u (fun b => step (simulate h (k' b)))))
    ?_ (Or.inl ⟨t, s, hts, rfl, rfl⟩)
  rintro x y (⟨t, s, hts, rfl, rfl⟩ | ⟨γ, u, k, k', hkk', rfl, rfl⟩)
  · obtain ⟨t', s', ht, hs, M⟩ := hts.dest
    cases M with
    | pure r r' hrr ht' hs' =>
        have ht_eq : t' = pure r := by
          apply PFunctor.M.eq_of_dest_eq
          change shape' t' = shape' (pure r)
          exact ht'.trans (shape'_pure r).symm
        have hs_eq : s' = pure r' := by
          apply PFunctor.M.eq_of_dest_eq
          change shape' s' = shape' (pure r')
          exact hs'.trans (shape'_pure r').symm
        subst ht_eq
        subst hs_eq
        refine ⟨pure r, pure r', ?_, ?_,
          MatchRel.pure r r' hrr (shape'_pure r) (shape'_pure r')⟩
        · simpa only [simulate_pure] using ht.simulate h
        · simpa only [simulate_pure] using hs.simulate h
    | tau ct cs ht' hs' hcont =>
        have ht_eq : t' = step (ct PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq
          change shape' t' = shape' (step (ct PUnit.unit))
          rw [ht', shape'_step]
        have hs_eq : s' = step (cs PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq
          change shape' s' = shape' (step (cs PUnit.unit))
          rw [hs', shape'_step]
        subst ht_eq
        subst hs_eq
        refine ⟨step (simulate h (ct PUnit.unit)),
          step (simulate h (cs PUnit.unit)), ?_, ?_, ?_⟩
        · simpa only [simulate_step_eq] using ht.simulate h
        · simpa only [simulate_step_eq] using hs.simulate h
        · exact MatchRel.tau _ _ (shape'_step _) (shape'_step _)
            (Or.inl ⟨ct PUnit.unit, cs PUnit.unit, hcont, rfl, rfl⟩)
    | query a c c' ht' hs' hcont =>
        have ht_eq : t' = query a c := by
          apply PFunctor.M.eq_of_dest_eq
          change shape' t' = shape' (query a c)
          exact ht'.trans (shape'_query a c).symm
        have hs_eq : s' = query a c' := by
          apply PFunctor.M.eq_of_dest_eq
          change shape' s' = shape' (query a c')
          exact hs'.trans (shape'_query a c').symm
        subst ht_eq
        subst hs_eq
        have ht_sim := ht.simulate h
        have hs_sim := hs.simulate h
        rw [simulate_query_eq_bind] at ht_sim hs_sim
        rcases hu : PFunctor.M.dest (h a) with ⟨sh, cu⟩
        cases sh with
        | pure b =>
            have hu_eq : h a = pure b := by
              apply PFunctor.M.eq_of_dest_eq
              rw [hu]
              change (⟨.pure b, cu⟩ : (Poly F (E.B a)).Obj _) =
                ⟨.pure b, PEmpty.elim⟩
              congr 1
              funext z
              exact z.elim
            rw [hu_eq, bind_pure_left] at ht_sim hs_sim
            refine ⟨step (simulate h (c b)), step (simulate h (c' b)),
              ht_sim, hs_sim, ?_⟩
            exact MatchRel.tau _ _ (shape'_step _) (shape'_step _)
              (Or.inl ⟨c b, c' b, hcont b, rfl, rfl⟩)
        | step =>
            refine ⟨bind (h a) (fun b => step (simulate h (c b))),
              bind (h a) (fun b => step (simulate h (c' b))),
              ht_sim, hs_sim, ?_⟩
            exact MatchRel.tau _ _
              (dest_bind_step _ (h a) cu hu) (dest_bind_step _ (h a) cu hu)
              (Or.inr ⟨E.B a, cu PUnit.unit, c, c', hcont, rfl, rfl⟩)
        | query q =>
            refine ⟨bind (h a) (fun b => step (simulate h (c b))),
              bind (h a) (fun b => step (simulate h (c' b))),
              ht_sim, hs_sim, ?_⟩
            refine MatchRel.query q _ _ (dest_bind_query _ (h a) q cu hu)
              (dest_bind_query _ (h a) q cu hu) ?_
            intro b
            exact Or.inr ⟨E.B a, cu b, c, c', hcont, rfl, rfl⟩
  · rcases hu : PFunctor.M.dest u with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have hu_eq : u = pure r := by
          apply PFunctor.M.eq_of_dest_eq
          rw [hu]
          change (⟨.pure r, c⟩ : (Poly F γ).Obj _) =
            ⟨.pure r, PEmpty.elim⟩
          congr 1
          funext z
          exact z.elim
        subst hu_eq
        rw [bind_pure_left, bind_pure_left]
        refine ⟨step (simulate h (k r)), step (simulate h (k' r)),
          .refl _, .refl _, ?_⟩
        exact MatchRel.tau _ _ (shape'_step _) (shape'_step _)
          (Or.inl ⟨k r, k' r, hkk' r, rfl, rfl⟩)
    | step =>
        refine ⟨bind u (fun b => step (simulate h (k b))),
          bind u (fun b => step (simulate h (k' b))), .refl _, .refl _, ?_⟩
        exact MatchRel.tau _ _ (dest_bind_step _ u c hu) (dest_bind_step _ u c hu)
          (Or.inr ⟨γ, c PUnit.unit, k, k', hkk', rfl, rfl⟩)
    | query a =>
        refine ⟨bind u (fun b => step (simulate h (k b))),
          bind u (fun b => step (simulate h (k' b))), .refl _, .refl _, ?_⟩
        refine MatchRel.query a _ _ (dest_bind_query _ u a c hu)
          (dest_bind_query _ u a c hu) ?_
        intro b
        exact Or.inr ⟨γ, c b, k, k', hkk', rfl, rfl⟩

/-! ### `simulate` is monadic and identity-preserving -/

theorem simulate_id {E : PFunctor.{uEA, uEB}} {α : Type uα}
    (t : ITree E α) :
    WeakBisim (simulate (Handler.id E) t) t := by
  refine WeakBisim.coinduct
    (fun x y => x = simulate (Handler.id E) y ∨
      x = step (simulate (Handler.id E) y))
    ?_ (Or.inl rfl)
  rintro x y hxy
  have hxx' : TauSteps x (simulate (Handler.id E) y) := by
    rcases hxy with rfl | rfl
    · exact TauSteps.refl _
    · exact TauSteps.one _ (shape'_step _)
  rcases hy : PFunctor.M.dest y with ⟨sh, c⟩
  cases sh with
  | pure r =>
      have hy_eq : y = pure r := by
        apply PFunctor.M.eq_of_dest_eq; rw [hy]
        change (⟨.pure r, c⟩ : (Poly E α).Obj _) = ⟨.pure r, PEmpty.elim⟩
        congr 1; funext z; exact z.elim
      subst hy_eq
      rw [simulate_pure] at hxx'
      exact ⟨pure r, pure r, hxx', .refl _,
        Match.pure r (shape'_pure r) (shape'_pure r)⟩
  | step =>
      have hy_eq : y = step (c PUnit.unit) := by
        apply PFunctor.M.eq_of_dest_eq; rw [hy]; rfl
      subst hy_eq
      rw [simulate_step_eq] at hxx'
      refine ⟨step (simulate (Handler.id E) (c PUnit.unit)), step (c PUnit.unit),
        hxx', .refl _, ?_⟩
      exact Match.tau _ _ (shape'_step _) (shape'_step _) (Or.inl rfl)
  | query a =>
      have hy_eq : y = query a c := by
        apply PFunctor.M.eq_of_dest_eq; rw [hy]; rfl
      subst hy_eq
      rw [simulate_query_eq_bind,
          show (Handler.id E) a = query a pure from rfl,
          bind_query] at hxx'
      simp only [bind_pure_left] at hxx'
      refine ⟨query a (fun b => step (simulate (Handler.id E) (c b))),
        query a c, hxx', .refl _, ?_⟩
      refine Match.query a _ _ (shape'_query _ _) (shape'_query _ _) ?_
      intro b
      exact Or.inr rfl

/-! ### Handler-composition identities -/

/-- Postcomposing a handler with the trivial handler is pointwise weakly
equivalent to the original handler. -/
theorem Handler.id_comp_apply {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} (h : Handler E F) (a : E.A) :
    WeakBisim ((Handler.id F).comp h a) (h a) :=
  simulate_id (h a)

/-- Precomposing a handler with the trivial handler is pointwise weakly
equivalent to the original handler. -/
theorem Handler.comp_id_apply {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} (h : Handler E F) (a : E.A) :
    WeakBisim (h.comp (Handler.id E) a) (h a) := by
  change WeakBisim (simulate h (lift a)) (h a)
  simpa only [lift, simulate_pure, bind_pure_right] using
    (simulate_query h a (fun b => pure b))

/-- `simulate` distributes over `bind`, up to weak bisimilarity. The `step`
wrappers that appear after the coinductive unfolding are absorbed by the
weakness of `≈`.

The witness is a three-disjunct coinductive relation:
* the diagonal `x = y` for the pure-leaf alignment;
* the main "split at a top-level source tree `t`" disjunct;
* an auxiliary disjunct for traversing inside `h a`, the handler's output
  at a source-side `query a ...` node. This is what lets the coinductive
  step close when the source tree is query-headed and `simulate`'s
  productivity-forced silent step is emitted on the handler-output side. -/
theorem simulate_bind {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    {α : Type uα} {β : Type uβ}
    (h : Handler E F) (t : ITree E α) (k : α → ITree E β) :
    WeakBisim (simulate h (bind t k))
      (bind (simulate h t) (fun a => simulate h (k a))) := by
  refine WeakBisim.coinduct
    (fun (x y : ITree F β) => x = y ∨
      (∃ t : ITree E α,
        x = simulate h (bind t k) ∧
        y = bind (simulate h t) (fun a => simulate h (k a))) ∨
      (∃ (γ : Type uEB) (u : ITree F γ) (f : γ → ITree E α),
        x = bind u (fun b => step (simulate h (bind (f b) k))) ∧
        y = bind u (fun b => step
          (bind (simulate h (f b)) (fun a => simulate h (k a))))))
    ?_ (Or.inr (Or.inl ⟨t, rfl, rfl⟩))
  rintro a b (rfl | ⟨t, rfl, rfl⟩ | ⟨γ, u, f, rfl, rfl⟩)
  · -- Diagonal case.
    rcases ha : PFunctor.M.dest a with ⟨sh, c⟩
    refine ⟨a, a, .refl _, .refl _, ?_⟩
    cases sh with
    | pure r =>
        have e : shape' a = ⟨.pure r, PEmpty.elim⟩ := by
          change PFunctor.M.dest a = _
          rw [ha]; congr 1; funext z; exact z.elim
        exact Match.pure r e e
    | step => exact Match.tau c c ha ha (Or.inl rfl)
    | query a' => exact Match.query a' c c ha ha (fun _ => Or.inl rfl)
  · -- Main disjunct: split on `t`.
    rcases ht : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have ht_eq : t = pure r := by
          apply PFunctor.M.eq_of_dest_eq; rw [ht]
          change (⟨.pure r, c⟩ : (Poly E α).Obj _) = ⟨.pure r, PEmpty.elim⟩
          congr 1; funext z; exact z.elim
        subst ht_eq
        rw [bind_pure_left, simulate_pure, bind_pure_left]
        rcases hkr : PFunctor.M.dest (simulate h (k r)) with ⟨sh', c'⟩
        refine ⟨simulate h (k r), simulate h (k r), .refl _, .refl _, ?_⟩
        cases sh' with
        | pure r' =>
            have e : shape' (simulate h (k r)) = ⟨.pure r', PEmpty.elim⟩ := by
              change PFunctor.M.dest (simulate h (k r)) = _
              rw [hkr]; congr 1; funext z; exact z.elim
            exact Match.pure r' e e
        | step => exact Match.tau c' c' hkr hkr (Or.inl rfl)
        | query a' => exact Match.query a' c' c' hkr hkr (fun _ => Or.inl rfl)
    | step =>
        have ht_eq : t = step (c PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq; rw [ht]; rfl
        subst ht_eq
        rw [bind_step, simulate_step_eq, simulate_step_eq, bind_step]
        refine ⟨step (simulate h (bind (c PUnit.unit) k)),
          step (bind (simulate h (c PUnit.unit)) (fun a => simulate h (k a))),
          .refl _, .refl _, ?_⟩
        refine Match.tau _ _ (shape'_step _) (shape'_step _) ?_
        exact Or.inr (Or.inl ⟨c PUnit.unit, rfl, rfl⟩)
    | query a_E =>
        have ht_eq : t = query a_E c := by
          apply PFunctor.M.eq_of_dest_eq; rw [ht]; rfl
        subst ht_eq
        rw [bind_query, simulate_query_eq_bind, simulate_query_eq_bind,
            bind_assoc]
        simp only [bind_step]
        rcases hH : PFunctor.M.dest (h a_E) with ⟨sh', c'⟩
        cases sh' with
        | pure r =>
            have hH_eq : h a_E = pure r := by
              apply PFunctor.M.eq_of_dest_eq; rw [hH]
              change (⟨.pure r, c'⟩ : (Poly F (E.B a_E)).Obj _) =
                ⟨.pure r, PEmpty.elim⟩
              congr 1; funext z; exact z.elim
            rw [hH_eq, bind_pure_left, bind_pure_left]
            refine ⟨step (simulate h (bind (c r) k)),
              step (bind (simulate h (c r)) (fun a => simulate h (k a))),
              .refl _, .refl _, ?_⟩
            refine Match.tau _ _ (shape'_step _) (shape'_step _) ?_
            exact Or.inr (Or.inl ⟨c r, rfl, rfl⟩)
        | step =>
            have hH_eq : h a_E = step (c' PUnit.unit) := by
              apply PFunctor.M.eq_of_dest_eq; rw [hH]; rfl
            rw [hH_eq, bind_step, bind_step]
            refine ⟨step (bind (c' PUnit.unit)
                (fun b => step (simulate h (bind (c b) k)))),
              step (bind (c' PUnit.unit)
                (fun b => step
                  (bind (simulate h (c b)) (fun a => simulate h (k a))))),
              .refl _, .refl _, ?_⟩
            refine Match.tau _ _ (shape'_step _) (shape'_step _) ?_
            exact Or.inr (Or.inr ⟨E.B a_E, c' PUnit.unit, c, rfl, rfl⟩)
        | query a_F =>
            have hH_eq : h a_E = query a_F c' := by
              apply PFunctor.M.eq_of_dest_eq; rw [hH]; rfl
            rw [hH_eq, bind_query, bind_query]
            refine ⟨query a_F (fun b' => bind (c' b')
                (fun b => step (simulate h (bind (c b) k)))),
              query a_F (fun b' => bind (c' b')
                (fun b => step
                  (bind (simulate h (c b)) (fun a => simulate h (k a))))),
              .refl _, .refl _, ?_⟩
            refine Match.query a_F _ _ (shape'_query _ _) (shape'_query _ _) ?_
            intro b'
            exact Or.inr (Or.inr ⟨E.B a_E, c' b', c, rfl, rfl⟩)
  · -- Auxiliary disjunct: split on `u`.
    rcases hu : PFunctor.M.dest u with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have hu_eq : u = pure r := by
          apply PFunctor.M.eq_of_dest_eq; rw [hu]
          change (⟨.pure r, c⟩ : (Poly F γ).Obj _) = ⟨.pure r, PEmpty.elim⟩
          congr 1; funext z; exact z.elim
        subst hu_eq
        rw [bind_pure_left, bind_pure_left]
        refine ⟨step (simulate h (bind (f r) k)),
          step (bind (simulate h (f r)) (fun a => simulate h (k a))),
          .refl _, .refl _, ?_⟩
        refine Match.tau _ _ (shape'_step _) (shape'_step _) ?_
        exact Or.inr (Or.inl ⟨f r, rfl, rfl⟩)
    | step =>
        have hu_eq : u = step (c PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq; rw [hu]; rfl
        subst hu_eq
        rw [bind_step, bind_step]
        refine ⟨step (bind (c PUnit.unit)
            (fun b => step (simulate h (bind (f b) k)))),
          step (bind (c PUnit.unit)
            (fun b => step
              (bind (simulate h (f b)) (fun a => simulate h (k a))))),
          .refl _, .refl _, ?_⟩
        refine Match.tau _ _ (shape'_step _) (shape'_step _) ?_
        exact Or.inr (Or.inr ⟨γ, c PUnit.unit, f, rfl, rfl⟩)
    | query a_F =>
        have hu_eq : u = query a_F c := by
          apply PFunctor.M.eq_of_dest_eq; rw [hu]; rfl
        subst hu_eq
        rw [bind_query, bind_query]
        refine ⟨query a_F (fun b' => bind (c b')
            (fun b => step (simulate h (bind (f b) k)))),
          query a_F (fun b' => bind (c b')
            (fun b => step
              (bind (simulate h (f b)) (fun a => simulate h (k a))))),
          .refl _, .refl _, ?_⟩
        refine Match.query a_F _ _ (shape'_query _ _) (shape'_query _ _) ?_
        intro b'
        exact Or.inr (Or.inr ⟨γ, c b', f, rfl, rfl⟩)

/-! ### Composition of simulation -/

/-- Sequential simulation agrees with simulation through the composite
handler, up to weak bisimulation.

The proof uses three coinductive phases: source-tree traversal, traversal
inside the first handler's output, and traversal inside the second handler's
output. The latter two phases make the productivity-forced silent steps
explicit instead of relying on an unproved up-to-bind principle. -/
theorem simulate_comp {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    {G : PFunctor.{uGA, uGB}} {α : Type uα}
    (outer : Handler F G) (inner : Handler E F) (t : ITree E α) :
    WeakBisim (simulate outer (simulate inner t))
      (simulate (outer.comp inner) t) := by
  refine WeakBisim.coinduct
    (fun x y =>
      (∃ t : ITree E α,
        x = simulate outer (simulate inner t) ∧
        y = simulate (outer.comp inner) t) ∨
      (∃ (γ : Type uEB) (u : ITree F γ) (k : γ → ITree E α),
        x = simulate outer
          (bind u (fun b => step (simulate inner (k b)))) ∧
        y = bind (simulate outer u)
          (fun b => step (simulate (outer.comp inner) (k b)))) ∨
      (∃ (γ : Type uEB) (δ : Type uFB) (w : ITree G δ)
          (q : δ → ITree F γ) (k : γ → ITree E α),
        x = bind w (fun z => step (simulate outer
          (bind (q z) (fun b => step (simulate inner (k b)))))) ∧
        y = bind w (fun z => step
          (bind (simulate outer (q z))
            (fun b => step (simulate (outer.comp inner) (k b)))))))
    ?_ (Or.inl ⟨t, rfl, rfl⟩)
  rintro x y (⟨t, rfl, rfl⟩ | ⟨γ, u, k, rfl, rfl⟩ |
    ⟨γ, δ, w, q, k, rfl, rfl⟩)
  · rcases ht : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have ht_eq : t = pure r := by
          apply PFunctor.M.eq_of_dest_eq
          rw [ht]
          change (⟨.pure r, c⟩ : (Poly E α).Obj _) =
            ⟨.pure r, PEmpty.elim⟩
          congr 1
          funext z
          exact z.elim
        subst ht_eq
        rw [simulate_pure, simulate_pure, simulate_pure]
        exact ⟨pure r, pure r, .refl _, .refl _,
          Match.pure r (shape'_pure r) (shape'_pure r)⟩
    | step =>
        have ht_eq : t = step (c PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq
          rw [ht]
          rfl
        subst ht_eq
        rw [simulate_step_eq, simulate_step_eq, simulate_step_eq]
        refine ⟨step (simulate outer (simulate inner (c PUnit.unit))),
          step (simulate (outer.comp inner) (c PUnit.unit)),
          .refl _, .refl _, ?_⟩
        exact Match.tau _ _ (shape'_step _) (shape'_step _)
          (Or.inl ⟨c PUnit.unit, rfl, rfl⟩)
    | query a =>
        have ht_eq : t = query a c := by
          apply PFunctor.M.eq_of_dest_eq
          rw [ht]
          rfl
        subst ht_eq
        rw [simulate_query_eq_bind inner, simulate_query_eq_bind (outer.comp inner),
          Handler.comp_apply]
        rcases hu : PFunctor.M.dest (inner a) with ⟨sh, cu⟩
        cases sh with
        | pure r =>
            have hu_eq : inner a = pure r := by
              apply PFunctor.M.eq_of_dest_eq
              rw [hu]
              change (⟨.pure r, cu⟩ : (Poly F (E.B a)).Obj _) =
                ⟨.pure r, PEmpty.elim⟩
              congr 1
              funext z
              exact z.elim
            rw [hu_eq, bind_pure_left, simulate_step_eq, simulate_pure,
              bind_pure_left]
            refine ⟨step (simulate outer (simulate inner (c r))),
              step (simulate (outer.comp inner) (c r)), .refl _, .refl _, ?_⟩
            exact Match.tau _ _ (shape'_step _) (shape'_step _)
              (Or.inl ⟨c r, rfl, rfl⟩)
        | step =>
            have hu_eq : inner a = step (cu PUnit.unit) := by
              apply PFunctor.M.eq_of_dest_eq
              rw [hu]
              rfl
            rw [hu_eq, bind_step, simulate_step_eq, simulate_step_eq, bind_step]
            refine ⟨step (simulate outer
                (bind (cu PUnit.unit)
                  (fun b => step (simulate inner (c b))))),
              step (bind (simulate outer (cu PUnit.unit))
                (fun b => step (simulate (outer.comp inner) (c b)))),
              .refl _, .refl _, ?_⟩
            exact Match.tau _ _ (shape'_step _) (shape'_step _)
              (Or.inr (Or.inl ⟨E.B a, cu PUnit.unit, c, rfl, rfl⟩))
        | query a_F =>
            have hu_eq : inner a = query a_F cu := by
              apply PFunctor.M.eq_of_dest_eq
              rw [hu]
              rfl
            rw [hu_eq, bind_query, simulate_query_eq_bind,
              simulate_query_eq_bind, bind_assoc]
            simp only [bind_step]
            rcases hw : PFunctor.M.dest (outer a_F) with ⟨sh, cw⟩
            cases sh with
            | pure z =>
                have hw_eq : outer a_F = pure z := by
                  apply PFunctor.M.eq_of_dest_eq
                  rw [hw]
                  change (⟨.pure z, cw⟩ : (Poly G (F.B a_F)).Obj _) =
                    ⟨.pure z, PEmpty.elim⟩
                  congr 1
                  funext e
                  exact e.elim
                rw [hw_eq, bind_pure_left, bind_pure_left]
                refine ⟨step (simulate outer
                    (bind (cu z) (fun b => step (simulate inner (c b))))),
                  step (bind (simulate outer (cu z))
                    (fun b => step (simulate (outer.comp inner) (c b)))),
                  .refl _, .refl _, ?_⟩
                exact Match.tau _ _ (shape'_step _) (shape'_step _)
                  (Or.inr (Or.inl ⟨E.B a, cu z, c, rfl, rfl⟩))
            | step =>
                refine ⟨bind (outer a_F) (fun z => step (simulate outer
                    (bind (cu z) (fun b => step (simulate inner (c b)))))),
                  bind (outer a_F) (fun z => step
                    (bind (simulate outer (cu z))
                      (fun b => step (simulate (outer.comp inner) (c b))))),
                  .refl _, .refl _, ?_⟩
                exact Match.tau _ _ (dest_bind_step _ (outer a_F) cw hw)
                  (dest_bind_step _ (outer a_F) cw hw)
                  (Or.inr (Or.inr
                    ⟨E.B a, F.B a_F, cw PUnit.unit, cu, c, rfl, rfl⟩))
            | query q' =>
                refine ⟨bind (outer a_F) (fun z => step (simulate outer
                    (bind (cu z) (fun b => step (simulate inner (c b)))))),
                  bind (outer a_F) (fun z => step
                    (bind (simulate outer (cu z))
                      (fun b => step (simulate (outer.comp inner) (c b))))),
                  .refl _, .refl _, ?_⟩
                refine Match.query q' _ _
                  (dest_bind_query _ (outer a_F) q' cw hw)
                  (dest_bind_query _ (outer a_F) q' cw hw) ?_
                intro z
                exact Or.inr (Or.inr
                  ⟨E.B a, F.B a_F, cw z, cu, c, rfl, rfl⟩)
  · rcases hu : PFunctor.M.dest u with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have hu_eq : u = pure r := by
          apply PFunctor.M.eq_of_dest_eq
          rw [hu]
          change (⟨.pure r, c⟩ : (Poly F γ).Obj _) =
            ⟨.pure r, PEmpty.elim⟩
          congr 1
          funext z
          exact z.elim
        subst hu_eq
        rw [bind_pure_left, simulate_step_eq, simulate_pure, bind_pure_left]
        refine ⟨step (simulate outer (simulate inner (k r))),
          step (simulate (outer.comp inner) (k r)), .refl _, .refl _, ?_⟩
        exact Match.tau _ _ (shape'_step _) (shape'_step _)
          (Or.inl ⟨k r, rfl, rfl⟩)
    | step =>
        have hu_eq : u = step (c PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq
          rw [hu]
          rfl
        subst hu_eq
        rw [bind_step, simulate_step_eq, simulate_step_eq, bind_step]
        refine ⟨step (simulate outer
            (bind (c PUnit.unit) (fun b => step (simulate inner (k b))))),
          step (bind (simulate outer (c PUnit.unit))
            (fun b => step (simulate (outer.comp inner) (k b)))),
          .refl _, .refl _, ?_⟩
        exact Match.tau _ _ (shape'_step _) (shape'_step _)
          (Or.inr (Or.inl ⟨γ, c PUnit.unit, k, rfl, rfl⟩))
    | query a =>
        have hu_eq : u = query a c := by
          apply PFunctor.M.eq_of_dest_eq
          rw [hu]
          rfl
        subst hu_eq
        rw [bind_query, simulate_query_eq_bind, simulate_query_eq_bind,
          bind_assoc]
        simp only [bind_step]
        rcases hw : PFunctor.M.dest (outer a) with ⟨sh, cw⟩
        cases sh with
        | pure z =>
            have hw_eq : outer a = pure z := by
              apply PFunctor.M.eq_of_dest_eq
              rw [hw]
              change (⟨.pure z, cw⟩ : (Poly G (F.B a)).Obj _) =
                ⟨.pure z, PEmpty.elim⟩
              congr 1
              funext e
              exact e.elim
            rw [hw_eq, bind_pure_left, bind_pure_left]
            refine ⟨step (simulate outer
                (bind (c z) (fun b => step (simulate inner (k b))))),
              step (bind (simulate outer (c z))
                (fun b => step (simulate (outer.comp inner) (k b)))),
              .refl _, .refl _, ?_⟩
            exact Match.tau _ _ (shape'_step _) (shape'_step _)
              (Or.inr (Or.inl ⟨γ, c z, k, rfl, rfl⟩))
        | step =>
            refine ⟨bind (outer a) (fun z => step (simulate outer
                (bind (c z) (fun b => step (simulate inner (k b)))))),
              bind (outer a) (fun z => step
                (bind (simulate outer (c z))
                  (fun b => step (simulate (outer.comp inner) (k b))))),
              .refl _, .refl _, ?_⟩
            exact Match.tau _ _ (dest_bind_step _ (outer a) cw hw)
              (dest_bind_step _ (outer a) cw hw)
              (Or.inr (Or.inr ⟨γ, F.B a, cw PUnit.unit, c, k, rfl, rfl⟩))
        | query q' =>
            refine ⟨bind (outer a) (fun z => step (simulate outer
                (bind (c z) (fun b => step (simulate inner (k b)))))),
              bind (outer a) (fun z => step
                (bind (simulate outer (c z))
                  (fun b => step (simulate (outer.comp inner) (k b))))),
              .refl _, .refl _, ?_⟩
            refine Match.query q' _ _ (dest_bind_query _ (outer a) q' cw hw)
              (dest_bind_query _ (outer a) q' cw hw) ?_
            intro z
            exact Or.inr (Or.inr ⟨γ, F.B a, cw z, c, k, rfl, rfl⟩)
  · rcases hw : PFunctor.M.dest w with ⟨sh, c⟩
    cases sh with
    | pure z =>
        have hw_eq : w = pure z := by
          apply PFunctor.M.eq_of_dest_eq
          rw [hw]
          change (⟨.pure z, c⟩ : (Poly G δ).Obj _) =
            ⟨.pure z, PEmpty.elim⟩
          congr 1
          funext e
          exact e.elim
        subst hw_eq
        rw [bind_pure_left, bind_pure_left]
        refine ⟨step (simulate outer
            (bind (q z) (fun b => step (simulate inner (k b))))),
          step (bind (simulate outer (q z))
            (fun b => step (simulate (outer.comp inner) (k b)))),
          .refl _, .refl _, ?_⟩
        exact Match.tau _ _ (shape'_step _) (shape'_step _)
          (Or.inr (Or.inl ⟨γ, q z, k, rfl, rfl⟩))
    | step =>
        refine ⟨bind w (fun z => step (simulate outer
            (bind (q z) (fun b => step (simulate inner (k b)))))),
          bind w (fun z => step
            (bind (simulate outer (q z))
              (fun b => step (simulate (outer.comp inner) (k b))))),
          .refl _, .refl _, ?_⟩
        exact Match.tau _ _ (dest_bind_step _ w c hw) (dest_bind_step _ w c hw)
          (Or.inr (Or.inr ⟨γ, δ, c PUnit.unit, q, k, rfl, rfl⟩))
    | query a =>
        refine ⟨bind w (fun z => step (simulate outer
            (bind (q z) (fun b => step (simulate inner (k b)))))),
          bind w (fun z => step
            (bind (simulate outer (q z))
              (fun b => step (simulate (outer.comp inner) (k b))))),
          .refl _, .refl _, ?_⟩
        refine Match.query a _ _ (dest_bind_query _ w a c hw)
          (dest_bind_query _ w a c hw) ?_
        intro z
        exact Or.inr (Or.inr ⟨γ, δ, c z, q, k, rfl, rfl⟩)

/-- Handler composition is associative pointwise up to weak bisimulation. -/
theorem Handler.comp_assoc_apply {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {G : PFunctor.{uGA, uGB}}
    {H : PFunctor.{uHA, uHB}}
    (third : Handler G H) (second : Handler F G) (first : Handler E F)
    (a : E.A) :
    WeakBisim (third.comp (second.comp first) a)
      ((third.comp second).comp first a) := by
  simpa only [Handler.comp_apply] using simulate_comp third second (first a)

/-! ### One-step unfoldings of `mapSpec`

These are direct `M.corec` unfoldings using `dest_corec_eq` and the fact
that `M.dest` is injective (`PFunctor.M.eq_of_dest_eq`). They do **not**
need any bisimulation tooling. -/

@[simp] theorem mapSpec_pure {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (φ : PFunctor.Lens E F) (r : α) :
    mapSpec φ (pure (F := E) r) = pure r := by
  apply PFunctor.M.eq_of_dest_eq
  rw [mapSpec, PFunctor.M.dest_corec_eq _ _ (mapSpecStep_pure φ r)]
  unfold ITree.pure
  rw [PFunctor.M.dest_mk]
  congr 1
  funext b
  exact b.elim

@[simp] theorem mapSpec_step {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (φ : PFunctor.Lens E F) (t : ITree E α) :
    mapSpec φ (step t) = step (mapSpec φ t) := by
  apply PFunctor.M.eq_of_dest_eq
  rw [mapSpec, PFunctor.M.dest_corec_eq _ _ (mapSpecStep_step φ t)]
  unfold ITree.step
  rw [PFunctor.M.dest_mk]

@[simp] theorem mapSpec_query {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (φ : PFunctor.Lens E F) (a : E.A) (k : E.B a → ITree E α) :
    mapSpec φ (query a k) =
      query (φ.toFunA a) (fun b => mapSpec φ (k (φ.toFunB a b))) := by
  apply PFunctor.M.eq_of_dest_eq
  rw [mapSpec, PFunctor.M.dest_corec_eq _ _ (mapSpecStep_query φ a k)]
  unfold ITree.query
  rw [PFunctor.M.dest_mk]

/-! ### Functoriality of `mapSpec` -/

theorem mapSpec_id {E : PFunctor.{uEA, uEB}} {α : Type uα}
    (t : ITree E α) :
    mapSpec (PFunctor.Lens.id E) t = t := by
  conv_rhs => rw [← PFunctor.M.corec_dest t]
  refine PFunctor.M.corec_eq_corec
    (mapSpecStep (PFunctor.Lens.id E)) PFunctor.M.dest Eq t t rfl ?_
  rintro u v rfl
  rcases h : PFunctor.M.dest u with ⟨sh, c⟩
  cases sh with
  | pure r =>
      refine ⟨.pure r, c, c, ?_, rfl, fun b => b.elim⟩
      simp only [mapSpecStep, shape', h]
      congr 1
      funext b; exact b.elim
  | step =>
      refine ⟨.step, c, c, ?_, rfl, fun _ => rfl⟩
      simp only [mapSpecStep, shape', h]
  | query a =>
      refine ⟨.query a, c, c, ?_, rfl, fun _ => rfl⟩
      change mapSpecStep (PFunctor.Lens.id E) u = ⟨.query a, c⟩
      simp only [mapSpecStep, shape', h]
      rfl

/-- Computing one `M.dest` step of `mapSpec`, in terms of `mapSpecStep`. -/
theorem dest_mapSpec {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (φ : PFunctor.Lens E F) (u : ITree E α) :
    PFunctor.M.dest (mapSpec φ u) =
      ⟨(mapSpecStep φ u).1, fun b => mapSpec φ ((mapSpecStep φ u).2 b)⟩ := by
  rw [mapSpec, PFunctor.M.dest_corec_apply]

/-- Same as `dest_mapSpec` but stated with `shape'` on the LHS. -/
theorem shape'_mapSpec {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (φ : PFunctor.Lens E F) (u : ITree E α) :
    shape' (mapSpec φ u) =
      ⟨(mapSpecStep φ u).1, fun b => mapSpec φ ((mapSpecStep φ u).2 b)⟩ :=
  dest_mapSpec φ u

theorem mapSpec_comp {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    {G : PFunctor.{uGA, uGB}} {α : Type uα}
    (φ : PFunctor.Lens E F) (ψ : PFunctor.Lens F G) (t : ITree E α) :
    mapSpec (ψ ∘ₗ φ) t = mapSpec ψ (mapSpec φ t) := by
  refine PFunctor.M.corec_eq_corec
    (mapSpecStep (ψ ∘ₗ φ)) (mapSpecStep ψ)
    (fun u v => v = mapSpec φ u) t (mapSpec φ t) rfl ?_
  rintro u v rfl
  rcases h : PFunctor.M.dest u with ⟨sh, c⟩
  have hu : shape' u = ⟨sh, c⟩ := h
  cases sh with
  | pure r =>
      refine ⟨.pure r, PEmpty.elim, PEmpty.elim, ?_, ?_, ?_⟩
      · change mapSpecStep (ψ ∘ₗ φ) u = ⟨.pure r, PEmpty.elim⟩
        rw [mapSpecStep, hu]
      · change mapSpecStep ψ (mapSpec φ u) = ⟨.pure r, PEmpty.elim⟩
        rw [mapSpecStep, shape'_mapSpec, mapSpecStep, hu]
      · intro b; exact b.elim
  | step =>
      refine ⟨.step, fun _ => c PUnit.unit, fun _ => mapSpec φ (c PUnit.unit),
        ?_, ?_, fun _ => rfl⟩
      · change mapSpecStep (ψ ∘ₗ φ) u = ⟨.step, fun _ => c PUnit.unit⟩
        rw [mapSpecStep, hu]
      · change mapSpecStep ψ (mapSpec φ u) = ⟨.step, fun _ => mapSpec φ (c PUnit.unit)⟩
        rw [mapSpecStep, shape'_mapSpec, mapSpecStep, hu]
  | query a =>
      refine ⟨.query (ψ.toFunA (φ.toFunA a)),
        fun b => c ((ψ ∘ₗ φ).toFunB a b),
        fun b => mapSpec φ (c ((ψ ∘ₗ φ).toFunB a b)),
        ?_, ?_, fun _ => rfl⟩
      · change mapSpecStep (ψ ∘ₗ φ) u =
          ⟨.query (ψ.toFunA (φ.toFunA a)), fun b => c ((ψ ∘ₗ φ).toFunB a b)⟩
        rw [mapSpecStep, hu]
        rfl
      · change mapSpecStep ψ (mapSpec φ u) =
          ⟨.query (ψ.toFunA (φ.toFunA a)),
            fun b => mapSpec φ (c ((ψ ∘ₗ φ).toFunB a b))⟩
        rw [mapSpecStep, shape'_mapSpec, mapSpecStep, hu]
        rfl

/-! ### Monad-morphism laws for `mapSpec`

`mapSpec` is a monad morphism: it distributes over `bind` and `iter`
strictly (no τ-step insertion), in contrast to `simulate ∘ Handler.ofLens`
which only matches `mapSpec` up to weak bisim. The proofs are by
`PFunctor.M.bisim` with a relation that encodes the *defining equation*
(left-hand side ↔ right-hand side) plus the trivial diagonal closure. -/

theorem mapSpec_bind {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα} {β : Type uβ}
    (φ : PFunctor.Lens E F)
    (t : ITree E α) (k : α → ITree E β) :
    mapSpec φ (bind t k) = bind (mapSpec φ t) (fun a => mapSpec φ (k a)) := by
  refine PFunctor.M.bisim
    (fun (u v : ITree F β) =>
      u = v ∨ ∃ t : ITree E α,
        u = mapSpec φ (bind t k) ∧
        v = bind (mapSpec φ t) (fun a => mapSpec φ (k a)))
    ?_ _ _ (Or.inr ⟨t, rfl, rfl⟩)
  rintro u v (rfl | ⟨t, rfl, rfl⟩)
  · rcases h : PFunctor.M.dest u with ⟨sh, c⟩
    exact ⟨sh, c, c, rfl, rfl, fun _ => Or.inl rfl⟩
  · rcases h : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have ht : t = pure r := by
          apply PFunctor.M.eq_of_dest_eq; rw [h]
          change (⟨.pure r, c⟩ : (Poly E α).Obj _) = ⟨.pure r, PEmpty.elim⟩
          congr 1; funext z; exact z.elim
        subst ht
        rw [bind_pure_left, mapSpec_pure, bind_pure_left]
        rcases hk : PFunctor.M.dest (mapSpec φ (k r)) with ⟨sh', c'⟩
        exact ⟨sh', c', c', rfl, rfl, fun _ => Or.inl rfl⟩
    | step =>
        have ht : t = step (c PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq; rw [h]; rfl
        subst ht
        rw [bind_step, mapSpec_step, mapSpec_step, bind_step]
        refine ⟨.step,
          fun _ => mapSpec φ (bind (c PUnit.unit) k),
          fun _ => bind (mapSpec φ (c PUnit.unit)) (fun a => mapSpec φ (k a)),
          shape'_step _, shape'_step _,
          fun _ => Or.inr ⟨c PUnit.unit, rfl, rfl⟩⟩
    | query a =>
        have ht : t = query a c := by
          apply PFunctor.M.eq_of_dest_eq; rw [h]; rfl
        subst ht
        rw [bind_query, mapSpec_query, mapSpec_query, bind_query]
        refine ⟨.query (φ.toFunA a),
          fun b => mapSpec φ (bind (c (φ.toFunB a b)) k),
          fun b =>
            bind (mapSpec φ (c (φ.toFunB a b))) (fun a => mapSpec φ (k a)),
          shape'_query _ _, shape'_query _ _,
          fun b => Or.inr ⟨c (φ.toFunB a b), rfl, rfl⟩⟩

/-! ### One-step `M.dest` lemmas for `M.corec (iterStep _)`

Used by `mapSpec_iter` below. They factor the case analysis on `shape' t`
out of the bisimulation proof. -/

private theorem dest_corec_iterStep_pure_inl
    {E : PFunctor.{uEA, uEB}} {α : Type uα} {β : Type uβ}
    (body : β → ITree E (β ⊕ α)) (t : ITree E (β ⊕ α)) (j : β)
    (cIn : (Poly E (β ⊕ α)).B (.pure (.inl j)) → (Poly E (β ⊕ α)).M)
    (h : PFunctor.M.dest t = ⟨.pure (.inl j), cIn⟩) :
    PFunctor.M.dest (PFunctor.M.corec (iterStep body) t) =
      ⟨.step, fun _ => PFunctor.M.corec (iterStep body) (body j)⟩ := by
  rw [PFunctor.M.dest_corec_apply, iterStep, h]

private theorem dest_corec_iterStep_pure_inr
    {E : PFunctor.{uEA, uEB}} {α : Type uα} {β : Type uβ}
    (body : β → ITree E (β ⊕ α)) (t : ITree E (β ⊕ α)) (r : α)
    (cIn : (Poly E (β ⊕ α)).B (.pure (.inr r)) → (Poly E (β ⊕ α)).M)
    (h : PFunctor.M.dest t = ⟨.pure (.inr r), cIn⟩) :
    PFunctor.M.dest (PFunctor.M.corec (iterStep body) t) =
      ⟨.pure r, PEmpty.elim⟩ := by
  rw [PFunctor.M.dest_corec_apply, iterStep, h]
  congr 1
  funext z
  exact z.elim

private theorem dest_corec_iterStep_step
    {E : PFunctor.{uEA, uEB}} {α : Type uα} {β : Type uβ}
    (body : β → ITree E (β ⊕ α)) (t : ITree E (β ⊕ α))
    (c : PUnit.{uEB + 1} → ITree E (β ⊕ α))
    (h : PFunctor.M.dest t = ⟨.step, c⟩) :
    PFunctor.M.dest (PFunctor.M.corec (iterStep body) t) =
      ⟨.step, fun u => PFunctor.M.corec (iterStep body) (c u)⟩ := by
  rw [PFunctor.M.dest_corec_apply, iterStep, h]

private theorem dest_corec_iterStep_query
    {E : PFunctor.{uEA, uEB}} {α : Type uα} {β : Type uβ}
    (body : β → ITree E (β ⊕ α)) (t : ITree E (β ⊕ α)) (a : E.A)
    (c : E.B a → ITree E (β ⊕ α))
    (h : PFunctor.M.dest t = ⟨.query a, c⟩) :
    PFunctor.M.dest (PFunctor.M.corec (iterStep body) t) =
      ⟨.query a, fun b => PFunctor.M.corec (iterStep body) (c b)⟩ := by
  rw [PFunctor.M.dest_corec_apply, iterStep, h]

theorem mapSpec_iter {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα} {β : Type uβ}
    (φ : PFunctor.Lens E F)
    (body : β → ITree E (β ⊕ α)) (init : β) :
    mapSpec φ (iter body init) = iter (fun j => mapSpec φ (body j)) init := by
  refine PFunctor.M.bisim
    (fun (u v : ITree F α) =>
      u = v ∨ ∃ t : ITree E (β ⊕ α),
        u = mapSpec φ (PFunctor.M.corec (iterStep body) t) ∧
        v = PFunctor.M.corec
              (iterStep (fun j => mapSpec φ (body j))) (mapSpec φ t))
    ?_ _ _ (Or.inr ⟨body init, rfl, rfl⟩)
  rintro u v (rfl | ⟨t, rfl, rfl⟩)
  · rcases h : PFunctor.M.dest u with ⟨sh, c⟩
    exact ⟨sh, c, c, rfl, rfl, fun _ => Or.inl rfl⟩
  · rcases h : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure rj =>
        cases rj with
        | inl j =>
            have hL : PFunctor.M.dest
                (PFunctor.M.corec (iterStep body) t) =
                ⟨.step, fun _ => PFunctor.M.corec (iterStep body) (body j)⟩ :=
              dest_corec_iterStep_pure_inl body t j c h
            have hMt : mapSpec φ t = pure (.inl j) := by
              have ht : t = pure (.inl j) := by
                apply PFunctor.M.eq_of_dest_eq; rw [h]
                change (⟨.pure (.inl j), c⟩ : (Poly E (β ⊕ α)).Obj _) =
                  ⟨.pure (.inl j), PEmpty.elim⟩
                congr 1; funext z; exact z.elim
              rw [ht, mapSpec_pure]
            have hR : PFunctor.M.dest
                (PFunctor.M.corec
                  (iterStep (fun j => mapSpec φ (body j))) (mapSpec φ t)) =
                ⟨.step, fun _ => PFunctor.M.corec
                  (iterStep (fun j => mapSpec φ (body j)))
                  (mapSpec φ (body j))⟩ := by
              rw [hMt]
              exact dest_corec_iterStep_pure_inl
                (fun j => mapSpec φ (body j)) (pure (.inl j)) j PEmpty.elim
                (PFunctor.M.dest_mk _)
            refine ⟨.step,
              fun _ => mapSpec φ (PFunctor.M.corec (iterStep body) (body j)),
              fun _ => PFunctor.M.corec
                (iterStep (fun j => mapSpec φ (body j))) (mapSpec φ (body j)),
              ?_, hR, fun _ => Or.inr ⟨body j, rfl, rfl⟩⟩
            simp only [dest_mapSpec, mapSpecStep, shape']
            rw [hL]
        | inr r =>
            have hL : PFunctor.M.dest
                (PFunctor.M.corec (iterStep body) t) =
                ⟨.pure r, PEmpty.elim⟩ :=
              dest_corec_iterStep_pure_inr body t r c h
            have hMt : mapSpec φ t = pure (.inr r) := by
              have ht : t = pure (.inr r) := by
                apply PFunctor.M.eq_of_dest_eq; rw [h]
                change (⟨.pure (.inr r), c⟩ : (Poly E (β ⊕ α)).Obj _) =
                  ⟨.pure (.inr r), PEmpty.elim⟩
                congr 1; funext z; exact z.elim
              rw [ht, mapSpec_pure]
            have hR : PFunctor.M.dest
                (PFunctor.M.corec
                  (iterStep (fun j => mapSpec φ (body j))) (mapSpec φ t)) =
                ⟨.pure r, PEmpty.elim⟩ := by
              rw [hMt]
              exact dest_corec_iterStep_pure_inr
                (fun j => mapSpec φ (body j)) (pure (.inr r)) r PEmpty.elim
                (PFunctor.M.dest_mk _)
            refine ⟨.pure r, PEmpty.elim, PEmpty.elim, ?_, hR, fun b => b.elim⟩
            simp only [dest_mapSpec, mapSpecStep, shape']
            rw [hL]
            congr 1
            funext z
            exact z.elim
    | step =>
        have hL : PFunctor.M.dest
            (PFunctor.M.corec (iterStep body) t) =
            ⟨.step, fun u => PFunctor.M.corec (iterStep body) (c u)⟩ :=
          dest_corec_iterStep_step body t c h
        have hMt : mapSpec φ t = step (mapSpec φ (c PUnit.unit)) := by
          have ht : t = step (c PUnit.unit) := by
            apply PFunctor.M.eq_of_dest_eq; rw [h]; rfl
          rw [ht, mapSpec_step]
        have hR : PFunctor.M.dest
            (PFunctor.M.corec
              (iterStep (fun j => mapSpec φ (body j))) (mapSpec φ t)) =
            ⟨.step, fun _ => PFunctor.M.corec
              (iterStep (fun j => mapSpec φ (body j)))
              (mapSpec φ (c PUnit.unit))⟩ := by
          rw [hMt]
          exact dest_corec_iterStep_step
            (fun j => mapSpec φ (body j)) (step (mapSpec φ (c PUnit.unit)))
            (fun _ => mapSpec φ (c PUnit.unit)) (PFunctor.M.dest_mk _)
        refine ⟨.step,
          fun _ => mapSpec φ (PFunctor.M.corec (iterStep body) (c PUnit.unit)),
          fun _ => PFunctor.M.corec
            (iterStep (fun j => mapSpec φ (body j)))
            (mapSpec φ (c PUnit.unit)),
          ?_, hR, fun _ => Or.inr ⟨c PUnit.unit, rfl, rfl⟩⟩
        simp only [dest_mapSpec, mapSpecStep, shape']
        rw [hL]
    | query a =>
        have hL : PFunctor.M.dest
            (PFunctor.M.corec (iterStep body) t) =
            ⟨.query a, fun b => PFunctor.M.corec (iterStep body) (c b)⟩ :=
          dest_corec_iterStep_query body t a c h
        have hMt : mapSpec φ t =
            query (φ.toFunA a) (fun b => mapSpec φ (c (φ.toFunB a b))) := by
          have ht : t = query a c := by
            apply PFunctor.M.eq_of_dest_eq; rw [h]; rfl
          rw [ht, mapSpec_query]
        have hR : PFunctor.M.dest
            (PFunctor.M.corec
              (iterStep (fun j => mapSpec φ (body j))) (mapSpec φ t)) =
            ⟨.query (φ.toFunA a), fun b => PFunctor.M.corec
              (iterStep (fun j => mapSpec φ (body j)))
              (mapSpec φ (c (φ.toFunB a b)))⟩ := by
          rw [hMt]
          exact dest_corec_iterStep_query
            (fun j => mapSpec φ (body j))
            (query (φ.toFunA a) (fun b => mapSpec φ (c (φ.toFunB a b))))
            (φ.toFunA a)
            (fun b => mapSpec φ (c (φ.toFunB a b)))
            (PFunctor.M.dest_mk _)
        refine ⟨.query (φ.toFunA a),
          fun b => mapSpec φ (PFunctor.M.corec (iterStep body)
            (c (φ.toFunB a b))),
          fun b => PFunctor.M.corec
            (iterStep (fun j => mapSpec φ (body j)))
            (mapSpec φ (c (φ.toFunB a b))),
          ?_, hR, fun b => Or.inr ⟨c (φ.toFunB a b), rfl, rfl⟩⟩
        simp only [dest_mapSpec, mapSpecStep, shape']
        rw [hL]

/-! ### Derived `mapSpec` lemmas

These follow directly from `mapSpec_bind` + `mapSpec_pure`. -/

@[simp] theorem mapSpec_map {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα} {β : Type uβ}
    (φ : PFunctor.Lens E F) (f : α → β) (t : ITree E α) :
    mapSpec φ (ITree.map f t) = ITree.map f (mapSpec φ t) := by
  simp only [ITree.map, mapSpec_bind, mapSpec_pure]

theorem mapSpec_functorMap {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α β : Type u}
    (φ : PFunctor.Lens E F) (f : α → β)
    (t : ITree E α) : mapSpec φ (f <$> t) = f <$> mapSpec φ t := by
  simp only [map_eq_functor_map, mapSpec_map]

@[simp] theorem mapSpec_cat {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα} {β : Type uβ}
    {γ : Type uγ} (φ : PFunctor.Lens E F)
    (f : α → ITree E β) (g : β → ITree E γ) (a : α) :
    mapSpec φ (ITree.cat f g a) =
      ITree.cat (mapSpec φ ∘ f) (mapSpec φ ∘ g) a := by
  change mapSpec φ (bind (f a) g) =
    bind ((mapSpec φ ∘ f) a) (fun b => (mapSpec φ ∘ g) b)
  rw [mapSpec_bind]
  rfl

/-- `mapSpec` distributes over `Seq.seq`, i.e. it is an Applicative
morphism. Falls out of `mapSpec_bind` + `mapSpec_functorMap` after unfolding
the default `seq` of `Monad (ITree F)` to `bind`. -/
@[simp] theorem mapSpec_seq {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α β : Type u}
    (φ : PFunctor.Lens E F) (mf : ITree E (α → β))
    (mx : ITree E α) :
    mapSpec φ (mf <*> mx) = mapSpec φ mf <*> mapSpec φ mx := by
  change mapSpec φ (bind mf (fun f => f <$> mx)) =
    bind (mapSpec φ mf) (fun f => f <$> mapSpec φ mx)
  rw [mapSpec_bind]
  simp only [mapSpec_functorMap]

/-! ### Relating `simulate` and `mapSpec` -/

theorem simulate_ofLens {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {α : Type uα}
    (φ : PFunctor.Lens E F) (t : ITree E α) :
    WeakBisim (simulate (Handler.ofLens φ) t) (mapSpec φ t) := by
  refine WeakBisim.coinduct
    (fun x y => (∃ t : ITree E α,
        x = simulate (Handler.ofLens φ) t ∧ y = mapSpec φ t) ∨
      (∃ t : ITree E α,
        x = step (simulate (Handler.ofLens φ) t) ∧ y = mapSpec φ t))
    ?_ (Or.inl ⟨t, rfl, rfl⟩)
  rintro x y hxy
  obtain ⟨t, hxx', rfl⟩ : ∃ t,
      TauSteps x (simulate (Handler.ofLens φ) t) ∧ y = mapSpec φ t := by
    rcases hxy with ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
    · exact ⟨t, TauSteps.refl _, rfl⟩
    · exact ⟨t, TauSteps.one _ (shape'_step _), rfl⟩
  rcases ht : PFunctor.M.dest t with ⟨sh, c⟩
  cases sh with
  | pure r =>
      have ht_eq : t = pure r := by
        apply PFunctor.M.eq_of_dest_eq; rw [ht]
        change (⟨.pure r, c⟩ : (Poly E α).Obj _) = ⟨.pure r, PEmpty.elim⟩
        congr 1; funext z; exact z.elim
      subst ht_eq
      rw [simulate_pure] at hxx'
      rw [mapSpec_pure]
      exact ⟨pure r, pure r, hxx', .refl _,
        Match.pure r (shape'_pure r) (shape'_pure r)⟩
  | step =>
      have ht_eq : t = step (c PUnit.unit) := by
        apply PFunctor.M.eq_of_dest_eq; rw [ht]; rfl
      subst ht_eq
      rw [simulate_step_eq] at hxx'
      rw [mapSpec_step]
      refine ⟨step (simulate (Handler.ofLens φ) (c PUnit.unit)),
        step (mapSpec φ (c PUnit.unit)), hxx', .refl _, ?_⟩
      refine Match.tau _ _ (shape'_step _) (shape'_step _) ?_
      exact Or.inl ⟨c PUnit.unit, rfl, rfl⟩
  | query a =>
      have ht_eq : t = query a c := by
        apply PFunctor.M.eq_of_dest_eq; rw [ht]; rfl
      subst ht_eq
      rw [simulate_query_eq_bind,
          show (Handler.ofLens φ) a =
            query (φ.toFunA a) (fun b => pure (φ.toFunB a b)) from rfl,
          bind_query] at hxx'
      simp only [bind_pure_left] at hxx'
      rw [mapSpec_query]
      refine ⟨query (φ.toFunA a)
          (fun b => step (simulate (Handler.ofLens φ) (c (φ.toFunB a b)))),
        query (φ.toFunA a) (fun b => mapSpec φ (c (φ.toFunB a b))),
        hxx', .refl _, ?_⟩
      refine Match.query (φ.toFunA a) _ _ (shape'_query _ _) (shape'_query _ _) ?_
      intro b
      exact Or.inr ⟨c (φ.toFunB a b), rfl, rfl⟩

/-- Composition of pure-renaming handlers agrees pointwise, up to weak
bisimilarity, with composition of their underlying lenses. -/
theorem Handler.ofLens_comp_apply {E : PFunctor.{uEA, uEB}}
    {F : PFunctor.{uFA, uFB}} {G : PFunctor.{uGA, uGB}}
    (φ : PFunctor.Lens E F)
    (ψ : PFunctor.Lens F G) (a : E.A) :
    WeakBisim ((Handler.ofLens ψ).comp (Handler.ofLens φ) a)
      (Handler.ofLens (ψ ∘ₗ φ) a) := by
  simpa only [Handler.comp_apply, Handler.ofLens, mapSpec_query, mapSpec_pure,
    PFunctor.Lens.comp, Function.comp_apply] using
    (simulate_ofLens ψ (Handler.ofLens φ a))

end ITree
