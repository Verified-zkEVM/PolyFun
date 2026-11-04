/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Do
public import PolyFun.Control.Do.Spec
public import PolyFun.PFunctor.Handler.Charge

/-!
# Charges for core `vcgen`

Two ways to hand cost reasoning to core `vcgen`.

**The budget reading.** `FreeM.budgetWPMonad c B` interprets free programs over predicates on
the amount spent. Its weakest precondition is the fold of `OpSpec.budget c B`, so a triple from
"`s` spent" to "at most `B` spent" is exactly `IsChargeBound` (`isChargeBound_iff_triple`). Its
call rule `Spec.lift_budget` asks `s + c a ≤ B` and continues from `s + c a`, stated with the
lattice connectives `⊓` and `⨅` that `vcgen` splits, so `vcgen` proceeds call by call. Unlike the
upper-bound reading of `OpSpec.charge`, there is no supremum to stop at. The reading fixes `c` and
`B`, so it is installed locally with `attribute [local instance]`, and its call rule is scoped:
`open scoped PFunctor.FreeM.BudgetReading`.

**The instrumented reading.** `Handler.withCharge h c a` is `modify (· + c a)` followed by `h a`
(`withCharge_eq_modify`, a `vcgen` rule under `open scoped PFunctor.Handler.ChargeSteps`), so the
amount spent is ordinary `StateT` state
and core's state rules and loop invariants apply in any base interpretation. Under the demonic
reading of the base, a triple for a program run through the instrumented identity handler is a
statement about every completed path and the amount spent along it
(`triple_liftM_id_withCharge_iff`), which turns a `vcgen` proof into a completed-path cost bound.
-/

@[expose] public section

universe uA uB v

open Std.WP

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, uB}} {ω : Type uB} [Add ω] [LE ω]

/-- The budget reading of a charge: free programs interpreted over predicates on the amount
spent, with a call at `a` admitted when `s + c a ≤ B`. -/
abbrev budgetWPMonad (c : P.A → ω) (B : ω) : WPMonad (FreeM P) (ω → Prop) EStack⟨⟩ :=
  (OpSpec.budget c B).toWPMonad (OpSpec.budget_monotone c B)

theorem budgetWPMonad_wp (c : P.A → ω) (B : ω) {α : Type uB} (x : FreeM P α)
    (post : α → ω → Prop) (epost : EStack⟨⟩) :
    ((budgetWPMonad c B).toWP α).wp x post epost = wpFold (OpSpec.budget c B) x post :=
  OpSpec.toWPMonad_wp _ _ x post epost

/-- A charge bound is a triple of the budget reading from "`s` spent" to "at most `B` spent". -/
theorem isChargeBound_iff_triple [Zero ω] (c : P.A → ω) (B : ω) {α : Type uB} (x : FreeM P α)
    (s : ω) :
    x.IsChargeBound c B s ↔
      @Triple (ω → Prop) EStack⟨⟩ (FreeM P α) α _ _ x ((budgetWPMonad c B).toWP α)
        (fun t => t = s) (fun _ t => t ≤ B) ⊥ := by
  let := budgetWPMonad (P := P) c B
  constructor
  · intro h
    refine ⟨fun t ht => ?_⟩
    subst ht
    change ((budgetWPMonad c B).toWP α).wp x (fun _ t => t ≤ B) ⊥ t
    rw [budgetWPMonad_wp]
    exact h
  · intro h
    have := h.le_wp s rfl
    change ((budgetWPMonad c B).toWP α).wp x (fun _ t => t ≤ B) ⊥ s at this
    rwa [budgetWPMonad_wp] at this

namespace Spec

/-- Under the budget reading, a call at `a` asks `s + c a ≤ B` and continues from `s + c a`. The
precondition is stated with the lattice connectives `⊓` and `⨅`, which `vcgen` splits, so it
proceeds call by call. It is a `vcgen` rule under `open scoped PFunctor.FreeM.BudgetReading`. -/
theorem lift_budget (c : P.A → ω) (B : ω) (a : P.A) (Q : P.B a → ω → Prop) (E : EStack⟨⟩) :
    @Triple (ω → Prop) EStack⟨⟩ (FreeM P (P.B a)) (P.B a) _ _ (FreeM.lift (P := P) a)
      ((budgetWPMonad c B).toWP _)
      (Lean.Order.meet (fun s => s + c a ≤ B) (Lean.Order.iInf fun b => fun s => Q b (s + c a)))
      Q E := by
  let := budgetWPMonad (P := P) c B
  refine ⟨fun s hs => ?_⟩
  rw [budgetWPMonad_wp, FreeM.wpFold_lift]
  simp only [Lean.Order.meet_apply, Lean.Order.iInf_apply] at hs
  have h₁ : Lean.Order.PartialOrder.rel _ _ := Lean.Order.meet_le_left (s + c a ≤ B)
    (Lean.Order.iInf fun i => Q i (s + c a))
  have h₂ : Lean.Order.PartialOrder.rel _ _ := Lean.Order.meet_le_right (s + c a ≤ B)
    (Lean.Order.iInf fun i => Q i (s + c a))
  exact ⟨h₁ hs, fun b => Lean.Order.iInf_le (fun i => Q i (s + c a)) b (h₂ hs)⟩

end Spec

namespace BudgetReading

attribute [scoped spec] Spec.lift_budget

end BudgetReading

end FreeM

namespace Handler

variable {P : PFunctor.{uA, uB}} {ω : Type uB}

/-- An instrumented call adds its charge to the state and then runs the handler. It is a `vcgen`
rule under `open scoped PFunctor.Handler.ChargeSteps`. -/
theorem withCharge_eq_modify {m : Type uB → Type v} [Monad m] [LawfulMonad m] [Add ω]
    (h : Handler m P) (c : P.A → ω) (a : P.A) :
    h.withCharge c a = (modify (· + c a) >>= fun _ => StateT.lift (h a) : StateT ω m (P.B a)) := by
  refine StateT.ext fun s => ?_
  simp [Handler.run_withCharge]

namespace ChargeSteps

attribute [scoped spec] withCharge_eq_modify

end ChargeSteps

section Demonic

open scoped FreeM.DemonicWP

/-- **From `vcgen` to cost bounds.** Under the demonic reading of the base, a triple for a program
run through the identity handler instrumented with a charge says that every completed path meets
the postcondition at its output and the amount spent along it. -/
theorem triple_liftM_id_withCharge_iff [AddMonoid ω] (c : P.A → ω) {α : Type uB}
    (x : FreeM P α) (s : ω) (post : α → ω → Prop) :
    Triple (x.liftM ((Handler.id P).withCharge c)) (fun t => t = s) post ⊥ ↔
      ∀ p : FreeM.Path x, post (FreeM.output x p) (s + FreeM.Path.charge c x p) := by
  rw [Triple.iff]
  have key : ∀ t, wp (x.liftM ((Handler.id P).withCharge c)) post ⊥ t ↔
      ∀ z ∈ FreeM.supp ((x.liftM ((Handler.id P).withCharge c)).run t), post z.1 z.2 := by
    intro t
    rw [StateT.wp_apply_eq, FreeM.DemonicWP.wp_apply_eq,
      MonadAttach.allOutputs_iff_forall_support, FreeM.support_eq_supp]
  constructor
  · intro h p
    exact (key s).1 (h s rfl) _ (by rw [supp_run_liftM_id_withCharge]; exact ⟨p, rfl⟩)
  · intro h t ht
    subst ht
    refine (key t).2 fun z hz => ?_
    rw [supp_run_liftM_id_withCharge] at hz
    obtain ⟨p, rfl⟩ := hz
    exact h p

end Demonic

end Handler

end PFunctor
