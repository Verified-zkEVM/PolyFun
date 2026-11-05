/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Value
public import PolyFun.PFunctor.Free.Path.Charge
public import PolyFun.PFunctor.Handler.Free
public import PolyFun.PFunctor.Handler.Instrumentation.Free
public import PolyFun.PFunctor.Handler.Sum
public import Mathlib.Control.Monad.Writer

/-!
# Charges through handlers

A handler implements the calls of an interface `P`. This module relates the charge bounds and
costs of `PolyFun.PFunctor.Free.Cost` to the runs of programs through handlers.

## Handlers implemented by free programs

`h.WithinCharge d c` says that the implementation `h a` of each call at `a` stays within `c a`
under the target charge `d`. Simulating a program within budget through such a handler stays
within the same budget (`FreeM.IsChargeBound.liftM`). Identity, lens and sum handlers are within
their obvious charges, and certificates compose (`WithinCharge.comp`). In value form,
`handlerCost d h` is the worst-case cost of each implementation, with equations for identity, lens
and sum handlers and the bound `handlerCost_comp_le` for composites.

## Stateful handlers

For a handler into `StateT σ (FreeM Q)` whose step bound holds from every state, the same transfer
holds (`FreeM.IsChargeBound.run_liftM`). When the step's target charge depends on the state, a
potential pays for it: `Path.exists_run_liftM_amortized` bounds the target charge of every
completed path by the source charge plus the growth of the potential.

## Pausing runs

`FreeM.runUntil h x state` runs `x` through a handler that may decline a call, returning either the
output or the pending call with its continuation. `FreeM.IsChargeBound.runUntil` is the budget form
of the amortized transfer: a nonnegative potential that pays for each step gives the run a target
budget. Every paused continuation stays within the budget of the program it interrupts
(`FreeM.IsChargeBound.runUntil_paused`).

## Running in any monad

`h.withCharge c` runs `h` while keeping the amount spent as state: a call at `a` adds `c a`
before it runs. Forgetting the state recovers the handler (`fst_map_run_liftM_withCharge`), and on
every possible result of a run of a program within budget `B`, the amount spent is at most `B`
(`FreeM.IsChargeBound.le_of_canReturn_run_liftM_withCharge`). This is an instance of resource
growth (`FreeM.IsChargeBound.le_of_canReturn_run_liftM`): if each call at `a` raises a measure `f`
of the handler state by at most `c a`, then a program within budget `B` raises it by at most `B`.
`h.withChargeW c` logs the charges in a writer instead; it is writer tracing of the charge
(`withChargeW_eq_withTraceBefore`).

`run_liftM_withCharge_id` evaluates a run through a deterministic handler: it returns the output
and the charge of the one path that handler picks.

`h.withBudget c B` refuses a call that would spend more than `B`, and `h.withBudgetOr c B fallback`
answers it with a fallback instead. On a program within budget neither intervenes
(`run_liftM_withBudget_of_isChargeBound`, `run_liftM_withBudgetOr_of_isChargeBound`).
-/

@[expose] public section

universe uA uB uA₂ uA₃ v w

namespace PFunctor

namespace Handler

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}

/-! ## Charge certificates for free handlers -/

section Certificate

/-- The implementation of each call at `a` stays within `c a` under the target charge `d`. -/
def WithinCharge {ω : Type w} [Add ω] [LE ω] [Zero ω] (h : Handler (FreeM Q) P) (d : Q.A → ω)
    (c : P.A → ω) : Prop :=
  ∀ a, (h a).IsChargeBound d (c a)

theorem WithinCharge.sum {ω : Type w} [Add ω] [LE ω] [Zero ω] {f : Handler (FreeM R) P}
    {g : Handler (FreeM R) Q} {d : R.A → ω} {c₁ : P.A → ω} {c₂ : Q.A → ω}
    (hf : f.WithinCharge d c₁) (hg : g.WithinCharge d c₂) :
    (sum f g).WithinCharge d (Sum.elim c₁ c₂) := by
  rintro (a | a)
  · exact hf a
  · exact hg a

variable {ω : Type w} [AddCommMonoid ω] [PartialOrder ω]

theorem withinCharge_id (d : Q.A → ω) : (Handler.id Q).WithinCharge d d :=
  fun a => (FreeM.isChargeBound_lift_iff a).2 (by rw [zero_add])

theorem withinCharge_ofLens (l : Lens P Q) (d : Q.A → ω) :
    (ofLens l).WithinCharge d (d ∘ l.toFunA) :=
  fun a => ⟨by rw [zero_add]; rfl, fun _ => by rw [zero_add]; exact le_rfl⟩

theorem WithinCharge.comp [IsOrderedAddMonoid ω] {second : Handler (FreeM R) Q}
    {first : Handler (FreeM Q) P} {e : R.A → ω} {d : Q.A → ω} {c : P.A → ω}
    (hs : second.WithinCharge e d) (hf : first.WithinCharge d c) :
    (second.comp first).WithinCharge e c :=
  fun a => (hf a).liftM second fun b => hs b

end Certificate

/-! ## Instrumentation -/

section Instrumentation

variable {m : Type uB → Type v} {ω : Type uB}

/-- Instrument a handler with a charge: a call at `a` adds `c a` to the amount spent, kept as
state, and then runs the handler. -/
def withCharge [Functor m] [Add ω] (h : Handler m P) (c : P.A → ω) : Handler (StateT ω m) P :=
  fun a s => (fun b => (b, s + c a)) <$> h a

@[simp]
theorem run_withCharge [Functor m] [Add ω] (h : Handler m P) (c : P.A → ω) (a : P.A) (s : ω) :
    (h.withCharge c a).run s = (fun b => (b, s + c a)) <$> h a :=
  rfl

/-- Forgetting the amount spent recovers the uninstrumented run. -/
theorem fst_map_run_liftM_withCharge [Monad m] [LawfulMonad m] [Add ω] (h : Handler m P)
    (c : P.A → ω) {α : Type uB} (x : FreeM P α) (s : ω) :
    Prod.fst <$> (x.liftM (h.withCharge c)).run s = x.liftM h := by
  induction x using FreeM.rec generalizing s with
  | pure a => simp [FreeM.liftM]
  | liftBind a r ih =>
    change Prod.fst <$> (h.withCharge c a >>= fun b => (r b).liftM (h.withCharge c)).run s =
      h a >>= fun b => (r b).liftM h
    simp [StateT.run_bind, bind_map_left, map_bind, ih]

/-- **Deterministic runs.** Running a program through a handler into `Id` instrumented with a
charge returns the output of the one path the handler picks, and adds that path's charge to the
amount spent. With subsingleton answers this is the worst case
(`Path.forall_charge_le_iff_ofHandler`). -/
theorem run_liftM_withCharge_id [AddMonoid ω] (h : Handler Id P) (c : P.A → ω) {α : Type uB}
    (x : FreeM P α) (s : ω) :
    ((x.liftM (h.withCharge c)).run s).run =
      (FreeM.output x (FreeM.Path.ofHandler (fun a => (h a).run) x),
        s + FreeM.Path.charge c x (FreeM.Path.ofHandler (fun a => (h a).run) x)) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact (congrArg (Prod.mk a) (add_zero s)).symm
  | liftBind a r ih =>
    change (((r (h a).run).liftM (h.withCharge c)).run (s + c a)).run = _
    rw [ih, add_assoc]
    rfl

/-- **Instrumenting the program itself.** Run through the identity handler instrumented with a
charge, a program returns, on each completed path, its output together with the amount spent along
that path. -/
theorem supp_run_liftM_id_withCharge [AddMonoid ω] (c : P.A → ω) {α : Type uB} (x : FreeM P α)
    (s : ω) :
    FreeM.supp ((x.liftM ((Handler.id P).withCharge c)).run s) =
      Set.range fun p : FreeM.Path x => (FreeM.output x p, s + FreeM.Path.charge c x p) := by
  induction x using FreeM.rec generalizing s with
  | pure a =>
    ext z
    change z = (a, s) ↔ _
    exact ⟨fun h => ⟨⟨⟩, by rw [h]; exact congrArg (Prod.mk a) (add_zero s)⟩,
      fun ⟨_, h⟩ => h.symm.trans (congrArg (Prod.mk a) (add_zero s))⟩
  | liftBind a r ih =>
    change FreeM.supp (FreeM.liftBind a fun b =>
      ((r b).liftM ((Handler.id P).withCharge c)).run (s + c a)) = _
    ext z
    simp only [FreeM.supp, Set.mem_iUnion, ih, Set.mem_range]
    constructor
    · rintro ⟨b, p, rfl⟩
      exact ⟨⟨b, p⟩, by rw [add_assoc]; rfl⟩
    · rintro ⟨⟨b, p⟩, rfl⟩
      exact ⟨b, p, by rw [add_assoc]; rfl⟩

/-! ### Writer instrumentation -/

/-- Instrument a handler with a charge in a writer: a call at `a` writes `c a`. The log lives in
`Multiplicative ω`, so it accumulates the sum of the charges. -/
def withChargeW [Functor m] (h : Handler m P) (c : P.A → ω) :
    Handler (WriterT (Multiplicative ω) m) P :=
  fun a => WriterT.mk ((fun b => (b, Multiplicative.ofAdd (c a))) <$> h a)

@[simp]
theorem run_withChargeW [Functor m] (h : Handler m P) (c : P.A → ω) (a : P.A) :
    (h.withChargeW c a).run = (fun b => (b, Multiplicative.ofAdd (c a))) <$> h a :=
  rfl

/-- Charging in a writer is writer tracing of the charge, logged before each call. -/
theorem withChargeW_eq_withTraceBefore [Monad m] [LawfulMonad m] [AddMonoid ω] (h : Handler m P)
    (c : P.A → ω) : h.withChargeW c = h.withTraceBefore fun a => Multiplicative.ofAdd (c a) := by
  funext a
  apply WriterT.ext
  simp [withTraceBefore_apply, run_withChargeW, MonadWriter.tell]

/-- **Deterministic runs, writer form.** Running a program through a handler into `Id`
instrumented with a charge in a writer returns the output of the one path the handler picks and
logs that path's charge. -/
theorem run_liftM_withChargeW_id [AddMonoid ω] (h : Handler Id P) (c : P.A → ω) {α : Type uB}
    (x : FreeM P α) :
    (x.liftM (h.withChargeW c)).run.run =
      (FreeM.output x (FreeM.Path.ofHandler (fun a => (h a).run) x),
        Multiplicative.ofAdd
          (FreeM.Path.charge c x (FreeM.Path.ofHandler (fun a => (h a).run) x))) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    change ((fun q : _ × Multiplicative ω => (q.1, Multiplicative.ofAdd (c a) * q.2)) <$>
      ((r (h a).run).liftM (h.withChargeW c)).run).run = _
    rw [Id.run_map, ih]
    rfl

/-- **The program's own log.** Run through the identity handler instrumented with a charge in a
writer, a program returns, on each completed path, its output together with that path's charge. -/
theorem supp_run_liftM_id_withChargeW [AddMonoid ω] (c : P.A → ω) {α : Type uB} (x : FreeM P α) :
    FreeM.supp (x.liftM ((Handler.id P).withChargeW c)).run =
      Set.range fun p : FreeM.Path x =>
        (FreeM.output x p, Multiplicative.ofAdd (FreeM.Path.charge c x p)) := by
  induction x using FreeM.rec with
  | pure a =>
    ext z
    change z = (a, 1) ↔ _
    exact ⟨fun h => ⟨⟨⟩, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  | liftBind a r ih =>
    have ih' : ∀ b, MonadAttach.support ((r b).liftM ((Handler.id P).withChargeW c)).run =
        Set.range fun p : FreeM.Path (r b) =>
          (FreeM.output (r b) p, Multiplicative.ofAdd (FreeM.Path.charge c (r b) p)) := ih
    change MonadAttach.support (FreeM.liftBind a fun b =>
      FreeM.map (fun q : _ × Multiplicative ω => (q.1, Multiplicative.ofAdd (c a) * q.2))
        ((r b).liftM ((Handler.id P).withChargeW c)).run) = _
    ext z
    simp only [FreeM.support_liftBind, Set.mem_iUnion, FreeM.support_map, ih', Set.mem_image,
      Set.mem_range]
    constructor
    · rintro ⟨b, _, ⟨p, rfl⟩, rfl⟩
      exact ⟨⟨b, p⟩, rfl⟩
    · rintro ⟨⟨b, p⟩, rfl⟩
      exact ⟨b, _, ⟨p, rfl⟩, rfl⟩

/-- Run a handler under a budget: a call at `a` that would bring the amount spent above `B`
fails; any other call is charged and run. -/
def withBudget [Monad m] [Add ω] [LE ω] [DecidableLE ω] (h : Handler m P) (c : P.A → ω)
    (B : ω) : Handler (StateT ω (OptionT m)) P :=
  fun a s => if s + c a ≤ B then OptionT.lift ((fun b => (b, s + c a)) <$> h a) else failure

/-- A program within budget never meets the budget gate: running it under `withBudget` is running
it under `withCharge`. -/
theorem run_liftM_withBudget_of_isChargeBound [Monad m] [LawfulMonad m] [AddCommMonoid ω]
    [PartialOrder ω] [DecidableLE ω] (h : Handler m P) (c : P.A → ω) {α : Type uB}
    {x : FreeM P α} {B s : ω} (hx : x.IsChargeBound c B s) :
    ((x.liftM (h.withBudget c B)).run s).run = some <$> (x.liftM (h.withCharge c)).run s := by
  induction x using FreeM.rec generalizing s with
  | pure a => simp [FreeM.liftM]
  | liftBind a r ih =>
    change ((h.withBudget c B a >>= fun b => (r b).liftM (h.withBudget c B)).run s).run =
      some <$> (h.withCharge c a >>= fun b => (r b).liftM (h.withCharge c)).run s
    have hs : s + c a ≤ B := hx.1
    simp only [StateT.run_bind, run_withCharge, bind_map_left, map_bind]
    simp only [withBudget, StateT.run, hs, ite_true, OptionT.run_bind_lift, bind_map_left]
    exact bind_congr fun b => ih b (hx.2 b)

/-- Run a handler under a budget with a fallback: a call at `a` that would bring the amount spent
above `B` is answered by `fallback a` without being charged or run; any other call is charged and
run. -/
def withBudgetOr [Monad m] [Add ω] [LE ω] [DecidableLE ω] (h : Handler m P) (c : P.A → ω)
    (B : ω) (fallback : (a : P.A) → P.B a) : Handler (StateT ω m) P :=
  fun a s => if s + c a ≤ B then (fun b => (b, s + c a)) <$> h a else pure (fallback a, s)

/-- A program within budget never reaches the fallback: running it under `withBudgetOr` is running
it under `withCharge`. -/
theorem run_liftM_withBudgetOr_of_isChargeBound [Monad m] [LawfulMonad m] [AddCommMonoid ω]
    [PartialOrder ω] [DecidableLE ω] (h : Handler m P) (c : P.A → ω)
    (fallback : (a : P.A) → P.B a) {α : Type uB} {x : FreeM P α} {B s : ω}
    (hx : x.IsChargeBound c B s) :
    (x.liftM (h.withBudgetOr c B fallback)).run s = (x.liftM (h.withCharge c)).run s := by
  induction x using FreeM.rec generalizing s with
  | pure a => rfl
  | liftBind a r ih =>
    change ((h.withBudgetOr c B fallback a >>= fun b =>
        (r b).liftM (h.withBudgetOr c B fallback)).run s) =
      (h.withCharge c a >>= fun b => (r b).liftM (h.withCharge c)).run s
    have hs : s + c a ≤ B := hx.1
    simp only [StateT.run_bind, run_withCharge]
    simp only [withBudgetOr, StateT.run, hs, ite_true]
    simp only [bind_map_left]
    exact bind_congr fun b => ih b (hx.2 b)

end Instrumentation

/-! ## Value form -/

section Cost

variable {ω : Type w} [AddCommMonoid ω] [CompleteLattice ω] [CanonicallyOrderedAdd ω]

@[simp]
theorem handlerCost_id (d : Q.A → ω) : FreeM.handlerCost d (Handler.id Q) = d :=
  funext fun a => FreeM.cost_lift a

@[simp]
theorem handlerCost_ofLens (l : Lens P Q) (d : Q.A → ω) :
    FreeM.handlerCost d (ofLens l) = d ∘ l.toFunA :=
  funext fun a => by
    change d (l.toFunA a) + ⨆ _ : Q.B (l.toFunA a), (0 : ω) = d (l.toFunA a)
    rw [iSup_zero_eq_zero, add_zero]

omit [CanonicallyOrderedAdd ω] in
@[simp]
theorem handlerCost_sum (f : Handler (FreeM R) P) (g : Handler (FreeM R) Q) (d : R.A → ω) :
    FreeM.handlerCost d (sum f g) = Sum.elim (FreeM.handlerCost d f) (FreeM.handlerCost d g) :=
  funext fun | .inl _ => rfl | .inr _ => rfl

omit [CanonicallyOrderedAdd ω] in
/-- A composite handler costs at most its first stage, charged by the cost of the second. -/
theorem handlerCost_comp_le [IsOrderedAddMonoid ω] (second : Handler (FreeM R) Q)
    (first : Handler (FreeM Q) P) (e : R.A → ω) :
    FreeM.handlerCost e (second.comp first) ≤
      FreeM.handlerCost (FreeM.handlerCost e second) first :=
  fun a => FreeM.cost_liftM_le e second (first a)

end Cost

end Handler

namespace FreeM

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}} {α : Type uB}

/-! ## Stateful handlers implemented by free programs -/

section Stateful

variable {ω : Type w} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] {B s : ω}

/-- **Stateful-handler transfer.** If, from every state, the implementation of each call at `a`
stays within `c a` under the target charge `d`, then from every state the simulation of a
program within budget `B` under `c` stays within `B` under `d`. -/
theorem IsChargeBound.run_liftM {σ : Type uB} (h : Handler (StateT σ (FreeM Q)) P)
    {c : P.A → ω} {d : Q.A → ω} (hstep : ∀ a σ₁, ((h a).run σ₁).IsChargeBound d (c a))
    {x : FreeM P α} (hx : x.IsChargeBound c B s) (σ₀ : σ) :
    ((x.liftM h).run σ₀).IsChargeBound d B s := by
  induction x using FreeM.rec generalizing s σ₀ with
  | pure a => exact hx
  | liftBind a r ih =>
    change ((h a >>= fun b => (r b).liftM h).run σ₀).IsChargeBound d B s
    rw [StateT.run_bind]
    have hh := (hstep a σ₀).add_left s
    rw [add_zero] at hh
    exact hh.bind_of_le hx.1 fun p s' hs' => (ih p.1 (hx.2 p.1) p.2).mono_spent hs'

end Stateful

/-! ## Amortized transfer through stateful handlers -/

section Amortized

variable {ω : Type w} [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω]

/-- **Amortized completed-path transfer.** Suppose a potential `Φ` on the handler state pays for
the target charge of each step: along every completed path of the implementation of a call at `a`
from `σ₁` to `σ₂`, the target charge plus `Φ σ₁` is at most `Φ σ₂` plus the source charge `c a`.
Then every completed path of the simulation from `σ₀` to a final state `σ` refines to a source
path with the same output, and the target charge plus `Φ σ₀` is at most `Φ σ` plus the source
charge. With `c = 0` and `Φ` the size of a cache, this bounds the target calls of a caching
handler by the growth of its cache. -/
theorem Path.exists_run_liftM_amortized {σ : Type uB} (h : Handler (StateT σ (FreeM Q)) P)
    (Φ : σ → ω) {c : P.A → ω} {d : Q.A → ω}
    (hstep : ∀ a σ₁ (r : Path ((h a).run σ₁)),
      Path.charge d _ r + Φ σ₁ ≤ Φ (output _ r).2 + c a)
    (x : FreeM P α) (σ₀ : σ) (q : Path ((x.liftM h).run σ₀)) :
    ∃ p : Path x, (output _ q).1 = output x p ∧
      Path.charge d _ q + Φ σ₀ ≤ Φ (output _ q).2 + Path.charge c x p := by
  induction x using FreeM.rec generalizing σ₀ with
  | pure a => exact ⟨⟨⟩, rfl, le_of_eq ((zero_add (Φ σ₀)).trans (add_zero (Φ σ₀)).symm)⟩
  | liftBind a r ih =>
    change Path (FreeM.bind ((h a).run σ₀) fun p => ((r p.1).liftM h).run p.2) at q
    let sp := Path.splitBind ((h a).run σ₀) (fun p => ((r p.1).liftM h).run p.2) q
    obtain ⟨p, hout, hle⟩ := ih (output _ sp.1).1 (output _ sp.1).2 sp.2
    refine ⟨⟨(output _ sp.1).1, p⟩, ?_, ?_⟩
    · exact (congrArg Prod.fst (Path.output_splitBind ((h a).run σ₀)
        (fun p => ((r p.1).liftM h).run p.2) q)).trans hout
    · have hq := Path.charge_splitBind (c := d) ((h a).run σ₀)
        (fun p => ((r p.1).liftM h).run p.2) q
      have hs := hstep a σ₀ sp.1
      have hout' : output _ q = output _ sp.2 :=
        Path.output_splitBind ((h a).run σ₀) (fun p => ((r p.1).liftM h).run p.2) q
      change Path.charge d _ q + Φ σ₀ ≤ Φ (output _ q).2 + (c a + Path.charge c (r _) p)
      rw [hq, hout']
      calc Path.charge d _ sp.1 + Path.charge d _ sp.2 + Φ σ₀
          = (Path.charge d _ sp.1 + Φ σ₀) + Path.charge d _ sp.2 := by ac_rfl
        _ ≤ (Φ (output _ sp.1).2 + c a) + Path.charge d _ sp.2 := add_le_add hs le_rfl
        _ = (Path.charge d _ sp.2 + Φ (output _ sp.1).2) + c a := by ac_rfl
        _ ≤ (Φ (output _ sp.2).2 + Path.charge c (r _) p) + c a := add_le_add hle le_rfl
        _ = Φ (output _ sp.2).2 + (c a + Path.charge c (r _) p) := by ac_rfl

end Amortized

/-! ## Pausing runs -/

section Pausing

variable {σ : Type*}

/-- Run a program, answering each call through `h` or pausing. On `none` the run stops and returns
the pending call with its continuation, leaving the state unchanged. -/
def runUntil (h : (a : P.A) → σ → FreeM Q (Option (P.B a × σ))) :
    FreeM P α → σ → FreeM Q ((α ⊕ (Σ a : P.A, (P.B a → FreeM P α))) × σ)
  | .pure x, state => .pure (.inl x, state)
  | .liftBind a next, state => FreeM.bind (h a state) fun r =>
      r.elim (.pure (.inr ⟨a, next⟩, state)) fun p => runUntil h (next p.1) p.2

@[simp]
theorem runUntil_pure (h : (a : P.A) → σ → FreeM Q (Option (P.B a × σ))) (x : α) (state : σ) :
    runUntil h (pure x) state = pure (.inl x, state) :=
  rfl

theorem runUntil_liftBind (h : (a : P.A) → σ → FreeM Q (Option (P.B a × σ))) (a : P.A)
    (next : P.B a → FreeM P α) (state : σ) :
    runUntil h (.liftBind a next) state = FreeM.bind (h a state) fun r =>
      r.elim (.pure (.inr ⟨a, next⟩, state)) fun p => runUntil h (next p.1) p.2 :=
  rfl

/-- **Budgets of paused continuations.** If a program is within budget `B` from `s`, every paused
result of a run through `h` returns a call and continuation that are within `B` from an amount
`s' ≥ s` spent along the answered prefix. -/
theorem IsChargeBound.exists_runUntil_paused {ω : Type w} [AddCommMonoid ω] [PartialOrder ω]
    [CanonicallyOrderedAdd ω]
    {h : (a : P.A) → σ → FreeM Q (Option (P.B a × σ))} {c : P.A → ω} {B s : ω} {x : FreeM P α}
    (hx : x.IsChargeBound c B s) {state state' : σ} {a : P.A} {k : P.B a → FreeM P α}
    (hz : (Sum.inr ⟨a, k⟩, state') ∈ FreeM.supp (FreeM.runUntil h x state)) :
    ∃ s', s ≤ s' ∧ (FreeM.liftBind a k).IsChargeBound c B s' := by
  induction x using FreeM.rec generalizing s state with
  | pure v =>
    have hz' : ((Sum.inr ⟨a, k⟩, state') : (α ⊕ (Σ a : P.A, (P.B a → FreeM P α))) × σ) =
      (Sum.inl v, state) := hz
    simp at hz'
  | liftBind a' r ih =>
    change _ ∈ MonadAttach.support (FreeM.bind (h a' state) _) at hz
    rw [FreeM.support_bind] at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨o, -, hz⟩ := hz
    rcases o with _ | ⟨b, state''⟩
    · have hz' : ((Sum.inr ⟨a, k⟩, state') : (α ⊕ (Σ a : P.A, (P.B a → FreeM P α))) × σ) =
          (Sum.inr ⟨a', r⟩, state) := hz
      simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff] at hz'
      obtain ⟨⟨rfl, hk⟩, -⟩ := hz'
      obtain rfl := eq_of_heq hk
      exact ⟨s, le_rfl, hx⟩
    · obtain ⟨s', hs', h'⟩ := ih b (hx.2 b) hz
      exact ⟨s', le_self_add.trans hs', h'⟩

/-- Every paused continuation of a run of a program within budget `B` from `s` is itself within
`B` from `s`: a pause never needs a larger budget than the program it interrupts. -/
theorem IsChargeBound.runUntil_paused {ω : Type w} [AddCommMonoid ω] [PartialOrder ω]
    [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]
    {h : (a : P.A) → σ → FreeM Q (Option (P.B a × σ))} {c : P.A → ω} {B s : ω} {x : FreeM P α}
    (hx : x.IsChargeBound c B s) {state state' : σ} {a : P.A} {k : P.B a → FreeM P α}
    (hz : (Sum.inr ⟨a, k⟩, state') ∈ FreeM.supp (FreeM.runUntil h x state)) :
    (FreeM.liftBind a k).IsChargeBound c B s :=
  let ⟨_, hs, h'⟩ := hx.exists_runUntil_paused hz
  h'.mono_spent hs

variable {ω : Type w} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedCancelAddMonoid ω]

/-- **Amortized budget for a pausing run.** Suppose a nonnegative potential `Φ` on the handler
state pays for the gap between the two charges: whenever the caller can afford a call at `a`, its
step stays within the target budget `T` and ends with `spent + Φ next ≤ spent₀ + Φ now + c a`, where
a pause keeps the state. Then a program within budget `B` from `s` runs within `T` from `e`,
provided `e + Φ state + B ≤ T + s`. The proof cancels the amount spent, so the cost type is a
cancellative ordered monoid such as `ℕ`, `ℤ` or `ι → ℕ`, not `ℕ∞`. -/
theorem IsChargeBound.runUntil {h : (a : P.A) → σ → FreeM Q (Option (P.B a × σ))} (Φ : σ → ω)
    (hΦ : ∀ state, 0 ≤ Φ state) {c : P.A → ω} {d : Q.A → ω} {B T : ω}
    (hstep : ∀ a state e, e + Φ state + c a ≤ T →
      wpFold (OpSpec.budget d T) (h a state)
        (fun r e' => e' + Φ (r.elim state Prod.snd) ≤ e + Φ state + c a) e)
    {x : FreeM P α} {s : ω} (hx : x.IsChargeBound c B s) {e : ω} {state : σ}
    (hT : e + Φ state + B ≤ T + s) : (FreeM.runUntil h x state).IsChargeBound d T e := by
  induction x using FreeM.rec generalizing s e state with
  | pure a =>
    have hs : s ≤ B := hx
    have h₁ : e + Φ state + s ≤ T + s := (add_le_add le_rfl hs).trans hT
    exact (le_add_of_nonneg_right (hΦ state)).trans (le_of_add_le_add_right h₁)
  | liftBind a r ih =>
    have hs : s + c a ≤ B := hx.1
    have hpre : e + Φ state + c a ≤ T := by
      refine le_of_add_le_add_right (a := s) ?_
      calc e + Φ state + c a + s = e + Φ state + (s + c a) := by ac_rfl
        _ ≤ e + Φ state + B := add_le_add le_rfl hs
        _ ≤ T + s := hT
    change wpFold (OpSpec.budget d T) (FreeM.bind (h a state) _) (fun _ s' => s' ≤ T) e
    rw [wpFold_bind']
    refine wpFold_mono (OpSpec.budget_mono d T) (h a state) (fun r e' hr => ?_) e
      (hstep a state e hpre)
    rcases r with _ | ⟨b, state'⟩
    · change e' + Φ state ≤ e + Φ state + c a at hr
      exact (le_add_of_nonneg_right (hΦ state)).trans (hr.trans hpre)
    · change e' + Φ state' ≤ e + Φ state + c a at hr
      refine ih b (hx.2 b) ?_
      calc e' + Φ state' + B ≤ e + Φ state + c a + B := add_le_add hr le_rfl
        _ = e + Φ state + B + c a := by ac_rfl
        _ ≤ T + s + c a := add_le_add hT le_rfl
        _ = T + (s + c a) := add_assoc _ _ _

end Pausing

/-! ## Resource growth in any monad -/

section Growth

variable {m : Type uB → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
  {ω : Type w} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] {B s : ω}

/-- **Resource growth.** If each call at `a` raises a measure `f` of the handler state by at most
`c a`, then on every possible result of running a program within budget `B` from a state whose
measure is at most the amount already spent, the measure is at most `B`. -/
theorem IsChargeBound.le_of_canReturn_run_liftM {σ : Type uB} (h : Handler (StateT σ m) P)
    (f : σ → ω) {c : P.A → ω}
    (hstep : ∀ a σ₁ z, MonadAttach.CanReturn ((h a).run σ₁) z → f z.2 ≤ f σ₁ + c a)
    {x : FreeM P α} (hx : x.IsChargeBound c B s) {σ₀ : σ} (hσ : f σ₀ ≤ s) {z : α × σ}
    (hz : MonadAttach.CanReturn ((x.liftM h).run σ₀) z) : f z.2 ≤ B := by
  induction x using FreeM.rec generalizing s σ₀ with
  | pure a =>
    have := LawfulMonadAttach.eq_of_canReturn_pure (m := m) hz
    subst this
    exact hσ.trans hx
  | liftBind a r ih =>
    change MonadAttach.CanReturn ((h a >>= fun b => (r b).liftM h).run σ₀) z at hz
    rw [StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
    exact ih p.1 (hx.2 p.1) ((hstep a σ₀ p hp).trans (add_le_add hσ le_rfl)) hz

/-- On every possible result of an instrumented run of a program within budget `B`, the amount
spent is at most `B`. -/
theorem IsChargeBound.le_of_canReturn_run_liftM_withCharge {ω : Type uB} [AddCommMonoid ω]
    [PartialOrder ω] [IsOrderedAddMonoid ω] {B s : ω} (h : Handler m P) {c : P.A → ω}
    {x : FreeM P α} (hx : x.IsChargeBound c B s) {z : α × ω}
    (hz : MonadAttach.CanReturn ((x.liftM (h.withCharge c)).run s) z) : z.2 ≤ B := by
  refine hx.le_of_canReturn_run_liftM (h.withCharge c) id (fun a σ₁ z hz => ?_) le_rfl hz
  obtain ⟨b, -, rfl⟩ := LawfulMonadAttach.canReturn_map_imp' hz
  exact le_rfl

end Growth

end FreeM

end PFunctor
