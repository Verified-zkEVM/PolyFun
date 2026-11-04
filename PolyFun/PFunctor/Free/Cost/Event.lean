/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Path.Charge

/-!
# Charges that depend on answers, and watermarks

A charge `c : P.A → ω` is paid when a call is made. Some costs depend on the answer: the size of
returned data, a gas price that depends on whether a key was already warm, a basis that grows with
each reply. An **event charge** `e : P.Idx → ω` prices a call together with its answer.

* `Path.chargeEvent e x p` is the event charge of a completed path. It is the additive valuation of
  the path's event trace (`chargeEvent_eq_traceList_charge`), and an ordinary charge is the event
  charge that ignores the answer (`chargeEvent_fst`).
* `IsEventChargeBound x e B s` is the budget reading: after each answer, the amount spent stays at
  most `B`. It is the fold of `OpSpec.eventBudget e B`. A charge that dominates the event charge
  gives an event bound (`IsEventChargeBound.of_isChargeBound`), event bounds bound every completed
  path (`chargeEvent_le_of_isEventChargeBound`), and they add under sequencing
  (`IsEventChargeBound.bind`).

With signed prices, the amount spent along a path can rise and fall. The **watermark** of a
sequence of prices is the pair of its highest prefix sum (`peak`, at least `0`) and its total
(`net`). Watermarks form a monoid under concatenation, which is not commutative, and the watermark
of a path is the path charge into that monoid. A budget with signed prices is exactly a bound on
the peak of every completed path (`isChargeBound_iff_forall_peak_le`, when every call has an
answer): this is how peak space, stack depth or live width are bounded by `+1`/`-1` prices.
-/

@[expose] public section

universe uA uB v w

namespace PFunctor

namespace OpSpec

variable {P : PFunctor.{uA, uB}}

/-- The budget reading of an event charge: after the answer `b` to a call at `a`, the amount spent
`s + e ⟨a, b⟩` is at most `B`, and the continuation starts from that amount. -/
def eventBudget {ω : Type w} [Add ω] [LE ω] (e : P.Idx → ω) (B : ω) : OpSpec P (ω → Prop) :=
  fun a k s => ∀ b, s + e ⟨a, b⟩ ≤ B ∧ k b (s + e ⟨a, b⟩)

end OpSpec

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v} {ω : Type w}

/-! ## Event charges of completed paths -/

namespace Path

/-- The total event charge along a completed path: each call is priced with its answer. -/
def chargeEvent [Add ω] [Zero ω] (e : P.Idx → ω) : (x : FreeM P α) → Path x → ω
  | .pure _, _ => 0
  | .liftBind a next, ⟨answer, tail⟩ => e ⟨a, answer⟩ + chargeEvent e (next answer) tail

variable {e : P.Idx → ω}

/-- A charge that ignores the answer is an ordinary charge. -/
theorem chargeEvent_fst [Add ω] [Zero ω] (c : P.A → ω) (x : FreeM P α) (p : Path x) :
    chargeEvent (fun i => c i.1) x p = charge c x p := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    exact congrArg (c a + ·) (ih b p)

/-- The event charge of a path is the additive valuation of its event trace. -/
theorem chargeEvent_eq_traceList_charge [AddMonoid ω] (x : FreeM P α) (p : Path x) :
    chargeEvent e x p = TraceList.charge e (trace x p) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    exact congrArg (e ⟨a, b⟩ + ·) (ih b p)

end Path

/-! ## Event budgets -/

section Bound

variable [Add ω] [LE ω] [Zero ω]

/-- With `s` already spent, after every answer of `x` the amount spent stays at most `B`, where the
answer `b` to a call at `a` costs `e ⟨a, b⟩`, and every leaf is reached within `B`. -/
def IsEventChargeBound (x : FreeM P α) (e : P.Idx → ω) (B : ω) (spent : ω := 0) : Prop :=
  wpFold (OpSpec.eventBudget e B) x (fun _ s => s ≤ B) spent

variable {e : P.Idx → ω} {B s : ω}

@[simp]
theorem isEventChargeBound_pure_iff (a : α) :
    IsEventChargeBound (pure a : FreeM P α) e B s ↔ s ≤ B :=
  Iff.rfl

theorem isEventChargeBound_liftBind_iff (a : P.A) (r : P.B a → FreeM P α) :
    IsEventChargeBound (FreeM.liftBind a r) e B s ↔
      ∀ b, s + e ⟨a, b⟩ ≤ B ∧ IsEventChargeBound (r b) e B (s + e ⟨a, b⟩) :=
  Iff.rfl

@[simp]
theorem isEventChargeBound_lift_bind_iff' {α : Type uB} (a : P.A) (r : P.B a → FreeM P α) :
    IsEventChargeBound (Bind.bind (α := no_index (P.B a)) (FreeM.lift a) r) e B s ↔
      ∀ b, s + e ⟨a, b⟩ ≤ B ∧ IsEventChargeBound (r b) e B (s + e ⟨a, b⟩) :=
  Iff.rfl

end Bound

section Ordered

variable [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] {e : P.Idx → ω} {B s : ω}

/-- A charge paid when the call is made, at least the event charge of every answer, gives an event
bound. -/
theorem IsEventChargeBound.of_isChargeBound {c : P.A → ω} (he : ∀ i, e i ≤ c i.1)
    {x : FreeM P α} (h : x.IsChargeBound c B s) : x.IsEventChargeBound e B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h
  | liftBind a r ih =>
    intro b
    have hb : s + e ⟨a, b⟩ ≤ s + c a := add_le_add le_rfl (he ⟨a, b⟩)
    exact ⟨hb.trans h.1, ih b (IsChargeBound.mono_spent (h.2 b) hb)⟩

omit [IsOrderedAddMonoid ω] in
/-- An event bound bounds the event charge of every completed path. -/
theorem chargeEvent_le_of_isEventChargeBound {x : FreeM P α} (h : x.IsEventChargeBound e B s)
    (p : Path x) : s + Path.chargeEvent e x p ≤ B := by
  induction x using FreeM.rec generalizing s with
  | pure a =>
    change s + 0 ≤ B
    rw [add_zero]
    exact h
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    change s + (e ⟨a, b⟩ + Path.chargeEvent e (r b) p) ≤ B
    rw [← add_assoc]
    exact ih b (h b).2 p

omit [IsOrderedAddMonoid ω] in
/-- Event bounds are monotone in the budget. -/
theorem IsEventChargeBound.mono {x : FreeM P α} {B' : ω} (h : x.IsEventChargeBound e B s)
    (hB : B ≤ B') : x.IsEventChargeBound e B' s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h.trans hB
  | liftBind a r ih => exact fun b => ⟨(h b).1.trans hB, ih b (h b).2⟩

/-- Spending more earlier keeps less room, so a bound from a larger amount spent holds from a
smaller one. -/
theorem IsEventChargeBound.mono_spent {x : FreeM P α} {s' : ω} (h : x.IsEventChargeBound e B s)
    (hs : s' ≤ s) : x.IsEventChargeBound e B s' := by
  induction x using FreeM.rec generalizing s s' with
  | pure a => exact hs.trans h
  | liftBind a r ih =>
    intro b
    have hb : s' + e ⟨a, b⟩ ≤ s + e ⟨a, b⟩ := add_le_add hs le_rfl
    exact ⟨hb.trans (h b).1, ih b (h b).2 hb⟩

end Ordered

section Canonical

variable [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]
  {e : P.Idx → ω} {B₁ B₂ s : ω}

omit [CanonicallyOrderedAdd ω] in
/-- Raising the spent amount and the budget together preserves an event bound. -/
theorem IsEventChargeBound.add_left {x : FreeM P α} (h : x.IsEventChargeBound e B₁ s) (t : ω) :
    x.IsEventChargeBound e (t + B₁) (t + s) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact add_le_add le_rfl h
  | liftBind a r ih =>
    intro b
    rw [add_assoc]
    exact ⟨add_le_add le_rfl (h b).1, ih b (h b).2⟩

/-- **Event budgets add under sequencing.** -/
theorem IsEventChargeBound.bind {γ : Type v} {x : FreeM P α} {f : α → FreeM P γ}
    (hx : x.IsEventChargeBound e B₁ s) (hf : ∀ a, (f a).IsEventChargeBound e B₂) :
    (FreeM.bind x f).IsEventChargeBound e (B₁ + B₂) s := by
  induction x using FreeM.rec generalizing s with
  | pure a =>
    have := (hf a).add_left s
    rw [add_zero] at this
    exact this.mono (add_le_add hx le_rfl)
  | liftBind a r ih =>
    intro b
    exact ⟨((hx b).1).trans le_self_add, ih b (hx b).2⟩

end Canonical

end FreeM

/-! ## Watermarks -/

/-- The watermark of a sequence of signed prices: its highest prefix sum, counting the empty
prefix, and its total. -/
@[ext]
structure Watermark (ω : Type w) where
  /-- The highest prefix sum, at least `0`. -/
  peak : ω
  /-- The total. -/
  net : ω

namespace Watermark

variable {ω : Type w}

instance [Zero ω] : Zero (Watermark ω) := ⟨⟨0, 0⟩⟩

/-- Concatenation: the second part's peak counts from the first part's total. -/
instance [Add ω] [Max ω] : Add (Watermark ω) :=
  ⟨fun x y => ⟨max x.peak (x.net + y.peak), x.net + y.net⟩⟩

/-- The watermark of a single price. -/
def of [Zero ω] [Max ω] (a : ω) : Watermark ω := ⟨max 0 a, a⟩

@[simp] theorem zero_peak [Zero ω] : (0 : Watermark ω).peak = 0 := rfl
@[simp] theorem zero_net [Zero ω] : (0 : Watermark ω).net = 0 := rfl
@[simp] theorem add_peak [Add ω] [Max ω] (x y : Watermark ω) :
    (x + y).peak = max x.peak (x.net + y.peak) := rfl
@[simp] theorem add_net [Add ω] [Max ω] (x y : Watermark ω) : (x + y).net = x.net + y.net := rfl
@[simp] theorem of_peak [Zero ω] [Max ω] (a : ω) : (of a).peak = max 0 a := rfl
@[simp] theorem of_net [Zero ω] [Max ω] (a : ω) : (of a).net = a := rfl

end Watermark

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v} {ω : Type w} [AddCommGroup ω] [LinearOrder ω]
  [IsOrderedAddMonoid ω] {c : P.A → ω} {B s : ω}

omit [IsOrderedAddMonoid ω] in
/-- The peak of a path's watermark is at least `0`: it counts the empty prefix. -/
theorem Path.zero_le_peak (x : FreeM P α) (p : Path x) :
    0 ≤ (Path.charge (Watermark.of ∘ c) x p).peak := by
  induction x using FreeM.rec with
  | pure a => exact le_rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    change 0 ≤ max (max 0 (c a)) (c a + (Path.charge (Watermark.of ∘ c) (r b) p).peak)
    exact le_max_of_le_left (le_max_left _ _)

/-- The peak of a path's watermark from `s` spent: the highest amount spent along the path. -/
private theorem add_peak_liftBind (a : P.A) (r : P.B a → FreeM P α) (b : P.B a) (p : Path (r b)) :
    s + (Path.charge (Watermark.of ∘ c) (FreeM.liftBind a r) ⟨b, p⟩).peak =
      max (max s (s + c a)) ((s + c a) + (Path.charge (Watermark.of ∘ c) (r b) p).peak) := by
  change s + max (max 0 (c a)) (c a + _) = _
  rw [← max_add_add_left, ← max_add_add_left, add_zero, add_assoc]

/-- **A signed budget is a bound on the peak.** Starting within budget, a program stays within
budget exactly when the watermark of every completed path peaks within it, when every reachable
call has an answer. With prices `+1` on allocation and `-1` on release, this bounds peak space. -/
theorem isChargeBound_iff_forall_peak_le {x : FreeM P α} (hx : x.ProgramProgress) :
    (s ≤ B ∧ x.IsChargeBound c B s) ↔
      ∀ p : Path x, s + (Path.charge (Watermark.of ∘ c) x p).peak ≤ B := by
  induction x using FreeM.rec generalizing s with
  | pure a =>
    refine ⟨fun h _ => ?_, fun h => ⟨?_, ?_⟩⟩
    · simpa using h.1
    · simpa using h PUnit.unit
    · simpa using h PUnit.unit
  | liftBind a r ih =>
    obtain ⟨⟨b₀⟩, hr⟩ := hx
    refine ⟨fun ⟨hs, h⟩ p => ?_, fun h => ?_⟩
    · rcases p with ⟨b, p⟩
      rw [add_peak_liftBind]
      exact max_le (max_le hs h.1) ((ih b (hr b)).1 ⟨h.1, h.2 b⟩ p)
    · obtain ⟨p₀⟩ := (hr b₀).nonempty_path
      have h₀ := h ⟨b₀, p₀⟩
      rw [add_peak_liftBind] at h₀
      have hs : s ≤ B := (le_max_left _ _).trans ((le_max_left _ _).trans h₀)
      have hca : s + c a ≤ B := (le_max_right _ _).trans ((le_max_left _ _).trans h₀)
      refine ⟨hs, hca, fun b => ((ih b (hr b)).2 fun p => ?_).2⟩
      have hb := h ⟨b, p⟩
      rw [add_peak_liftBind] at hb
      exact (le_max_right _ _).trans hb

end FreeM

end PFunctor
