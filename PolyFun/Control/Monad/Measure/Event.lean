/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Lossless
public import ToCslib.MeasureTheory.Measure.Prop
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Event probabilities and failure probabilities of computations

`prEvent mx` is the mass that the successful-output measure of `mx : m Prop` puts on `True`. An
event `p` of the outputs of `mx : m α` is the computation `p <$> mx`, so its probability is
`prEvent (p <$> mx)`; the event laws below are stated in this form. Downstream notation for events
of `do` sequences, such as VCVio's `Pr{…}[…]`, elaborates to it.

`prFail mx` is the probability that `mx` fails or does not terminate: the defect of its
successful-output measure, the mass that never reached a value. It is defined at every universe
and needs no measurable structure on the outputs.

The equations below identify an event with the measure of a set when the event is measurable.
-/

public section

open MeasureTheory
open scoped ENNReal

universe u v

/-- The probability that a computation returns a true proposition: the mass its successful-output
measure puts on `True`. -/
@[expose] noncomputable def prEvent {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    ℝ≥0∞ :=
  evalDist mx {True}

theorem prEvent_def {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    prEvent mx = evalDist mx {True} := rfl

/-- The mass a proposition-valued computation puts on `True` is its event probability, the form
the event laws are stated in. -/
@[simp, grind norm]
theorem evalDist_singleton_true {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    evalDist mx {True} = prEvent mx := rfl

/-- The probability that a computation fails or does not terminate: the defect of its
successful-output measure. The defect is read on the image of the outputs in `PUnit`, so it needs
no measurable structure on the outputs. Under lawful semantics it is the defect of the output
measure in every measurable structure (`prFail_eq_defect`). -/
@[expose] noncomputable def prFail {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type u} (mx : m α) : ℝ≥0∞ :=
  (evalDist ((fun _ ↦ PUnit.unit) <$> mx)).defect

/-! ## Events -/

/-- An event is the true mass of its propositional selector. -/
theorem prEvent_eq_evalDist_map
    {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) :
    prEvent (p <$> mx) = evalDist (p <$> mx) {True} := rfl

/-- A measurable predicate returned by a computation has the probability of its event. -/
theorem prEvent_eq_evalDist {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p : α → Prop)
    (hp : Measurable p) :
    prEvent (p <$> mx) = evalDist mx {x | p x} := by
  rw [prEvent_eq_evalDist_map, evalDist_map_apply mx hp (measurableSet_singleton True)]
  simp

/-- On a discrete output space every predicate is a measurable event. -/
theorem prEvent_eq_evalDist_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p : α → Prop) :
    prEvent (p <$> mx) = evalDist mx {x | p x} :=
  prEvent_eq_evalDist mx p Measurable.of_discrete

/-- Equality to one output has its singleton mass whenever singletons are measurable. -/
theorem prEvent_eq_evalDist_singleton
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] (mx : m α) (a : α) :
    prEvent ((fun x ↦ x = a) <$> mx) = evalDist mx {a} := by
  simpa only [Set.ofPred_eq_eq_singleton] using
    prEvent_eq_evalDist mx (fun x ↦ x = a) (measurableSet_singleton a).mem

/-- A final decidable event has the same success mass whether it is returned as a proposition
or decided to a Boolean; no measurable structure on intermediate values is needed. -/
theorem prEvent_eq_evalDist_decide
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
    prEvent (p <$> mx) = evalDist (do let x ← mx; return decide (p x)) {true} := by
  classical
  calc
    _ = evalDist (p <$> mx) {True} := prEvent_eq_evalDist_map mx p
    _ = evalDist ((fun b : Prop ↦ decide b) <$> (p <$> mx)) {true} := by
      rw [evalDist_map_apply (p <$> mx)
        (Measurable.of_discrete : Measurable fun b : Prop ↦ decide b)
        (measurableSet_singleton true)]
      congr 1
      ext b
      simp
    _ = _ := by
      congr 1
      congr 1
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      apply bind_congr
      intro x
      by_cases hx : p x <;> simp [hx]

/-- Pointwise equivalent predicates have the same probability after a common computation. -/
theorem prEvent_congr
    {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) (h : ∀ x, p x ↔ q x) :
    prEvent (p <$> mx) = prEvent (q <$> mx) := by
  have hpq : p = q := funext fun x ↦ propext (h x)
  rw [hpq]

/-- Measurable predicates agreeing almost everywhere have equal event probabilities. -/
theorem prEvent_congr_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (h : ∀ᵐ x ∂evalDist mx, p x ↔ q x) :
    prEvent (p <$> mx) = prEvent (q <$> mx) := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_congr (h.mono fun _ hx ↦ propext hx)

/-- An event that never occurs has probability zero. -/
theorem prEvent_eq_zero_of_forall_not
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) (h : ∀ x, ¬p x) :
    prEvent (p <$> mx) = 0 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  simp [h]

/-- An impossible final observation has zero mass, including after a failed computation. -/
@[simp↓ high, grind norm↓]
theorem prEvent_false
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) : prEvent ((fun _ ↦ False) <$> mx) = 0 :=
  prEvent_eq_zero_of_forall_not mx (fun _ ↦ False) (fun _ ↦ id)

/-- Almost-everywhere implication bounds probabilities of measurable events. -/
theorem prEvent_mono_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (hpq : ∀ᵐ x ∂evalDist mx, p x → q x) :
    prEvent (p <$> mx) ≤ prEvent (q <$> mx) := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_mono_ae hpq

/-- Implication between events bounds their probabilities on a discrete output space. -/
theorem prEvent_mono_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    prEvent (p <$> mx) ≤ prEvent (q <$> mx) := by
  rw [prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  exact measure_mono (Set.ofPred_subset_ofPred.mpr hpq)

/-- Implication between final events bounds their probabilities without a measurable-space
argument on the intermediate values. -/
theorem prEvent_mono
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    prEvent (p <$> mx) ≤ prEvent (q <$> mx) := by
  let obs : α → Prop × Prop := fun x ↦ (p x, q x)
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  exact prEvent_mono_ae mx p q (measurable_fst.comp hobs) (measurable_snd.comp hobs)
    (Filter.Eventually.of_forall hpq)

/-- An observed bind integrates the event probability of each measurable continuation.
Only the common draw needs a selected measurable space; the continuation is observed in `Prop`.
-/
theorem prEvent_bind_eq_lintegral
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [MeasurableSpace α] (mx : m α) (f : α → m β) (p : β → Prop)
    (hf : Measurable fun x ↦ evalDist (p <$> f x)) :
    prEvent (p <$> (mx >>= f)) = ∫⁻ x, prEvent (p <$> f x) ∂evalDist mx := by
  rw [prEvent_def, map_bind, evalDist_bind _ _ hf,
    Measure.bind_apply (measurableSet_singleton True) hf.aemeasurable]
  rfl

/-- A bind of event computations integrates the continuation's event over a measurable source. -/
theorem prEvent_bind
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (f : α → m Prop)
    (hf : Measurable fun x ↦ evalDist (f x)) :
    prEvent (mx >>= f) = ∫⁻ x, prEvent (f x) ∂evalDist mx := by
  rw [prEvent_def, evalDist_bind _ _ hf,
    Measure.bind_apply (measurableSet_singleton True) hf.aemeasurable]
  rfl

/-- A bind of event computations integrates the continuation's event over a discrete source. -/
theorem prEvent_bind_of_discrete
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx : m α) (f : α → m Prop) :
    prEvent (mx >>= f) = ∫⁻ x, prEvent (f x) ∂evalDist mx :=
  prEvent_bind mx f Measurable.of_discrete

/-- A discrete common draw discharges the observed continuation's measurability. -/
theorem prEvent_bind_eq_lintegral_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (f : α → m β) (p : β → Prop) :
    prEvent (p <$> (mx >>= f)) = ∫⁻ x, prEvent (p <$> f x) ∂evalDist mx :=
  prEvent_bind_eq_lintegral mx f p Measurable.of_discrete

/-- AE equality of measurable observed continuation probabilities gives equality after a draw. -/
theorem prEvent_bind_congr_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β γ : Type} [MeasurableSpace α] (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop)
    (hf : Measurable fun x ↦ evalDist (p <$> f x))
    (hg : Measurable fun x ↦ evalDist (q <$> g x))
    (h : ∀ᵐ x ∂evalDist mx, prEvent (p <$> f x) = prEvent (q <$> g x)) :
    prEvent (p <$> (mx >>= f)) = prEvent (q <$> (mx >>= g)) := by
  rw [prEvent_bind_eq_lintegral mx f p hf, prEvent_bind_eq_lintegral mx g q hg]
  exact lintegral_congr_ae h

/-- Pointwise equality of observed continuation probabilities gives equality after a common
draw. Neither the draw nor the continuation outputs need a measurable-space argument. -/
theorem prEvent_bind_congr
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β γ : Type} (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop)
    (h : ∀ x, prEvent (p <$> f x) = prEvent (q <$> g x)) :
    prEvent (p <$> (mx >>= f)) = prEvent (q <$> (mx >>= g)) := by
  let obs : α → Measure Prop × Measure Prop :=
    fun x ↦ (evalDist (p <$> f x), evalDist (q <$> g x))
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  exact prEvent_bind_congr_ae mx f g p q (measurable_fst.comp hobs)
    (measurable_snd.comp hobs) (Filter.Eventually.of_forall h)

/-- An event of two successive draws, which may read both outputs, integrates the event of the
second draw over a discrete first draw. -/
theorem prEvent_bind_bind_eq_lintegral_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (f : α → m β) (p : α → β → Prop) :
    prEvent (mx >>= fun x ↦ p x <$> f x) = ∫⁻ x, prEvent (p x <$> f x) ∂evalDist mx := by
  have key := prEvent_bind_eq_lintegral_of_discrete mx (fun x ↦ (fun y ↦ p x y) <$> f x) id
  simp only [id_map, Functor.map_map, id_eq] at key
  exact key

/-- An output map composes the final event with that map. -/
@[grind norm]
theorem prEvent_map
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    {α β : Type} (mx : m α) (f : α → β) (p : β → Prop) :
    prEvent (p <$> (f <$> mx)) = prEvent ((fun x ↦ p (f x)) <$> mx) := by
  rw [Functor.map_map]

/-- An injective map preserves the mass of each output. -/
theorem prEvent_map_injective
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    {α β : Type} (mx : m α) {f : α → β} (hf : Function.Injective f) (x : α) :
    prEvent ((fun y ↦ y = f x) <$> (f <$> mx)) = prEvent ((fun y ↦ y = x) <$> mx) := by
  rw [prEvent_map]
  exact prEvent_congr mx _ _ fun _ ↦ hf.eq_iff

/-- An event of a conditional computation is the conditional event. -/
theorem prEvent_ite {m : Type → Type v} [EvalDistSemantics m] (c : Prop) [Decidable c]
    (mx my : m Prop) : prEvent (if c then mx else my) = if c then prEvent mx else prEvent my := by
  split_ifs <;> rfl

/-- An event of a dependent conditional computation is the dependent conditional event. -/
theorem prEvent_dite {m : Type → Type v} [EvalDistSemantics m] (c : Prop) [Decidable c]
    (mx : c → m Prop) (my : ¬c → m Prop) :
    prEvent (if h : c then mx h else my h) = if h : c then prEvent (mx h) else prEvent (my h) := by
  split_ifs <;> rfl

/-- A returned proposition has probability one exactly when it holds. -/
@[simp, grind =]
theorem prEvent_pure_prop
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    (P : Prop) [Decidable P] :
    prEvent (pure P : m Prop) = if P then 1 else 0 := by
  rw [prEvent_def, evalDist_pure]
  by_cases h : P <;> simp [h]

/-- Returned propositions are ordered by implication. A continuation that destructures its input
with `match` keeps its event in this form, below a bind. -/
theorem prEvent_pure_mono
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {P Q : Prop} (h : P → Q) :
    prEvent (pure P : m Prop) ≤ prEvent (pure Q : m Prop) := by
  classical
  rw [prEvent_pure_prop, prEvent_pure_prop]
  split_ifs <;> simp_all

/-- An event of a pure computation has probability one exactly when it holds. -/
@[grind =]
theorem prEvent_pure
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type} (a : α) (p : α → Prop) [Decidable (p a)] :
    prEvent (p <$> (pure a : m α)) = if p a then 1 else 0 := by
  rw [map_pure, prEvent_pure_prop]

/-- After a draw from a finite type, an event is the finite sum of the draw's point masses times
the conditional event probabilities. -/
theorem prEvent_bind_eq_sum_fintype
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [Fintype α] (mx : m α) (f : α → m β) (p : β → Prop) :
    prEvent (p <$> (mx >>= f)) =
      ∑ a, prEvent ((fun x ↦ x = a) <$> mx) * prEvent (p <$> f a) := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, MeasureTheory.lintegral_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, prEvent_eq_evalDist_singleton]

/-- After a draw from a countable type, an event is the sum of the draw's point masses times the
conditional event probabilities. -/
theorem prEvent_bind_eq_tsum_of_countable
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [Countable α] (mx : m α) (f : α → m β) (p : β → Prop) :
    prEvent (p <$> (mx >>= f)) =
      ∑' a, prEvent ((fun x ↦ x = a) <$> mx) * prEvent (p <$> f a) := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, MeasureTheory.lintegral_countable']
  refine tsum_congr fun a => ?_
  rw [mul_comm, ← prEvent_eq_evalDist_singleton]

/-- Two output maps of one computation: an event of the first map is at most an event of the
second when, at every output, the first event implies the second. -/
theorem prEvent_map_le_map
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {γ α β : Type} (mx : m γ) (f : γ → α) (g : γ → β) (p : α → Prop) (q : β → Prop)
    (h : ∀ x, p (f x) → q (g x)) :
    prEvent (p <$> (f <$> mx)) ≤ prEvent (q <$> (g <$> mx)) := by
  rw [prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ h

/-- An event of a pure computation is at most an event of another pure computation when the
first event implies the second. -/
theorem prEvent_pure_le_pure
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} (a : α) (b : β) (p : α → Prop) (q : β → Prop) (h : p a → q b) :
    prEvent (p <$> (pure a : m α)) ≤ prEvent (q <$> (pure b : m β)) := by
  simpa only [map_pure] using
    prEvent_map_le_map (pure () : m Unit) (fun _ ↦ a) (fun _ ↦ b) p q fun _ ↦ h

/-- Events of independent draws have the product of their probabilities. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_bind_and
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} (mx : m α) (my : m β) (p : α → Prop) (q : β → Prop) :
    prEvent (mx >>= fun x ↦ (fun y ↦ p x ∧ q y) <$> my) =
      prEvent (p <$> mx) * prEvent (q <$> my) := by
  calc
    _ = prEvent ((fun z ↦ z.1 ∧ z.2) <$> (do
          let x ← p <$> mx
          let y ← q <$> my
          return (x, y))) := by
      simp only [map_bind, bind_map_left, bind_pure_comp, Functor.map_map]
    _ = ((evalDist (p <$> mx)).prod (evalDist (q <$> my))) ({True} ×ˢ {True}) := by
      rw [prEvent_eq_evalDist_of_discrete, evalDist_pair]
      congr 1
      ext z
      simp [Prod.ext_iff, eq_iff_iff]
    _ = _ := by
      rw [Measure.prod_prod]
      rfl

/-- Every event probability is at most one. -/
@[simp]
theorem prEvent_le_one {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    prEvent mx ≤ 1 :=
  evalDist_apply_le_one _ _

/-- Every event probability is finite. -/
@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem prEvent_ne_top {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    prEvent mx ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one mx)

/-- Every event probability is finite. -/
@[simp]
theorem prEvent_lt_top {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    prEvent mx < ⊤ :=
  (prEvent_ne_top mx).lt_top

/-- The event `True` has the successful mass of the computation, in any measurable structure on
its outputs. -/
theorem prEvent_true_eq_evalDist_apply_univ
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} [MeasurableSpace α]
    (mx : m α) : prEvent ((fun _ ↦ True) <$> mx) = evalDist mx Set.univ := by
  rw [prEvent_eq_evalDist_map,
    evalDist_map_apply mx measurable_const (measurableSet_singleton True)]
  simp

/-- A prefix whose result is unused scales the event by its successful mass. -/
@[simp]
theorem prEvent_bind_const
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α) (my : m Prop) :
    prEvent (mx >>= fun _ ↦ my) = prEvent ((fun _ ↦ True) <$> mx) * prEvent my := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_true_eq_evalDist_apply_univ]
  change evalDist (mx >>= fun _ ↦ my) {True} = evalDist mx Set.univ * evalDist my {True}
  rw [evalDist_bind_const, Measure.smul_apply, smul_eq_mul]

/-- A true constant event after a lossless draw has probability one. -/
theorem prEvent_const_of_lossless
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α : Type}
    (mx : m α) (hmx : prEvent ((fun _ ↦ True) <$> mx) = 1) {c : Prop} (hc : c) :
    prEvent ((fun _ ↦ c) <$> mx) = 1 := by
  rw [← hmx]
  exact prEvent_congr mx _ _ fun _ ↦ by simp [hc]

/-- A false constant event has probability zero. -/
theorem prEvent_const_of_not
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    (mx : m α) {c : Prop} (hc : ¬ c) : prEvent ((fun _ ↦ c) <$> mx) = 0 :=
  prEvent_eq_zero_of_forall_not mx _ fun _ ↦ hc

/-! ## Failure

`prFail mx` is the mass the successful-output measure of `mx` is missing: the probability that
`mx` fails or does not terminate. It needs no measurable structure on the outputs. -/

section prFail

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m] {α : Type u}

@[simp]
theorem prFail_le_one (mx : m α) : prFail mx ≤ 1 := tsub_le_self

@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem prFail_ne_top (mx : m α) : prFail mx ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prFail_le_one mx)

/-- A pure computation never fails. -/
@[simp, grind =]
theorem prFail_pure [LawfulMonad m] [LawfulPureEvalDistSemantics m] (a : α) :
    prFail (pure a : m α) = 0 := by
  simp [prFail, Measure.defect]

/-- The failure probability of a branch is that of the branch taken. -/
@[simp]
theorem prFail_ite (c : Prop) [Decidable c] (mx my : m α) :
    prFail (if c then mx else my) = if c then prFail mx else prFail my := by
  split_ifs <;> rfl

/-- Mapping the outputs does not change the failure probability. -/
@[simp, grind =]
theorem prFail_map [LawfulMonad m] {β : Type u} (f : α → β) (mx : m α) :
    prFail (f <$> mx) = prFail mx := by
  rw [prFail, prFail, Functor.map_map]

/-- Under lawful semantics, the failure probability is the defect of the output measure, in every
measurable structure on the outputs. -/
theorem prFail_eq_defect [LawfulMonad m] [LawfulEvalDistSemantics m] [MeasurableSpace α]
    (mx : m α) : prFail mx = (evalDist mx).defect := by
  rw [prFail, evalDist_map mx measurable_const, Measure.defect, Measure.defect,
    Measure.map_apply measurable_const MeasurableSet.univ, Set.preimage_univ]

/-- The failure probability is the mass missing from the output measure. -/
theorem prFail_eq_one_sub_evalDist_univ [LawfulMonad m] [LawfulEvalDistSemantics m]
    [MeasurableSpace α] (mx : m α) : prFail mx = 1 - evalDist mx Set.univ :=
  prFail_eq_defect mx

/-- A lossless semantics never fails. -/
theorem prFail_eq_zero_of_lossless [LosslessEvalDistSemantics m] (mx : m α) : prFail mx = 0 := by
  rw [prFail, Measure.defect, measure_univ, tsub_self]

end prFail

/-! ### Failure and the event `True` -/

section prFailEvent

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α : Type}

/-- The failure probability is one minus the probability of the event `True`. -/
theorem prFail_def (mx : m α) : prFail mx = 1 - prEvent ((fun _ ↦ True) <$> mx) := by
  let : MeasurableSpace α := ⊤
  rw [prFail_eq_one_sub_evalDist_univ, prEvent_true_eq_evalDist_apply_univ]

/-- Success and failure masses add up to one. -/
@[simp]
theorem prEvent_true_add_prFail (mx : m α) : prEvent ((fun _ ↦ True) <$> mx) + prFail mx = 1 := by
  rw [prFail_def]
  exact add_tsub_cancel_of_le (prEvent_le_one _)

/-- Failure and success masses add up to one. -/
@[simp]
theorem prFail_add_prEvent_true (mx : m α) : prFail mx + prEvent ((fun _ ↦ True) <$> mx) = 1 := by
  rw [add_comm, prEvent_true_add_prFail]

/-- A computation never fails exactly when it succeeds with probability one. -/
theorem prFail_eq_zero_iff (mx : m α) : prFail mx = 0 ↔ prEvent ((fun _ ↦ True) <$> mx) = 1 := by
  rw [prFail_def, tsub_eq_zero_iff_le]
  exact ⟨fun h ↦ le_antisymm (prEvent_le_one _) h, fun h ↦ h.ge⟩

/-- A computation always fails exactly when it succeeds with probability zero. -/
theorem prFail_eq_one_iff (mx : m α) : prFail mx = 1 ↔ prEvent ((fun _ ↦ True) <$> mx) = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [prFail_def, h, tsub_zero]⟩
  rw [prFail_def] at h
  by_contra hne
  exact (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hne).ne h

end prFailEvent
