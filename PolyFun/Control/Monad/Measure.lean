/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.MeasureTheory.Measure.Subprobability

/-!
# Measure-valued evaluation and its composition laws

`EvalDistSemantics m` interprets each computation `mx : m α` as a subprobability measure
`evalDist mx` on its successful outputs. The mass that the measure is missing is the probability
that `mx` fails or does not terminate.

`LawfulPureEvalDistSemantics` supplies the Dirac equation independently of bind, while
`LawfulEvalDistSemantics` adds the measurable-bind equation. Measurable spaces and
continuations are explicit; discrete source spaces discharge continuation measurability without
constraining the result space.

The final section states the laws of the expectation `∫⁻ r, r ∂evalDist (f <$> mx)` of a scalar
observation `f`, all but one of which place no measurable space on the observed type.
-/

public section

open MeasureTheory

universe u v

/-- A measure-valued subprobability semantics for a type constructor. -/
class EvalDistSemantics (m : Type u → Type v) where
  /-- Interpret a computation as its measure of successful outputs. -/
  denote : {α : Type u} → [MeasurableSpace α] → m α → Measure α
  /-- Successful output mass is at most one. -/
  apply_univ_le_one : ∀ {α : Type u} [MeasurableSpace α] (mx : m α),
    denote mx Set.univ ≤ 1

/-- The measure of successful outputs produced by `mx`. -/
@[expose, reducible, inline]
noncomputable def evalDist {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : Measure α :=
  EvalDistSemantics.denote mx

/-- Denotation commutes with conditional choice of a computation. -/
theorem evalDist_ite {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (p : Prop) [Decidable p] (mx my : m α) :
    evalDist (if p then mx else my) = if p then evalDist mx else evalDist my := by
  by_cases h : p <;> simp [h]

/-- Denotation commutes with dependent conditional choice of a computation. -/
theorem evalDist_dite {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (p : Prop) [Decidable p]
    (mx : p → m α) (my : ¬p → m α) :
    evalDist (if h : p then mx h else my h) =
      if h : p then evalDist (mx h) else evalDist (my h) := by
  by_cases h : p <;> simp [h]

/-- The mass of an event commutes with conditional choice of a computation. -/
@[simp high]
theorem evalDist_ite_apply {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (p : Prop) [Decidable p]
    (mx my : m α) (s : Set α) :
    evalDist (if p then mx else my) s = if p then evalDist mx s else evalDist my s := by
  by_cases h : p <;> simp [h]

/-- Event mass commutes with dependent conditional choice of a computation. -/
@[simp high]
theorem evalDist_dite_apply {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (p : Prop) [Decidable p]
    (mx : p → m α) (my : ¬p → m α) (s : Set α) :
    evalDist (if h : p then mx h else my h) s =
      if h : p then evalDist (mx h) s else evalDist (my h) s := by
  by_cases h : p <;> simp [h]

theorem evalDist_apply_univ_le_one {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : evalDist mx Set.univ ≤ 1 :=
  EvalDistSemantics.apply_univ_le_one mx

/-- Every computation denotation is a subprobability measure. -/
instance evalDist.instIsSubprobabilityMeasure {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : IsSubprobabilityMeasure (evalDist mx) :=
  ⟨evalDist_apply_univ_le_one mx⟩

/-- No event of a computation has mass above one. -/
@[simp]
theorem evalDist_apply_le_one {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) (s : Set α) : evalDist mx s ≤ 1 :=
  MeasureTheory.measure_le_one (evalDist mx) s

/-- A measure-valued semantics sends `pure` to a Dirac measure. This law is separate from the
bind law because a semantics can preserve pure even when continuous effects prevent a global
measurability proof for arbitrary bind continuations. -/
class LawfulPureEvalDistSemantics (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : Prop where
  /-- `pure` denotes a Dirac measure. -/
  denote_pure {α : Type u} [MeasurableSpace α] (x : α) :
    evalDist (pure x : m α) = Measure.dirac x

/-- A measure-valued semantics also respects measurable `bind` in the Giry monad. -/
class LawfulEvalDistSemantics (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : Prop extends LawfulPureEvalDistSemantics m where
  /-- Monadic bind denotes Giry bind whenever its measure-valued continuation is measurable. -/
  denote_bind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      (mx : m α) (f : α → m β) (hf : Measurable fun x => evalDist (f x)) :
    evalDist (mx >>= f) = Measure.bind (evalDist mx) fun x => evalDist (f x)

@[simp]
theorem evalDist_pure {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] {α : Type u} [MeasurableSpace α] (x : α) :
    evalDist (pure x : m α) = Measure.dirac x :=
  LawfulPureEvalDistSemantics.denote_pure x

instance evalDist.instIsProbabilityMeasurePure {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulPureEvalDistSemantics m] {α : Type u}
    [MeasurableSpace α] (x : α) : IsProbabilityMeasure (evalDist (pure x : m α)) := by
  rw [evalDist_pure]
  infer_instance

theorem evalDist_bind {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (f : α → m β) (hf : Measurable fun x => evalDist (f x)) :
    evalDist (mx >>= f) = Measure.bind (evalDist mx) fun x => evalDist (f x) :=
  LawfulEvalDistSemantics.denote_bind mx f hf

/-- On a discrete source type, every measure-valued continuation is measurable. -/
theorem evalDist_bind_of_discrete {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β) :
    evalDist (mx >>= f) = Measure.bind (evalDist mx) fun x => evalDist (f x) :=
  evalDist_bind mx f Measurable.of_discrete

/-- Almost-everywhere equal measurable continuation measures give equal composed measures. -/
theorem evalDist_bind_congr_ae {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (f g : α → m β)
    (hf : Measurable fun x ↦ evalDist (f x)) (hg : Measurable fun x ↦ evalDist (g x))
    (h : (fun x ↦ evalDist (f x)) =ᵐ[evalDist mx] fun x ↦ evalDist (g x)) :
    evalDist (mx >>= f) = evalDist (mx >>= g) := by
  rw [evalDist_bind mx f hf, evalDist_bind mx g hg]
  exact Measure.bind_congr_right h

/-- Pointwise equality of continuation measures gives equality after a common bind. No
measurable structure is required on the unobserved intermediate type: the common continuation
measure supplies its observation's pullback measurable space. -/
theorem evalDist_bind_congr {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace β]
    (mx : m α) (f g : α → m β) (h : ∀ x, evalDist (f x) = evalDist (g x)) :
    evalDist (mx >>= f) = evalDist (mx >>= g) := by
  let : MeasurableSpace α := MeasurableSpace.comap (fun x ↦ evalDist (f x)) inferInstance
  have hf : Measurable fun x ↦ evalDist (f x) := comap_measurable _
  have hg : Measurable fun x ↦ evalDist (g x) := by simpa only [← h] using hf
  exact evalDist_bind_congr_ae mx f g hf hg (Filter.Eventually.of_forall h)

/-- `Functor.map` along a measurable function denotes the pushforward measure. -/
theorem evalDist_map {m : Type u → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) {f : α → β} (hf : Measurable f) : evalDist (f <$> mx) = (evalDist mx).map f := by
  have hd : Measurable fun x => evalDist (pure (f x) : m β) := by
    simp only [evalDist_pure]
    exact Measure.measurable_dirac.comp hf
  rw [map_eq_bind_pure_comp, evalDist_bind mx (pure ∘ f) hd]
  simp only [Function.comp_apply, evalDist_pure]
  exact Measure.bind_dirac_eq_map (evalDist mx) hf

/-- On a discrete source type, every `Functor.map` denotes a pushforward. -/
theorem evalDist_map_of_discrete {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → β) :
    evalDist (f <$> mx) = (evalDist mx).map f :=
  evalDist_map mx Measurable.of_discrete

/-- A mapped computation assigns a measurable set the mass of its preimage. -/
theorem evalDist_map_apply {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [MeasurableSpace β] (mx : m α) {f : α → β} (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) : evalDist (f <$> mx) s = evalDist mx (f ⁻¹' s) := by
  rw [evalDist_map mx hf, Measure.map_apply hf hs]

/-- On a discrete source type, a mapped computation assigns a measurable set the mass of its
preimage. -/
theorem evalDist_map_apply_of_discrete {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → β) {s : Set β}
    (hs : MeasurableSet s) : evalDist (f <$> mx) s = evalDist mx (f ⁻¹' s) :=
  evalDist_map_apply mx Measurable.of_discrete hs

/-- Independent sequential draws denote Mathlib's product measure. -/
theorem evalDist_pair {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (my : m β) :
    evalDist (do let x ← mx; let y ← my; return (x, y)) = (evalDist mx).prod (evalDist my) := by
  have h (x : α) :
      evalDist (my >>= fun y => pure (x, y)) = (evalDist my).map (Prod.mk x) := by
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      (evalDist_map my (measurable_const.prodMk measurable_id :
        Measurable (Prod.mk x : β → α × β)))
  rw [evalDist_bind mx _ (by simpa only [h] using
    (Measurable.map_prodMk_left (ν := evalDist my)))]
  simp only [h, Measure.prod_eq_of_sfinite]

/-- A constant continuation scales the continuation's measure by the success mass
(`Measure.bind_const`). -/
@[simp]
theorem evalDist_bind_const {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (my : m β) :
    evalDist (mx >>= fun _ => my) = evalDist mx Set.univ • evalDist my := by
  rw [evalDist_bind mx (fun _ => my) measurable_const, Measure.bind_const]

/-- A constant map denotes the success mass at a point (`Measure.map_const`). -/
@[simp]
theorem evalDist_map_const {m : Type u → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (c : β) :
    evalDist ((fun _ => c) <$> mx) = evalDist mx Set.univ • Measure.dirac c := by
  rw [evalDist_map mx measurable_const, Measure.map_const]

/-- An AE-measurable valuation of composed outputs satisfies the integral tower law. -/
theorem lintegral_evalDist_bind_of_aemeasurable {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β)
    (hf : Measurable fun x ↦ evalDist (f x)) {g : β → ENNReal}
    (hg : AEMeasurable g (evalDist (mx >>= f))) :
    ∫⁻ y, g y ∂evalDist (mx >>= f) = ∫⁻ x, ∫⁻ y, g y ∂evalDist (f x) ∂evalDist mx := by
  rw [evalDist_bind mx f hf] at hg ⊢
  exact Measure.lintegral_bind hf.aemeasurable hg

/-- Integrating a bind first integrates each measurable continuation, then its common draw. -/
theorem lintegral_evalDist_bind {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [MeasurableSpace β] (mx : m α) (f : α → m β)
    (hf : Measurable fun x ↦ evalDist (f x)) {g : β → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂evalDist (mx >>= f) = ∫⁻ x, ∫⁻ y, g y ∂evalDist (f x) ∂evalDist mx := by
  exact lintegral_evalDist_bind_of_aemeasurable mx f hf hg.aemeasurable

/-- For a discrete common draw, the tower law needs no continuation measurability proof. -/
theorem lintegral_evalDist_bind_of_discrete {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β)
    {g : β → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂evalDist (mx >>= f) = ∫⁻ x, ∫⁻ y, g y ∂evalDist (f x) ∂evalDist mx :=
  lintegral_evalDist_bind mx f .of_discrete hg

/-- An AE-measurable valuation of a measurable output map integrates the composed functional. -/
theorem lintegral_evalDist_map_of_aemeasurable {m : Type u → Type v} [Monad m]
    [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] (mx : m α)
    {f : α → β} (hf : Measurable f) {g : β → ENNReal}
    (hg : AEMeasurable g (evalDist (f <$> mx))) :
    ∫⁻ y, g y ∂evalDist (f <$> mx) = ∫⁻ x, g (f x) ∂evalDist mx := by
  rw [evalDist_map mx hf] at hg ⊢
  exact lintegral_map' hg hf.aemeasurable

/-- Integrating a measurable output map integrates the composed functional. -/
theorem lintegral_evalDist_map {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [MeasurableSpace β] (mx : m α) {f : α → β} (hf : Measurable f) {g : β → ENNReal}
    (hg : Measurable g) : ∫⁻ y, g y ∂evalDist (f <$> mx) = ∫⁻ x, g (f x) ∂evalDist mx := by
  exact lintegral_evalDist_map_of_aemeasurable mx hf hg.aemeasurable

/-- On discrete source and target spaces, output-map integration needs no measurability
proofs. -/
@[simp high]
theorem lintegral_evalDist_map_of_discrete {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (mx : m α) (f : α → β) (g : β → ENNReal) :
    ∫⁻ y, g y ∂evalDist (f <$> mx) = ∫⁻ x, g (f x) ∂evalDist mx :=
  lintegral_evalDist_map mx .of_discrete .of_discrete

/-- Adding to a natural-valued observation adds the constant scaled by the successful output
mass. The observed computation's intermediate result needs no measurable-space instance. -/
@[simp high + 1]
theorem lintegral_evalDist_map_add_nat {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    (mx : m α) (f : α → ℕ) (c : ℕ) :
    (∫⁻ n, (n : ENNReal) ∂evalDist ((fun x ↦ f x + c) <$> mx)) =
      (∫⁻ n, (n : ENNReal) ∂evalDist (f <$> mx)) + c * evalDist (f <$> mx) Set.univ := by
  rw [show (fun x ↦ f x + c) <$> mx =
    (fun n : ℕ ↦ n + c) <$> (f <$> mx) by simp [Functor.map_map],
    lintegral_evalDist_map_of_discrete]
  simp [lintegral_add_right]

/-- Adding a fixed natural to an observed count scales that increment by successful mass.
The curried addition form supplies a binder-free pattern for `grind`. -/
@[grind =]
theorem lintegral_evalDist_map_const_add_nat {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    (mx : m α) (f : α → ℕ) (c : ℕ) :
    (∫⁻ n, (n : ENNReal) ∂evalDist (Nat.add c <$> (f <$> mx))) =
      (∫⁻ n, (n : ENNReal) ∂evalDist (f <$> mx)) + c * evalDist (f <$> mx) Set.univ := by
  simpa only [Functor.map_map, Function.comp_def, Nat.add_eq, Nat.add_comm] using
    lintegral_evalDist_map_add_nat mx f c

/-- The success mass of a bind is the integral of its continuation's success mass. -/
theorem evalDist_bind_apply_univ {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (f : α → m β) (hf : Measurable fun x ↦ evalDist (f x)) :
    evalDist (mx >>= f) Set.univ = ∫⁻ x, evalDist (f x) Set.univ ∂evalDist mx := by
  rw [evalDist_bind mx f hf, Measure.bind_apply MeasurableSet.univ hf.aemeasurable]

/-- A measurable map preserves the successful-output mass. -/
theorem evalDist_map_apply_univ {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) {f : α → β} (hf : Measurable f) :
    evalDist (f <$> mx) Set.univ = evalDist mx Set.univ := by
  rw [evalDist_map_apply mx hf MeasurableSet.univ, Set.preimage_univ]

/-- Implication between Boolean results bounds their pure successful masses. -/
theorem evalDist_pure_apply_le_of_imp {m : Type → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    (a b : Bool) (h : a = true → b = true) :
    evalDist (pure a : m Bool) {true} ≤ evalDist (pure b : m Bool) {true} := by
  cases a <;> cases b <;> simp_all

/-- A pure Boolean result covered by either of two results has mass bounded by their sum. -/
theorem evalDist_pure_apply_le_add_of_imp {m : Type → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    (a b c : Bool) (h : a = true → b = true ∨ c = true) :
    evalDist (pure a : m Bool) {true} ≤
      evalDist (pure b : m Bool) {true} + evalDist (pure c : m Bool) {true} := by
  cases a <;> cases b <;> cases c <;> simp_all

/-!
## Expectations of a scalar observation

For `f : α → ℝ≥0∞`, `∫⁻ r, r ∂evalDist (f <$> mx)` is the expectation of `f` under the
successful-output measure `evalDist mx`. It is not normalised by the success mass
`evalDist mx Set.univ`: failure contributes zero, so for a constant observation `c` it is
`c * evalDist mx Set.univ`. Only `ℝ≥0∞` needs a measurable space in this form, so the laws below
place none on `α`, except `lintegral_id_evalDist_map`, which identifies the expectation with
`∫⁻ x, f x ∂evalDist mx` at a discrete measurable space on `α`.
-/

/-- The expectation of a scalar observation is its integral against the computation's
successful-output measure, at any discrete measurable space on the output type. -/
theorem lintegral_id_evalDist_map {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (mx : m α) (f : α → ENNReal) :
    ∫⁻ r, r ∂evalDist (f <$> mx) = ∫⁻ x, f x ∂evalDist mx :=
  lintegral_evalDist_map mx .of_discrete measurable_id

/-- A pointwise bound on a scalar observation bounds its expectation. -/
theorem lintegral_id_evalDist_map_le_of_le {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    {f : α → ENNReal} {c : ENNReal} (hf : ∀ x, f x ≤ c) :
    ∫⁻ r, r ∂evalDist (f <$> mx) ≤ c := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map]
  calc ∫⁻ x, f x ∂evalDist mx ≤ ∫⁻ _, c ∂evalDist mx := lintegral_mono hf
    _ = c * evalDist mx Set.univ := lintegral_const c
    _ ≤ c := mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)

/-- The expectation of a scalar observation is monotone in the observation. -/
theorem lintegral_id_evalDist_map_mono {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    {f g : α → ENNReal} (hfg : ∀ x, f x ≤ g x) :
    ∫⁻ r, r ∂evalDist (f <$> mx) ≤ ∫⁻ r, r ∂evalDist (g <$> mx) := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
  exact lintegral_mono hfg

/-- The expectation of a sum of scalar observations is the sum of their expectations. -/
theorem lintegral_id_evalDist_map_add {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    (f g : α → ENNReal) :
    ∫⁻ r, r ∂evalDist ((fun x ↦ f x + g x) <$> mx) =
      (∫⁻ r, r ∂evalDist (f <$> mx)) + ∫⁻ r, r ∂evalDist (g <$> mx) := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map, lintegral_id_evalDist_map,
    lintegral_add_left Measurable.of_discrete]

/-- The constant-zero observation has expectation zero. -/
@[simp]
theorem lintegral_id_evalDist_map_zero {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α) :
    ∫⁻ r, r ∂evalDist ((fun _ ↦ (0 : ENNReal)) <$> mx) = 0 :=
  le_zero_iff.mp (lintegral_id_evalDist_map_le_of_le mx fun _ ↦ le_rfl)

/-- The expectation of a scalar observation of a bind is the expectation, under the head's
measure, of the observation's expectation under the continuation. -/
theorem lintegral_id_evalDist_map_bind {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type} (mx : m α)
    (g : α → m β) (f : β → ENNReal) :
    ∫⁻ r, r ∂evalDist (f <$> (mx >>= g)) =
      ∫⁻ r, r ∂evalDist ((fun x ↦ ∫⁻ r, r ∂evalDist (f <$> g x)) <$> mx) := by
  let _ : MeasurableSpace α := ⊤
  let _ : MeasurableSpace β := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map,
    lintegral_evalDist_bind_of_discrete mx g (g := f) Measurable.of_discrete]
  simp only [lintegral_id_evalDist_map]
