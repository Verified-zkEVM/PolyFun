/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Algebra.Relational
public import PolyFun.Control.Monad.Measure.Countable
public import PolyFun.Control.Monad.Measure.Relational.Bind

/-!
# Coupling semantics as a relational monad algebra

Under semantics with countable support (`CountableEvalDist`), pointwise conditional couplings
compose by bind with no measurability obligation (`ExpectationWP.relWP_bind_of_countableEvalDist`).
Each output measure concentrates on a countable set, where the choice of witnesses is almost
everywhere measurable. Countable support also supplies the diagonal
coupling, so equality in distribution is exactly the equality coupling
(`evalDistEq_iff_relWP_eq`).

`ExpectationWP.couplingAlgebra m₁ m₂` packages `ExpectationWP.RelWP`, read in the discrete
structures on the outputs, as a `MAlgRelOrdered m₁ m₂ Prop`. PolyFun's generic relational rules,
such as `MAlgRelOrdered.triple_bind`, then apply to coupling judgments. It is a definition, not an
instance, following the policy of `PolyFun.Control.Monad.Algebra`: install it locally or at a
verification boundary. Its carrier `Prop` places the outputs in `Type`.
-/

public section

open MeasureTheory

universe u v w₁ w₂

namespace ExpectationWP

/-- Under countable semantics, a computation is related to itself by equality in every structure
with measurable singletons. -/
theorem relWP_refl_of_countableEvalDist {m : Type u → Type w₁} [EvalDistSemantics m]
    [CountableEvalDist m] {α : Type u} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : m α) : RelWP mx mx (· = ·) :=
  let ⟨_, hs, h⟩ := CountableEvalDist.exists_countable_ae_mem mx
  relWP_refl_of_ae_mem_countable mx hs h

/-- Under lawful countable semantics, pointwise relational judgments compose by bind in discrete
structures on the intermediate outputs. No conditional coupling family needs to be supplied. -/
theorem relWP_bind_of_countableEvalDist {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulEvalDistSemantics m₁] [LawfulEvalDistSemantics m₂]
    [CountableEvalDist m₁] [CountableEvalDist m₂]
    {α γ : Type u} {β δ : Type v} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] [DiscreteMeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] [MeasurableSpace δ] [MeasurableSingletonClass δ]
    {mx : m₁ α} {my : m₂ β} {f : α → m₁ γ} {g : β → m₂ δ} {S : γ → δ → Prop}
    (h : RelWP mx my fun a b ↦ RelWP (f a) (g b) S) : RelWP (mx >>= f) (my >>= g) S := by
  obtain ⟨s, hs, hmx⟩ := CountableEvalDist.exists_countable_ae_mem mx
  obtain ⟨t, ht, hmy⟩ := CountableEvalDist.exists_countable_ae_mem my
  choose p hp hfp using fun a ↦ CountableEvalDist.exists_countable_ae_mem (f a)
  choose q hq hgq using fun b ↦ CountableEvalDist.exists_countable_ae_mem (g b)
  rw [RelWP, evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  exact CouplingPost.bind_of_countable_of_ae_mem h hs ht
    (hs.biUnion fun a _ ↦ hp a) (ht.biUnion fun b _ ↦ hq b) hmx hmy .of_discrete .of_discrete
    (fun a ha ↦ (hfp a).mono fun _ hx ↦ Set.mem_biUnion ha hx)
    (fun b hb ↦ (hgq b).mono fun _ hy ↦ Set.mem_biUnion hb hy)
    fun _ _ _ _ hab ↦ hab

/-- The coupling semantics of two lawful countable semantics, read in the discrete structures on
the outputs, as an ordered relational monad algebra. -/
@[expose, instance_reducible]
noncomputable def couplingAlgebra (m₁ : Type → Type w₁) (m₂ : Type → Type w₂)
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulEvalDistSemantics m₁] [LawfulEvalDistSemantics m₂]
    [CountableEvalDist m₁] [CountableEvalDist m₂] : MAlgRelOrdered m₁ m₂ Prop where
  rwp {α β} mx my R :=
    letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤
    RelWP mx my R
  rwp_pure {α β} a b R :=
    letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤
    propext (relWP_pure_pure_iff a b R)
  rwp_mono {α β} _ _ _ _ hpost h :=
    letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤
    relWP_mono h hpost
  rwp_bind_le {α β γ δ} _ _ _ _ _ h :=
    letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤
    letI : MeasurableSpace γ := ⊤; letI : MeasurableSpace δ := ⊤
    relWP_bind_of_countableEvalDist h

/-- The relational weakest precondition of `couplingAlgebra` is `RelWP` in the discrete
structures. -/
theorem couplingAlgebra_relWP_iff {m₁ : Type → Type w₁} {m₂ : Type → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulEvalDistSemantics m₁] [LawfulEvalDistSemantics m₂]
    [CountableEvalDist m₁] [CountableEvalDist m₂] {α β : Type} (mx : m₁ α) (my : m₂ β)
    (R : α → β → Prop) :
    (letI := couplingAlgebra m₁ m₂; MAlgRelOrdered.RelWP mx my R) ↔
      (letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤; RelWP mx my R) :=
  Iff.rfl

end ExpectationWP

/-- Under lawful semantics with countable support, equality in distribution is the existence of a
coupling concentrated on the diagonal, in any discrete structure on the outputs. -/
theorem evalDistEq_iff_relWP_eq {m : Type → Type w₁} {m' : Type → Type w₂} [Monad m] [Monad m']
    [LawfulMonad m] [LawfulMonad m'] [EvalDistSemantics m] [EvalDistSemantics m']
    [LawfulEvalDistSemantics m] [LawfulEvalDistSemantics m'] [CountableEvalDist m] {α : Type}
    {_ : MeasurableSpace α} [DiscreteMeasurableSpace α] {mx : m α} {my : m' α} :
    EvalDistEq mx my ↔ ExpectationWP.RelWP mx my (· = ·) := by
  refine ⟨fun h ↦ ?_, EvalDistEq.of_relWP_eq⟩
  obtain ⟨_, hs, hmx⟩ := CountableEvalDist.exists_countable_ae_mem mx
  exact h.relWP_eq_of_ae_mem_countable hs hmx
