/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Events.Exception
public import PolyFun.ITree.WP.Bind
public import PolyFun.ITree.WP.Bisim

/-! # Weakest preconditions of interaction trees

Each example pins one behaviour of the total and partial readings:
* silent divergence reads `⊥` totally and `⊤` partially;
* silent steps are transparent;
* without monotonicity the total reading can exceed the partial one;
* a loop that queries forever fails totally and succeeds partially;
* a thrown exception is a miracle for the demonic spec;
* divergence on either side of a `bind` propagates;
* a loop whose only extra structure is silent steps terminates.
-/

@[expose] public section

namespace PolyFunTest.ITreeWPExamples

open ITree PFunctor

/-- One operation, a coin flip answered by a Boolean. -/
@[reducible] def CoinE : PFunctor.{0, 0} where
  A := PUnit
  B _ := Bool

/-- Flip the coin once. -/
def flip : ITree CoinE Bool :=
  lift PUnit.unit

theorem coin_mono : (OpSpec.demonic CoinE).Monotone :=
  OpSpec.demonic_mono

/-! ## Silent divergence and silent steps -/

/-- Total correctness rejects silent divergence. Swapping the fixed points breaks this. -/
example : ¬ wpTotal (OpSpec.demonic CoinE) (diverge : ITree CoinE Nat) (fun _ => True) := by
  simp

/-- Partial correctness accepts silent divergence, whatever the postcondition. -/
example : wpPartial (OpSpec.demonic CoinE) (diverge : ITree CoinE Nat) (fun _ => False) := by
  simp

/-- Silent steps are transparent. Reading a silent step as anything but its continuation breaks
this. -/
example (r : Nat) (post : Nat → Prop) :
    wpTotal (OpSpec.demonic CoinE) (step (step (ITree.pure r))) post ↔ post r := by
  rw [wpTotal_step coin_mono, wpTotal_step coin_mono, wpTotal_pure coin_mono]

/-! ## Monotonicity is needed -/

/-- A spec that negates its continuation. It is not monotone. -/
def negSpec : OpSpec PFunctor.y.{0, 0} Prop :=
  fun _ k => ¬ k PUnit.unit

/-- The tree that queries forever. -/
def queries : ITree PFunctor.y.{0, 0} PUnit :=
  corec (fun _ : PUnit.{1} => ⟨.query PUnit.unit, fun _ => PUnit.unit⟩) PUnit.unit

theorem shape'_queries : shape' queries = ⟨.query PUnit.unit, fun _ => queries⟩ :=
  shape'_corec_eq _ _ rfl

/-- Without monotonicity the total reading can exceed the partial one, so
`ITree.wpTotal_le_wpPartial` needs its hypothesis. Every prefixed point holds at `queries`, and no
postfixed point does. -/
example :
    ¬ (wpTotal negSpec queries (fun _ => False) ≤ wpPartial negSpec queries (fun _ => False)) := by
  have htot : wpTotal negSpec queries (fun _ => False) := by
    rw [wpTotal_eq_iInf]
    simp only [iInf_Prop_eq]
    intro X hX
    have h := hX queries
    rw [wpStepFun, shape'_queries] at h
    change ¬ X queries → X queries at h
    exact Classical.byContradiction fun hn => hn (h hn)
  have hpar : ¬ wpPartial negSpec queries (fun _ => False) := by
    rw [wpPartial_eq_iSup]
    simp only [iSup_Prop_eq]
    rintro ⟨X, hX, hq⟩
    have h := hX queries
    rw [wpStepFun, shape'_queries] at h
    change X queries → ¬ X queries at h
    exact h hq hq
  exact fun hle => hpar (hle htot)

/-! ## Loops -/

/-- The body of `forever flip`: flip once, then continue. -/
def flipLoop (_ : PUnit.{1}) : ITree CoinE (PUnit.{1} ⊕ Nat) :=
  ITree.bind flip fun _ => ITree.pure (Sum.inl PUnit.unit)

/-- Flipping forever never returns, so it fails total correctness, by the loop upper bound. -/
example (post : Nat → Prop) :
    ¬ wpTotal (OpSpec.demonic CoinE) (forever flip : ITree CoinE Nat) post := by
  have h := wpTotal_iter_le coin_mono flipLoop post (B := fun _ => False) (fun _ => by
      rw [flipLoop, wpTotal_bind' coin_mono, flip, wpTotal_lift coin_mono]
      simp [wpTotal_pure coin_mono, OpSpec.demonic]) PUnit.unit
  exact h

/-- Flipping forever satisfies every postcondition partially, by the loop invariant `True`. -/
example (post : Nat → Prop) :
    wpPartial (OpSpec.demonic CoinE) (forever flip : ITree CoinE Nat) post :=
  le_wpPartial_iter coin_mono flipLoop post (I := fun _ => True) (fun _ => by
      rw [flipLoop, wpPartial_bind' coin_mono, flip, wpPartial_lift coin_mono]
      simp [wpPartial_pure coin_mono, OpSpec.demonic]) PUnit.unit trivial

/-- Count down by silent steps. -/
def countdown : Nat → ITree CoinE (Nat ⊕ PUnit.{1})
  | 0 => ITree.pure (Sum.inr PUnit.unit)
  | n + 1 => step (ITree.pure (Sum.inl n))

/-- A loop whose only extra structure is silent steps terminates, by the variant rule. Reading a
silent step as `⊥` breaks this. -/
example (post : PUnit.{1} → Prop) (h : post PUnit.unit) (n : Nat) :
    wpTotal (OpSpec.demonic CoinE) (iter countdown n) post :=
  le_wpTotal_iter coin_mono countdown post wellFounded_lt (I := fun _ => True) (fun j => by
    cases j with
    | zero => simpa [countdown, wpTotal_pure coin_mono] using h
    | succ j => simp [countdown, wpTotal_step coin_mono, wpTotal_pure coin_mono]) n trivial

/-! ## Exceptions -/

/-- A thrown exception never resumes, so the demonic spec, which asks something of every answer,
accepts it whatever the postcondition: a miracle. -/
example (e : Nat) :
    wpTotal (OpSpec.demonic (ExceptE.{0, 0} Nat)) (ExceptE.throw e : ITree _ Unit)
      (fun _ => False) := by
  rw [ExceptE.throw, wpTotal_query OpSpec.demonic_mono]
  exact fun b => b.elim

/-- The spec that rejects every throw, as Aeneas reads Rust failure. -/
def rejectSpec : OpSpec (ExceptE.{0, 0} Nat) Prop :=
  fun _ _ => False

/-- A spec that rejects throwing reads a thrown exception as `⊥`. -/
example (e : Nat) :
    ¬ wpTotal rejectSpec (ExceptE.throw e : ITree _ Unit) (fun _ => True) := by
  rw [ExceptE.throw, wpTotal_query (fun _ _ _ _ => le_rfl)]
  exact id

/-! ## Sequencing -/

/-- Divergence before a continuation fails total correctness. -/
example (k : Nat → ITree CoinE Nat) (post : Nat → Prop) :
    ¬ wpTotal (OpSpec.demonic CoinE) (ITree.bind diverge k) post := by
  rw [wpTotal_bind' coin_mono]
  simp

/-- Divergence after a query passes partial correctness. -/
example (post : Nat → Prop) :
    wpPartial (OpSpec.demonic CoinE)
      (ITree.bind flip fun _ => (diverge : ITree CoinE Nat)) post := by
  rw [wpPartial_bind' coin_mono, flip, wpPartial_lift coin_mono]
  simp [OpSpec.demonic]

/-- The bind law holds across universes. -/
example (t : ITree CoinE Bool) (k : Bool → ITree CoinE (ULift.{1} Nat))
    (post : ULift.{1} Nat → Prop) :
    wpTotal (OpSpec.demonic CoinE) (ITree.bind t k) post =
      wpTotal (OpSpec.demonic CoinE) t fun b => wpTotal (OpSpec.demonic CoinE) (k b) post :=
  wpTotal_bind' coin_mono k post t

/-- Weakly bisimilar trees have the same readings. -/
example (t : ITree CoinE Nat) (post : Nat → Prop) :
    wpTotal (OpSpec.demonic CoinE) (step t) post = wpTotal (OpSpec.demonic CoinE) t post :=
  WeakBisim.wpTotal_eq coin_mono (step_weakBisim t)

end PolyFunTest.ITreeWPExamples
