/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Family
public import PolyFun.Realizability.Quantitative.Resource
public import PolyFun.PFunctor.Free.Sigma
public import Mathlib.Data.Nat.Size

/-!
# Uniform pure families at a unary parameter boundary

One fixed initialization and readout machine for a packed pure Boolean family induces a
nonuniform family with constant description size. Injective pinned encodings then transfer the
finite-description counting separation to the uniform notion. The theorem concerns immediately
returning programs; interactive implementation requires a separate operational linker.
-/

public section

open PFunctor PFunctor.DynSystem.DynComputation Filter
open ComplexityBackends.CslibSingleTape

namespace ComplexityBackends.CslibSingleTape.Uniform

/-! ## The unary-parameter boundary -/

/-- A parameter in unary, a separator, then a payload. The `1^n` convention as an encoding. -/
@[expose] def unaryTag (n : ℕ) (s : List Bool) : List Bool := List.replicate n true ++ false :: s

theorem takeWhile_unaryTag (n : ℕ) (s : List Bool) :
    (unaryTag n s).takeWhile (fun b ↦ b) = List.replicate n true := by
  unfold unaryTag
  rw [List.takeWhile_append_of_pos (fun a ha ↦ by simpa using (List.mem_replicate.mp ha).2),
    List.takeWhile_cons_of_neg (by simp), List.append_nil]

theorem unaryTag_inj {n m : ℕ} {s t : List Bool} (h : unaryTag n s = unaryTag m t) :
    n = m ∧ s = t := by
  have hn : n = m := by
    have := congrArg (fun l ↦ (l.takeWhile (fun b ↦ b)).length) h
    simpa [takeWhile_unaryTag] using this
  subst hn
  refine ⟨rfl, ?_⟩
  unfold unaryTag at h
  exact (List.cons.inj (List.append_cancel_left h)).2

/-- Packed inputs: the canonical bitvector encoding tagged with its parameter in unary. -/
@[expose] noncomputable def unaryInput : (Σ n, BitVec n) → List Bool
  | ⟨n, x⟩ => unaryTag n (BitEncFam.bitVecX.enc n x)

theorem unaryInput_injective : Function.Injective unaryInput := by
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  obtain ⟨rfl, hs⟩ := unaryTag_inj h
  rw [BitEncFam.bitVecX.enc_injective n hs]

/-- Packed outputs: one Boolean tagged with its parameter in unary. -/
@[expose] def unaryOutput : (Σ _ : ℕ, Bool) → List Bool
  | ⟨n, b⟩ => unaryTag n [b]

theorem unaryOutput_injective : Function.Injective unaryOutput := by
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  obtain ⟨rfl, hs⟩ := unaryTag_inj h
  simp only [List.cons.injEq, and_true] at hs
  rw [hs]

variable {p : ℕ → PFunctor.{0, 0}}

/-- The packed head encoding: a tag bit, then the output or the position encoding. -/
@[expose] def headEnc (posEnc : (PFunctor.sigma p).A → List Bool) :
    (Σ _ : ℕ, Bool) ⊕ (PFunctor.sigma p).A → List Bool :=
  Sum.elim (fun o ↦ false :: unaryOutput o) (fun q ↦ true :: posEnc q)

theorem headEnc_injective {posEnc : (PFunctor.sigma p).A → List Bool}
    (hpos : Function.Injective posEnc) : Function.Injective (headEnc posEnc) := by
  rintro (o | q) (o' | q') h <;> simp only [headEnc, Sum.elim_inl, Sum.elim_inr,
    List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and] at h
  · rw [unaryOutput_injective h.2]
  · rw [hpos h.2]

/-- Unary framing charges the whole parameter and a separator. -/
@[simp] theorem length_unaryTag (n : ℕ) (s : List Bool) :
    (unaryTag n s).length = n + 1 + s.length := by simp [unaryTag]; omega

/-- The packed Boolean output includes its unary parameter, separator and payload bit. -/
@[simp] theorem length_unaryOutput (n : ℕ) (b : Bool) :
    (unaryOutput ⟨n, b⟩).length = n + 2 := by simp [unaryOutput, unaryTag]

/-! ## Uniform certificates for pure packed families -/

/-- A single machine, with single CSLib codes for `init` and `head`, implementing the packed
pure family `⟨n, x⟩ ↦ ⟨n, f n x⟩` at the unary-parameter boundary. The boundary (`posEnc`) is a
parameter, never an existential. -/
structure UniformPureWitness (p : ℕ → PFunctor.{0, 0}) (posEnc : (PFunctor.sigma p).A → List Bool)
    (f : (n : ℕ) → BitVec n → Bool) where
  /-- The single computation shared across all parameters. -/
  machine : DynSystem.DynComputation (PFunctor.sigma p) (Σ n, BitVec n) (Σ _ : ℕ, Bool)
  /-- Agreement with the packed pure family. -/
  implements : machine.Implements (FreeM.packFamily fun n v ↦ FreeM.pure (f n v))
  /-- The fixed hidden-state encoding. -/
  state : machine.State → List Bool
  /-- One initialization code at the unary input boundary. -/
  initCode : EncPolyTime unaryInput state machine.init
  /-- One readout code at the tagged output boundary. -/
  headCode : EncPolyTime state (headEnc posEnc) machine.head

/-- A packed polynomial program witness at this fixed unary boundary supplies the two
codes needed by the pure-family bridge. The run certificate retains its separate meaning. -/
noncomputable def UniformPureWitness.ofProgramWitness
    {p : ℕ → PFunctor.{0, 0}} [DecidableEq (PFunctor.sigma p).A]
    (posEnc : (PFunctor.sigma p).A → List Bool)
    (idxEnc : (PFunctor.sigma p).Idx → List Bool)
    (f : (n : ℕ) → BitVec n → Bool) {label : Type*}
    (contract : ResponseResourceContract Backend.quantitative
      (⟨unaryInput, unaryOutput, posEnc, idxEnc⟩ : Boundary Backend.encodingStepClass
        (PFunctor.sigma p) (Σ n, BitVec n) (Σ _ : ℕ, Bool)).interface label)
    (w : PolynomialProgramWitness Backend.quantitative
      ⟨unaryInput, unaryOutput, posEnc, idxEnc⟩ contract
      (FreeM.packFamily fun n v ↦ FreeM.pure (f n v))) : UniformPureWitness p posEnc f where
  machine := w.realization.machine
  implements := w.implements
  state := w.realization.state
  initCode := w.realization.initCode
  headCode := w.realization.headCode

variable {posEnc : (PFunctor.sigma p).A → List Bool} {f : (n : ℕ) → BitVec n → Bool}

theorem UniformPureWitness.head_init (w : UniformPureWitness p posEnc f) (n : ℕ) (x : BitVec n) :
    w.machine.head (w.machine.init ⟨n, x⟩) = Sum.inl ⟨n, f n x⟩ := by
  refine head_init_eq_of_implements_pure w.machine (g := fun v ↦ ⟨v.1, f v.1 v.2⟩) ?_ ⟨n, x⟩
  intro v
  rcases v with ⟨n, x⟩
  simpa using w.implements ⟨n, x⟩

/-- **Uniform ⇒ nonuniform, member by member.** The same two machines, recoded to the fibre. -/
noncomputable def UniformPureWitness.toRealizer (w : UniformPureWitness p posEnc f) (n : ℕ) :
    EncPolyTime (fun x : BitVec n ↦ unaryInput ⟨n, x⟩) (headEnc posEnc)
      (fun x ↦ Sum.inl ⟨n, f n x⟩) :=
  ((w.initCode.recode (fun x : BitVec n ↦ (⟨n, x⟩ : Σ n, BitVec n))
    (fun x ↦ w.machine.init ⟨n, x⟩) (fun _ ↦ rfl) (fun _ ↦ rfl)).comp w.headCode).copy _
    (fun x ↦ by simp [w.head_init])

theorem UniformPureWitness.size_toRealizer (w : UniformPureWitness p posEnc f) (n : ℕ) :
    (w.toRealizer n).size = w.initCode.size + w.headCode.size := by
  unfold UniformPureWitness.toRealizer
  rw [EncPolyTime.size_copy, EncPolyTime.size_comp, EncPolyTime.size_recode]

theorem UniformPureWitness.time_toRealizer (w : UniformPureWitness p posEnc f) (n : ℕ) :
    (w.toRealizer n).time = (w.initCode.comp w.headCode).time := by
  unfold UniformPureWitness.toRealizer
  rw [EncPolyTime.time_copy, EncPolyTime.comp_time, EncPolyTime.comp_time, EncPolyTime.time_recode]

/-- A uniform certificate gives a family with one shared time polynomial and constant
description size: every member uses the same machine. -/
noncomputable def UniformPureWitness.toFam (w : UniformPureWitness p posEnc f) :
    Backend.description.FamRealizer Backend.polynomialBackend
      (fun n (x : BitVec n) ↦ unaryInput ⟨n, x⟩) (fun _ ↦ headEnc posEnc)
      (fun n x ↦ Sum.inl ⟨n, f n x⟩) where
  wit n := w.toRealizer n
  time := (w.initCode.comp w.headCode).time
  time_le n k := by
    change (w.toRealizer n).time.eval k ≤ _
    rw [w.time_toRealizer]
    exact Polynomial.eval_le_eval (Nat.le_add_left k n)
  desc := .C (w.initCode.size + w.headCode.size)
  desc_le n := by
    change (w.toRealizer n).size ≤ _
    rw [w.size_toRealizer]
    simp

/-- **The uniform notion is not vacuous**: at any pinned position encoding, some Boolean family
has no uniform certificate. Obtained from the generic separation through bridge 2. -/
theorem exists_isEmpty_uniformPureWitness (hpos : Function.Injective posEnc) :
    ∃ f : (n : ℕ) → BitVec n → Bool, IsEmpty (UniformPureWitness p posEnc f) := by
  obtain ⟨f, hf⟩ := Backend.description.exists_not_realizableLE_poly
    (D := fun n ↦ BitVec n) (E := fun _ ↦ (Σ _ : ℕ, Bool) ⊕ (PFunctor.sigma p).A)
    (fun n (x : BitVec n) ↦ unaryInput ⟨n, x⟩) (fun _ ↦ headEnc posEnc) (fun n b ↦ Sum.inl ⟨n, b⟩)
    (fun n b b' h ↦ by simpa using h) (fun _ ↦ headEnc_injective hpos)
    (fun n ↦ 2 ^ (n / 4)) Polynomial.eventually_eval_le_two_pow_div_four
    Backend.eventually_card_tmTable_lt
  refine ⟨f, ⟨fun w ↦ hf ⟨.C (w.initCode.size + w.headCode.size),
    Filter.Eventually.of_forall fun n ↦ ?_⟩⟩⟩
  refine Backend.description.mem_realizableLE.mpr ⟨w.toRealizer n, ?_⟩
  rw [Backend.descSize_eq, w.size_toRealizer]
  simp

/-! ## The `1^n` canary, machine-free -/

/-- Under the unary parameter, an output of size `n` has a linear envelope in the input size. -/
theorem unary_envelope (n k : ℕ) : n ≤ (Polynomial.X : Polynomial ℕ).eval (n + k) := by
  simp

/-- Under a binary parameter, no polynomial in the input size bounds an output of size `n`:
`1^n` is not polynomially bounded in `Nat.size n`. -/
theorem binary_no_envelope (q : Polynomial ℕ) : ∃ n, q.eval (Nat.size n) < n := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (Polynomial.eventually_eval_le_two_pow_div_four q)
  refine ⟨2 ^ (M + 3), ?_⟩
  rw [Nat.size_pow]
  calc q.eval (M + 3 + 1) ≤ 2 ^ ((M + 3 + 1) / 4) := hM _ (by omega)
    _ < 2 ^ (M + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)

end ComplexityBackends.CslibSingleTape.Uniform
