/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunComplexitylib.Backend.StepClass
public import PolyFun.Realizability.Quantitative.Polynomial

/-!
# Concrete tidy machines as a quantitative backend

A `PolyFunComplexitylib.PolyTimeCode ea eb f` is a concrete finite-state binary multi-tape machine,
held as data, that tidily computes `eb (f a)` from `ea a` within certified time and space bounds
that are polynomial in the encoded input length. It is the quantitative refinement of
`PolyFunComplexitylib.polyTimeStepClass`: `PolyTimeCode.computableTidilyInPolyTime` erases it to
complexitylib's predicate, and `PolyTimeCode.ofComputable` chooses code for any member.

`PolyFunComplexitylib.quantitative` charges a code its certified time bound. That charge is
adequate by construction: every code carries, for every input, a run of its machine within the
charge (`PolyTimeCode.computes`). Composition is complexitylib's tidy sequential composition,
whose time is the two bounds plus a linear charge in the intermediate encoding; the constant of
that charge is chosen once per pair of codes, so the cost equation is exact
(`PolyFunComplexitylib.instHasExactCompositionQuantitative`).

The time bound is an upper envelope on the machine's run length, not its exact step count.
-/

@[expose] public section

universe u

namespace PolyFunComplexitylib

open PFunctor Turing Turing.MultiTapeTM

/-- A concrete tidy multi-tape machine computing `f` between the encodings, with time and space
bounds polynomial in the encoded input length. -/
structure PolyTimeCode {A B : Type u} (ea : A ↪ List Bool) (eb : B ↪ List Bool) (f : A → B) where
  /-- The number of work tapes. -/
  tapes : ℕ
  /-- The machine's control states. -/
  State : Type
  /-- The control states are finite. -/
  finite : Finite State
  /-- The machine. -/
  machine : MultiTapeTM tapes Bool State
  /-- The certified time bound on each input. -/
  time : A → ℕ
  /-- The certified space bound on each input. -/
  space : A → ℕ
  /-- The time bound is polynomial in the encoded input length. -/
  time_polyBounded : PolyBounded (fun a => (ea a).length) time
  /-- The space bound is polynomial in the encoded input length. -/
  space_polyBounded : PolyBounded (fun a => (ea a).length) space
  /-- The machine tidily computes `f` within the bounds on every input. -/
  computes : ComputesFunTidilyInTimeAndSpace machine ea eb f time space

namespace PolyTimeCode

variable {A B D : Type u} {ea : A ↪ List Bool} {eb : B ↪ List Bool} {ed : D ↪ List Bool}
  {f : A → B} {g : B → D}

/-- The code's machine witnesses tidy computability within its bounds. -/
theorem computableTidilyInTimeAndSpace (c : PolyTimeCode ea eb f) :
    ComputableTidilyInTimeAndSpace f ea eb c.time c.space :=
  ⟨c.tapes, c.State, c.finite, c.machine, c.computes⟩

/-- Forget a code to complexitylib's polynomial-time predicate. -/
theorem computableTidilyInPolyTime (c : PolyTimeCode ea eb f) :
    ComputableTidilyInPolyTime f ea eb :=
  ⟨c.time, c.space, c.time_polyBounded, c.space_polyBounded, c.computableTidilyInTimeAndSpace⟩

/-- Choose a machine for a tidy computation within given polynomial bounds. -/
noncomputable def ofTimeSpace {t s : A → ℕ} (ht : PolyBounded (fun a => (ea a).length) t)
    (hs : PolyBounded (fun a => (ea a).length) s)
    (h : ComputableTidilyInTimeAndSpace f ea eb t s) : PolyTimeCode ea eb f :=
  have h₁ := Classical.choose_spec h
  have h₂ := Classical.choose_spec h₁
  have h₃ := Classical.choose_spec h₂
  { tapes := Classical.choose h
    State := Classical.choose h₁
    finite := Classical.choose h₂
    machine := Classical.choose h₃
    time := t
    space := s
    time_polyBounded := ht
    space_polyBounded := hs
    computes := Classical.choose_spec h₃ }

@[simp] theorem time_ofTimeSpace {t s : A → ℕ} (ht : PolyBounded (fun a => (ea a).length) t)
    (hs : PolyBounded (fun a => (ea a).length) s)
    (h : ComputableTidilyInTimeAndSpace f ea eb t s) : (ofTimeSpace ht hs h).time = t := rfl

/-- Choose code for a member of complexitylib's polynomial-time class. -/
noncomputable def ofComputable (h : ComputableTidilyInPolyTime f ea eb) : PolyTimeCode ea eb f :=
  have h₁ := Classical.choose_spec h
  have h₂ := Classical.choose_spec h₁
  ofTimeSpace h₂.1 h₂.2.1 h₂.2.2

/-- Code for the identity: complexitylib's tidy copy machine, in linear time and space. -/
noncomputable def identity (ea : A ↪ List Bool) : PolyTimeCode ea ea id :=
  have h := ComputableTidilyInLinearTimeAndSpace.of_eq (f := id) (encIn := ea) (encMid := ea)
    fun _ => rfl
  ofTimeSpace (.of_forall_le (Classical.choose h) 1 fun _ => by simp)
    (.of_forall_le (Classical.choose h) 1 fun _ => by simp) (Classical.choose_spec h)

/-- The constant of the linear connection charge for sequential composition. -/
noncomputable def composeConst (cf : PolyTimeCode ea eb f) (cg : PolyTimeCode eb ed g) : ℕ :=
  Classical.choose (ComputableTidilyInTimeAndSpace.comp_linear cg.computableTidilyInTimeAndSpace
    cf.computableTidilyInTimeAndSpace)

/-- Work spent connecting two codes: linear in the length of the intermediate encoding. -/
noncomputable def composeOverhead (cf : PolyTimeCode ea eb f) (cg : PolyTimeCode eb ed g)
    (a : A) : ℕ :=
  composeConst cf cg * ((eb (f a)).length + 1)

/-- Sequential composition of codes: complexitylib's tidy composition of the two machines. -/
noncomputable def compose (cf : PolyTimeCode ea eb f) (cg : PolyTimeCode eb ed g) :
    PolyTimeCode ea ed (g ∘ f) :=
  have hl := cf.computableTidilyInPolyTime.polyBounded_length
  have hm := (PolyBounded.const (composeConst cf cg)).mul (hl.add (PolyBounded.const 1))
  ofTimeSpace ((cf.time_polyBounded.add (cg.time_polyBounded.comp hl)).add hm)
    ((cf.space_polyBounded.add (cg.space_polyBounded.comp hl)).add hm)
    (Classical.choose_spec (ComputableTidilyInTimeAndSpace.comp_linear
      cg.computableTidilyInTimeAndSpace cf.computableTidilyInTimeAndSpace))

theorem time_compose (cf : PolyTimeCode ea eb f) (cg : PolyTimeCode eb ed g) (a : A) :
    (cf.compose cg).time a = cf.time a + cg.time (f a) + composeOverhead cf cg a := rfl

end PolyTimeCode

/-- The quantitative backend over concrete tidy machines: a realizer is a `PolyTimeCode`, the
size of a value is its encoded length, and the charge is the code's certified time bound. -/
noncomputable def quantitative : QuantitativeStepClass polyTimeStepClass.{u} where
  Realizer ea eb f := PolyTimeCode ea eb f
  size ea a := (ea a).length
  cost c a := c.time a
  admissible c := c.computableTidilyInPolyTime

/-- The charge is adequate: on every input the realizer's machine runs within it. -/
theorem quantitative_adequate {A B : Type u} {ea : A ↪ List Bool} {eb : B ↪ List Bool}
    {f : A → B} (c : quantitative.Realizer ea eb f) (a : A) :
    c.machine.ComputesTidilyInTimeAndSpace (ea a) (eb (f a)) (quantitative.cost c a)
      (c.space a) :=
  c.computes a

noncomputable instance instHasCompositionQuantitative : quantitative.{u}.HasComposition where
  identity ea := PolyTimeCode.identity ea
  compose cf cg := cf.compose cg
  composeOverhead cf cg := cf.composeOverhead cg
  cost_compose_le _ _ _ := le_rfl

instance instHasExactCompositionQuantitative : quantitative.{u}.HasExactComposition where
  cost_compose_eq _ _ _ := rfl

/-! ## First-order polynomial certificates -/

open Complexity

/-- The first-order polynomial `c * (n + 1) ^ d`, the shape of complexitylib's explicit bounds. -/
def scaledPow (c d : ℕ) : FirstOrderPolynomial :=
  (FirstOrderPolynomial.const c).mul
    ((FirstOrderPolynomial.input.add (FirstOrderPolynomial.const 1)).pow d)

@[simp] theorem eval_scaledPow (c d n : ℕ) : (scaledPow c d).eval n = c * (n + 1) ^ d := by
  simp [scaledPow]

/-- Every code has first-order polynomial work and output-size certificates, read off from
complexitylib's explicit forms of its polynomial bounds. -/
noncomputable def PolyTimeCode.toPolyRealizer {A B : Type u} {ea : A ↪ List Bool}
    {eb : B ↪ List Bool} {f : A → B} (c : PolyTimeCode ea eb f) :
    quantitative.PolyRealizer ea eb f :=
  have ht := c.time_polyBounded.exists_le
  have hl := c.computableTidilyInPolyTime.polyBounded_length.exists_le
  { code := c
    work := scaledPow (Classical.choose ht) (Classical.choose (Classical.choose_spec ht))
    outputSize := scaledPow (Classical.choose hl) (Classical.choose (Classical.choose_spec hl))
    work_le := fun a => by
      rw [eval_scaledPow]
      exact Classical.choose_spec (Classical.choose_spec ht) a
    outputSize_le := fun a => by
      rw [eval_scaledPow]
      exact Classical.choose_spec (Classical.choose_spec hl) a }

end PolyFunComplexitylib
