/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.Probabilistic.Sampling
-- frontier: CslibFrontier.Computability.Probabilistic.PPT.Capture

public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Computability.Probabilistic.PPT.Capture
public import PolyFun.PFunctor.Handler.Free
public import PolyFun.PFunctor.Handler.Sum
public import PolyFunFrontier.Realizability.MultiTape

/-!
# Uniform machine realizations of typed free programs

`PPTProgram handler input output program` certifies a family of free programs at fixed input
and output encodings. A primitive request needs a certificate for its handler at the requested
arguments. A continuation that retains its input is certified on a pair of the input and the
first result. The same derivation can be used over a larger signature by relabelling its requests.

`PPTProgram.substitute` installs a free implementation at each request. Its soundness uses
`Handler.liftM_comp`, so folding the resulting source through the final handler agrees with
folding the original through the composite handler. The deterministic steps in the source
belong to `StepClass.multiTapePolyTime`.

`MachineRealization.ofPPTProgram` chooses a finite fair-coin machine and one polynomial clock
for the whole family. Its encoded output law agrees with the fold of the source program under
the specified handler, and every supported machine run halts within the clock. In particular,
the fair-bit rule realizes a sampler with that law, independently of the cost of executing the
original coin program.
-/

@[expose] public section

namespace PFunctor.FreeM

open Turing.MultiTapeTM
open Cslib.Probability (IsPPTOn)

/-- Draw a word in sampling order, running the given bit program once per output bit. -/
def sampleBits {P : PFunctor} (coin : P.FreeM Bool) : Nat → P.FreeM (List Bool)
  | 0 => pure []
  | n + 1 => do
    let bit ← coin
    return bit :: (← sampleBits coin n)

/-- Handling a fair bit at each draw gives the frontier's fair-word program. -/
theorem liftM_sampleBits {P : PFunctor} {H : Handler Cslib.ProbComp P} {coin : P.FreeM Bool}
    (hcoin : coin.liftM H = Cslib.ProbComp.uniform Bool) (n : Nat) :
    (sampleBits coin n).liftM H = Cslib.BitString.sampleList n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sampleBits, Cslib.BitString.sampleList, liftM_bind, liftM_pure, hcoin, ih]

/-- A compositional certificate for an input-indexed free program and its probabilistic handler.
The encodings belong to the family and are fixed across all inputs. -/
inductive PPTProgram : {P : PFunctor.{0, 0}} → Handler Cslib.ProbComp P → {α β : Type} →
    (α ↪ List Bool) → (β ↪ List Bool) → (α → P.FreeM β) → Prop where
  /-- Return an efficiently computed value. -/
  | localMap {P : PFunctor} {H : Handler Cslib.ProbComp P} {α β : Type}
      {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
      (hf : StepClass.multiTapePolyTime.Hom input output f) :
      PPTProgram H input output (fun a => pure (f a))
  /-- Make one request and read its dependent response at the chosen output type. -/
  | call {P : PFunctor} {H : Handler Cslib.ProbComp P} {α β : Type}
      {input : α ↪ List Bool} {output : β ↪ List Bool} {query : α → P.A}
      {answer : (a : α) → P.B (query a) → β}
      (h : IsPPTOn input output (fun a => answer a <$> H (query a))) :
      PPTProgram H input output (fun a => answer a <$> FreeM.lift (query a))
  /-- Retain the typed input across a probabilistic first stage. -/
  | bindWith {P : PFunctor} {H : Handler Cslib.ProbComp P} {α β γ : Type}
      {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
      {first : α → P.FreeM β} {next : α → β → P.FreeM γ}
      (hfirst : PPTProgram H input middle first)
      (hnext : PPTProgram H (encPair input middle) output (fun p => next p.1 p.2)) :
      PPTProgram H input output (fun a => first a >>= next a)
  /-- Choose between two source programs by an efficient Boolean test on the input. -/
  | branch {P : PFunctor} {H : Handler Cslib.ProbComp P} {α β : Type}
      {input : α ↪ List Bool} {output : β ↪ List Bool} {condition : α → Bool}
      {yes no : α → P.FreeM β}
      (hc : StepClass.multiTapePolyTime.Hom input encBool condition)
      (hy : PPTProgram H input output yes) (hn : PPTProgram H input output no) :
      PPTProgram H input output (fun a => if condition a then yes a else no a)
  /-- Prepare an argument with an encoded polynomial-time function. -/
  | preprocess {P : PFunctor} {H : Handler Cslib.ProbComp P} {α β γ : Type}
      {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
      {program : β → P.FreeM γ} {f : α → β}
      (h : PPTProgram H middle output program)
      (hf : StepClass.multiTapePolyTime.Hom input middle f) :
      PPTProgram H input output (fun a => program (f a))
  /-- Draw an efficiently computed unary number of fair bits. -/
  | sampleBits {P : PFunctor} {H : Handler Cslib.ProbComp P} {α : Type}
      {input : α ↪ List Bool} {count : α → Nat} {coin : P.FreeM Bool}
      (hcoin : coin.liftM H = Cslib.ProbComp.uniform Bool)
      (hcount : ComputableInPolyTime count input encUnary) :
      PPTProgram H input encBits (fun a => FreeM.sampleBits coin (count a))
  /-- Substitute a free program for each request. The original certificate reads requests
  through the composite of that implementation and the final handler. -/
  | substitute {P Q : PFunctor} {H : Handler Cslib.ProbComp Q} {α β : Type}
      {input : α ↪ List Bool} {output : β ↪ List Bool} {program : α → P.FreeM β}
      (impl : Handler (FreeM Q) P) (h : PPTProgram (H.comp impl) input output program) :
      PPTProgram H input output (fun a => (program a).liftM impl)

namespace PPTProgram

variable {P Q : PFunctor} {H : Handler Cslib.ProbComp P} {G : Handler Cslib.ProbComp Q}
  {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}

/-- Transport a certificate along an equation of source programs at every input. -/
theorem congr {first second : α → P.FreeM β} (h : PPTProgram H input middle first)
    (heq : ∀ a, first a = second a) : PPTProgram H input middle second :=
  funext heq ▸ h

/-- Relabel the source interface along a lens, using its backward map on responses. -/
theorem mapLens {program : α → P.FreeM β} (l : Lens P Q)
    (h : PPTProgram (G.comapLens l) input middle program) :
    PPTProgram G input middle (fun a => (program a).mapLens l) := by
  have h' : PPTProgram (G.comp (Handler.ofLens l)) input middle program :=
    by simpa only [Handler.comp_ofLens] using h
  exact (substitute (Handler.ofLens l) h').congr (fun a => Handler.liftM_ofLens l (program a))

/-- Apply an efficient deterministic map to the original input and a sampled result. -/
theorem mapWith {program : α → P.FreeM β} {f : α → β → γ}
    (h : PPTProgram H input middle program)
    (hf : StepClass.multiTapePolyTime.Hom (encPair input middle) output
      (fun p : α × β => f p.1 p.2)) :
    PPTProgram H input output (fun a => f a <$> program a) := by
  apply (h.bindWith (next := fun a b => pure (f a b)) (.localMap hf)).congr
  exact fun a => bind_pure_comp (f a) (program a)

/-- Use a program over the left component of a sum handler. -/
theorem sumLeft {program : α → P.FreeM β} (h : PPTProgram H input middle program)
    (right : Handler Cslib.ProbComp Q) :
    PPTProgram (H.sum right) input middle (fun a => (program a).mapLens Lens.inl) :=
  .mapLens Lens.inl (by simpa only [Handler.sum_comapLens_inl] using h)

/-- Use a program over the right component of a sum handler. -/
theorem sumRight {program : α → Q.FreeM β} (h : PPTProgram G input middle program)
    (left : Handler Cslib.ProbComp P) :
    PPTProgram (left.sum G) input middle (fun a => (program a).mapLens Lens.inr) :=
  .mapLens Lens.inr (by simpa only [Handler.sum_comapLens_inr] using h)

/-- The handler fold of a certified source is strict uniform probabilistic polynomial time. -/
theorem isPPTOn {program : α → P.FreeM β} (h : PPTProgram H input middle program) :
    IsPPTOn input middle (fun a => (program a).liftM H) := by
  induction h with
  | localMap hf => simpa only [liftM_pure] using ComputableInPolyTime.isPPTOn hf
  | call h => simpa only [liftM_map, liftM_lift] using h
  | bindWith _ _ ihFirst ihNext =>
    simpa only [liftM_bind] using ihFirst.bind_with ihNext
  | branch hc _ _ ihYes ihNo => simpa only [apply_ite] using IsPPTOn.cond hc ihYes ihNo
  | preprocess _ hf ih => exact ih.preprocess hf
  | sampleBits hcoin hcount =>
    simpa only [liftM_sampleBits hcoin] using hcount.sampleList
  | substitute impl _ ih => simpa only [Handler.liftM_comp] using ih

end PPTProgram

variable {P : PFunctor} {α β : Type}

/-- A finite fair-coin machine implementing the handler fold at the given boundary encodings. -/
structure MachineRealization (H : Handler Cslib.ProbComp P)
    (input : α ↪ List Bool) (encoding : β ↪ List Bool) (program : α → P.FreeM β) where
  tapes : ℕ
  State : Type
  [finiteState : Finite State]
  machine : Turing.MultiTapePTM tapes Bool State
  coefficient : ℕ
  degree : ℕ
  encoded_law (a : α) :
    Cslib.ProbComp.eval (machine.runClosed (coefficient * ((input a).length + 1) ^ degree)
      (input a)) = (Cslib.ProbComp.eval ((program a).liftM H)).map encoding
  halts (w : List Bool) :
    ∀ cfg ∈ (Cslib.ProbComp.eval (machine.runConfigFrom (Cslib.ProbComp.uniform Bool)
      Empty.elim (coefficient * (w.length + 1) ^ degree) (machine.initialConfig w))).support,
      cfg.tapes.state = none

namespace MachineRealization

variable {H : Handler Cslib.ProbComp P} {input : α ↪ List Bool} {encoding : β ↪ List Bool}
  {program : α → P.FreeM β}

/-- Choose the uniform machine and clock supplied by a certificate for the source program. -/
noncomputable def ofPPTProgram (h : PPTProgram H input encoding program) :
    MachineRealization H input encoding program := by
  apply Classical.choice
  obtain ⟨k, σ, hσ, m, c, d, law, halt⟩ := h.isPPTOn.exists_halting_machine
  exact ⟨⟨k, σ, m, c, d, fun a => (law a).symm, halt⟩⟩

/-- The machine's output distribution at its certified clock. -/
noncomputable def output (M : MachineRealization H input encoding program) (a : α) :
    PMF (List Bool) :=
  Cslib.ProbComp.eval (M.machine.runClosed (M.coefficient * ((input a).length + 1) ^ M.degree)
    (input a))

end MachineRealization

end PFunctor.FreeM
