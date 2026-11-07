/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Certified
public import PolyFun.PFunctor.Dynamical.DynComputation.Refine
public import PolyFun.PFunctor.Free.Cost.Tactic

/-!
# Bridging cost layers

Checks for certified handlers, stateful certificates and machine refinement, on a three-layer
chain:

* **specification**: a program makes hash queries, within a budget of `q`;
* **algorithm**: each hash query is two compression calls, a certified handler with exchange `2 •`;
* **machine**: each compression is three visible machine steps, by a stateful package that also
  counts compressions.

The machine executing the specification through both layers is within `6 q` steps, obtained by
composing the certificates without unfolding the program. The file also checks two shapes from
verified-circuit and zkVM benchmarks: the T-count of an adaptive circuit is its worst-case cost,
and an instrumented deterministic run reports the cycles of the path it takes.
-/

public section

open PFunctor PFunctor.FreeM PFunctor.Handler PFunctor.DynSystem.DynComputation

namespace PolyFunTest.ChargeBridges

/-! ## Three layers -/

/-- Hash queries, each with a Boolean answer. -/
abbrev Hash : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- Compression calls, each with a Boolean answer. -/
abbrev Compress : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- One visible machine step. -/
abbrev Step : PFunctor.{0, 0} := ⟨Unit, fun _ => PUnit⟩

/-- Scale a natural-number count. -/
@[expose] def scale (k : ℕ) : ℕ →+o ℕ where
  toFun n := k * n
  map_zero' := by simp
  map_add' a b := Nat.mul_add k a b
  monotone' _ _ h := by dsimp only; exact Nat.mul_le_mul_left k h

@[simp]
theorem scale_apply (k n : ℕ) : scale k n = k * n :=
  rfl

/-- Each hash query is two compression calls. -/
def hashByCompress : Handler (FreeM Compress) Hash := fun _ => do
  let _ ← FreeM.lift (P := Compress) ()
  FreeM.lift (P := Compress) ()

/-- The algorithm layer, certified with exchange `2 •`. -/
def hashLayer : Certified Hash Compress (fun _ => (1 : ℕ)) (fun _ => 1) where
  handler := hashByCompress
  exchange := scale 2
  certificate _ := by cost_bound [hashByCompress]

/-- Each compression is three machine steps; the package counts compressions and answers with the
parity of the count. -/
def compressBySteps : Stateful (FreeM Step) ℕ Compress := fun _ count => do
  let _ ← FreeM.lift (P := Step) ()
  let _ ← FreeM.lift (P := Step) ()
  let _ ← FreeM.lift (P := Step) ()
  pure (count % 2 = 0, count + 1)

theorem compressBySteps_withinCharge :
    compressBySteps.WithinCharge (fun _ => (1 : ℕ)) (fun _ => 3) := fun _ count => by
  change (FreeM.bind (FreeM.lift (P := Step) ()) fun _ => FreeM.bind (FreeM.lift (P := Step) ())
    fun _ => FreeM.bind (FreeM.lift (P := Step) ()) fun _ =>
      (pure (count % 2 = 0, count + 1) : FreeM Step (Bool × ℕ))).IsChargeBound _ _
  cost_bound

/-- The machine executing a specification program through both layers. -/
noncomputable def machine (x : Unit → FreeM Hash Bool) :
    DynSystem.DynComputation Step Unit (Bool × ℕ) :=
  ofFreeM fun g => compressBySteps.run ((x g).liftM hashLayer.handler) 0

/-- **End to end.** A specification within `q` hash queries runs on the machine within `6 q`
steps. The bound composes the algorithm layer's exchange (`2 •`), the stateful package's price
(`3` steps per compression), and the machine's refinement of the run. -/
theorem machine_isChargeBound (x : Unit → FreeM Hash Bool) (q : ℕ)
    (hx : ∀ g, (x g).IsChargeBound (fun _ => 1) q) (g : Unit) :
    (machine x).IsChargeBound (fun _ => 1) (6 * q) ((machine x).init g) := by
  have halg : ∀ g, ((x g).liftM hashLayer.handler).IsChargeBound (fun _ => 3) (6 * q) := by
    intro g
    have h2 := hashLayer.transfer (hx g)
    have h3 := h2.map (scale 3)
    simp only [hashLayer, scale_apply] at h3
    exact h3.mono (by omega)
  exact (refinesVia_ofFreeM compressBySteps (fun g => (x g).liftM hashLayer.handler)
    fun _ => 0).isChargeBound compressBySteps_withinCharge halg g

/-! ## Adaptive circuits -/

/-- Gates of an adaptive circuit: a T gate, a Toffoli gate, a Clifford gate, and a measurement
with a Boolean outcome. -/
inductive Gate
  | t
  | toffoli
  | clifford
  | measure

/-- The circuit interface: only a measurement has an informative answer. -/
abbrev Circuit : PFunctor.{0, 0} := ⟨Gate, fun g => match g with
  | .measure => Bool
  | _ => PUnit⟩

/-- T-count, with a Toffoli gate decomposed into seven T gates. -/
def tCount : Gate → ℕ∞
  | .t => 1
  | .toffoli => 7
  | .clifford => 0
  | .measure => 0

/-- Measure, then apply a Toffoli or two T gates depending on the outcome. -/
def adaptive : FreeM Circuit PUnit := do
  let _ ← FreeM.lift (P := Circuit) .clifford
  let b ← FreeM.lift (P := Circuit) .measure
  if b then
    FreeM.lift (P := Circuit) .toffoli
  else do
    let _ ← FreeM.lift (P := Circuit) .t
    FreeM.lift (P := Circuit) .t

/-- The T-count of an adaptive circuit is its worst-case cost over measurement outcomes. -/
example : cost tCount adaptive = 7 := by
  cost_bound [adaptive, tCount]

/-! ## Cycles of an instrumented run -/

/-- Instructions priced by cycles: arithmetic costs one cycle, a hash precompile eight. -/
inductive Instr
  | add
  | hash

abbrev Machine : PFunctor.{0, 0} := ⟨Instr, fun _ => Bool⟩

def cycles : Instr → ℕ
  | .add => 1
  | .hash => 8

def verify : FreeM Machine Bool := do
  let _ ← FreeM.lift (P := Machine) .add
  let ok ← FreeM.lift (P := Machine) .hash
  if ok then FreeM.lift (P := Machine) .add else pure false

/-- A deterministic executor answering every instruction with `true`. -/
def execute : Handler Id Machine := fun _ => true

/-- The instrumented run reports the cycles of the path the executor takes, and the program's
budget bounds them. -/
example : ((verify.liftM (execute.withCharge cycles)).run 0).2 = 10 := rfl

example : verify.IsChargeBound cycles 10 := by
  cost_bound [verify, cycles]

end PolyFunTest.ChargeBridges
