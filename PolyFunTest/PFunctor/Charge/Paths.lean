/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Path.Charge
public import PolyFun.Interaction.Basic.TypeTree

/-!
# Charges of completed paths

Checks for `PolyFun.PFunctor.Free.Path.Charge`:

* with signed weights, a prefix overspends a budget that every completed path respects, so the
  completed-path reading is not derived from the structural bound;
* a call with no answers ends no completed path, so the worst-case cost is the supremum of path
  charges only when every call has an answer;
* the completed-path bound transfers through a free handler, keeping the output;
* relabelling into a sum with a charge that ignores the other summand keeps path charges;
* charging distinct keys is subadditive and below the additive charge;
* weights on the nodes of a protocol bound a path by its length.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargePaths

/-! ## Signed weights -/

/-- Two operations with a single answer each. -/
abbrev Two : PFunctor := ⟨Bool, fun _ => PUnit⟩

/-- `true` costs `1` and `false` refunds `1`. -/
def signed (b : Two.A) : ℤ := if b then 1 else -1

/-- Spend one, then refund it. -/
def upDown : FreeM Two PUnit := do
  let _ ← FreeM.lift (P := Two) true
  FreeM.lift (P := Two) false

/-- Every completed path nets to zero. -/
example : ∀ p : Path upDown, Path.charge signed upDown p ≤ 0 := by
  rw [Path.forall_charge_le_iff_ofHandler (fun _ => PUnit.unit)]
  decide

/-- The first call already overspends a zero budget. -/
example : ¬ upDown.IsChargeBound signed 0 := by
  simp [upDown, signed]

/-! ## Calls with no answer -/

/-- One call that can never be answered. -/
abbrev Dead : PFunctor := ⟨Unit, fun _ => PEmpty⟩

def stuck : FreeM Dead PEmpty := FreeM.lift ()

/-- No completed path ends, so every completed path is within budget `0`. -/
example (p : Path stuck) : Path.charge (fun _ => (1 : ℕ)) stuck p ≤ 0 :=
  p.1.elim

/-- So the worst-case cost, which charges the call, is not the supremum of the path charges:
`cost_eq_iSup_charge` needs every reachable call to have an answer. -/
example : cost (fun _ => (1 : ℕ∞)) stuck ≠ ⨆ p : Path stuck, Path.charge (fun _ => 1) stuck p := by
  have hempty : IsEmpty (Path stuck) := ⟨fun p => p.1.elim⟩
  rw [iSup_of_empty]
  simp [stuck]

/-! ## Transfer through a handler -/

abbrev Coin : PFunctor := ⟨Unit, fun _ => Bool⟩

/-- Implement each call by two calls. -/
def doubled : (a : Coin.A) → FreeM Coin (Coin.B a) := fun _ => do
  let _ ← FreeM.lift (P := Coin) ()
  FreeM.lift (P := Coin) ()

theorem doubled_path (a : Coin.A) (r : Path (doubled a)) :
    Path.charge (fun _ => (1 : ℤ)) (doubled a) r ≤ 2 := by
  rcases r with ⟨b, b', ⟨⟩⟩
  change (1 : ℤ) + (1 + 0) ≤ 2
  decide

/-- When every call has an answer, the worst-case cost is the supremum of the path charges. -/
example {α : Type} (x : FreeM Coin α) (hx : x.ProgramProgress) :
    cost (fun _ => (1 : ℕ∞)) x = ⨆ p : Path x, Path.charge (fun _ => 1) x p :=
  Path.cost_eq_iSup_charge hx

example {α : Type} (x : FreeM Coin α) (n : ℤ)
    (hx : ∀ p : Path x, Path.charge (fun _ => (2 : ℤ)) x p ≤ n) (q : Path (x.liftM doubled)) :
    Path.charge (fun _ => (1 : ℤ)) (x.liftM doubled) q ≤ n :=
  Path.charge_liftM_le_of_forall doubled doubled_path hx q

/-! ## Relabelling with a change of cost monoid -/

/-- Relabel into the left summand of a sum interface, charging the right summand nothing. -/
example {α : Type} (x : FreeM Coin α) (q : Path (x.mapLens (Lens.inl (Q := Two)))) :
    Path.charge (Sum.elim (fun _ => (1 : ℤ)) fun _ => 0) (x.mapLens Lens.inl) q =
      Path.charge (fun _ => (1 : ℤ)) x (Path.pullMapLens Lens.inl x q) :=
  Path.charge_mapLens_eq_map (AddMonoidHom.id ℤ) Lens.inl (fun _ => rfl) x q

/-! ## Distinct keys -/

abbrev Keys : PFunctor.{0, 0} := ⟨ℕ, fun _ => Bool⟩

/-- Querying keys `1, 2, 1` charges two distinct keys, while the additive charge is three. -/
example :
    TraceList.freshCharge (fun _ => (1 : ℕ)) ∅
        ([⟨1, true⟩, ⟨2, true⟩, ⟨1, false⟩] : TraceList Keys) = 2 ∧
      TraceList.charge (fun _ => (1 : ℕ)) ([⟨1, true⟩, ⟨2, true⟩, ⟨1, false⟩] : TraceList Keys) =
        3 := by
  decide

/-! ## Budgets on protocol nodes -/

/-- Two rounds, weighted `2` and `3`. -/
@[expose] def rounds : Interaction.TypeTree.{0} := .node Bool fun _ => .node (Fin 3) fun _ => .done

@[expose] def roundWeights : Displayed.Decoration (fun _ => ℕ) rounds :=
  ⟨2, fun _ => ⟨3, fun _ => PUnit.unit⟩⟩

example (p : Path rounds) : Path.chargeDec rounds roundWeights p ≤ Path.length rounds p • 3 :=
  Path.chargeDec_le_length_nsmul rounds roundWeights
    ⟨by decide, fun _ => ⟨le_rfl, fun _ => trivial⟩⟩ p

end PolyFunTest.ChargePaths
