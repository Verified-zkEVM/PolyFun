/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.PFunctor.Free.WP.StatefulFrame
public import PolyFunTest.ModuleAPI.StatefulCombinators

/-!
# Ordinary-import checks for stateful sum frames

The counter advances twice while a true flag is framed. A flag request clears the flag
while a fixed counter value is framed. The core framing API also accepts postconditions
that mention both state components, and its frame-closure rule uses the exported
supremum-preservation instances.
-/

@[expose] public section

namespace PolyFunTest.ModuleAPI.StatefulFrame

open PFunctor Std.WP Lean.Order
open PFunctor.Handler.Stateful
open PolyFunTest.ModuleAPI.StatefulCombinators

/-- Two requests to the counter interface, returning the second answer. -/
def twoTicks : FreeM counter Nat := do
  let _ ← FreeM.lift ()
  FreeM.lift ()

example : Triple ((twoTicks.mapLens (Lens.inl (Q := flag))).liftM (sum tick take))
    (fun st => st.1 = 3 ∧ st.2 = true)
    (fun a st => (a = 4 ∧ st.1 = 5) ∧ st.2 = true) Lean.Order.bot := by
  apply triple_sum_inl_frame tick take (x := twoTicks)
    (A := fun n => n = 3) (B := fun a n => a = 4 ∧ n = 5) (fun b => b = true)
  constructor
  intro n hn
  change n + 1 = 4 ∧ n + 1 + 1 = 5
  subst n
  exact ⟨rfl, rfl⟩

example : Triple (((FreeM.lift (P := flag) ()).mapLens (Lens.inr (P := counter))).liftM
    (sum tick take)) (fun st => st.1 = 7 ∧ st.2 = true)
    (fun a st => st.1 = 7 ∧ (a = true ∧ st.2 = false)) Lean.Order.bot := by
  apply triple_sum_inr_frame tick take (x := FreeM.lift ())
    (A := fun b => b = true) (B := fun a b => a = true ∧ b = false) (fun n => n = 7)
  constructor
  intro b hb
  change b = true ∧ false = false
  exact ⟨hb, rfl⟩

example (post : Nat → Nat × Bool → Prop) (E : EStack⟨⟩) (F : Bool → Prop) :
    frameFst F (wp ((twoTicks.mapLens Lens.inl).liftM (sum tick take)) post E) ⊑
      wp ((twoTicks.mapLens Lens.inl).liftM (sum tick take))
        (fun a => frameFst F (post a)) E :=
  (frames_sum_inl tick take twoTicks F).op_wp_le_wp_op post E

example (post : Nat → Nat × Bool → Prop) (E : EStack⟨⟩) :
    wp ((twoTicks.mapLens Lens.inl).liftM (sum tick take)) post E ⊑
      ((WP.wpTrans ((twoTicks.mapLens Lens.inl).liftM (sum tick take))).frameClosure frameFst).apply
        post E := by
  exact WP.Frames.le_frameClosure frameFst (frames_sum_inl tick take twoTicks)
    PartialOrder.rel_refl

/--
info: 'PFunctor.Handler.Stateful.triple_sum_inl_frame' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms triple_sum_inl_frame
/--
info: 'PFunctor.Handler.Stateful.triple_sum_inr_frame' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms triple_sum_inr_frame

end PolyFunTest.ModuleAPI.StatefulFrame
