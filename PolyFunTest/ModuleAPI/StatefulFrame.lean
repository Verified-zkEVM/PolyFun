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
        (fun a => frameFst F (post a)) E := by
  simpa only [top_meet] using (frames_sum_inl tick take twoTicks F).op_wp_le_wp_op post E

/-- Throwing in the base monad uses the original exception predicate under any guard. -/
example (f : Handler.Stateful (Except String) Nat counter)
    (g : Handler.Stateful (Except String) Bool flag) (F : Nat → Prop)
    (guard : Nat × Bool → Prop) (post : Bool → Nat × Bool → Prop) (E : String → Prop) :
    let x := ((FreeM.lift (P := flag) ()).mapLens Lens.inr).liftM (sum f g)
    Lean.Order.meet guard (frameSnd F (wp x post E)) ⊑ wp x (fun a => frameSnd F (post a)) E :=
  (frames_sum_inr f g (FreeM.lift ()) F guard).op_wp_le_wp_op post E

/-- An exception thrown over a state monad sees the frame at the state where it was thrown. -/
example (e : String) (F : Bool → Prop) (guard : Nat × Bool → Prop) :
    WP.Frames (frameFst (S := Nat) (T := Bool))
      (opE := FrameOp.prod (FrameOp.pointwise frameFst) FrameOp.ignore)
      (throwThe String e : ExceptT String (StateM (Nat × Bool)) Nat) F guard := by
  constructor
  intro post E st h
  exact meet_le_right guard _ st h

example (post : Nat → Nat × Bool → Prop) (E : EStack⟨⟩) :
    wp ((twoTicks.mapLens Lens.inl).liftM (sum tick take)) post E ⊑
      ((WP.trans ((twoTicks.mapLens Lens.inl).liftM (sum tick take))).frameClosure frameFst).apply
        post E := by
  apply (PredTrans.le_frameClosure_iff frameFst _).mpr
  intro F
  simpa only [top_meet, WP.wp] using (frames_sum_inl tick take twoTicks F).op_wp_le_wp_op post E

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
