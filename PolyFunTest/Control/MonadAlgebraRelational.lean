/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.Control.Monad.Algebra.Relational

/-!
# Relational monad-algebra canaries

Concrete identity-algebra examples pin the core relational WP laws and the
transformer side lifts. These tests are intentionally independent of any
downstream probability or cryptography instance.
-/

@[expose] public section

namespace PolyFunTest.MonadAlgebraRelational

open MAlgRelOrdered

noncomputable local instance instIdRel : MAlgRelOrdered Id Id Prop where
  rwp x y post := post x y
  rwp_pure _ _ _ := rfl
  rwp_mono hpost := hpost _ _
  rwp_bind_le _ _ _ _ _ := le_rfl

noncomputable local instance instIdOrdered : MAlgOrdered Id Prop where
  μ x := x
  μ_pure _ := rfl
  μ_bind_mono _ _ h x := h x

local instance instStrictId : StrictBind Id Id Prop where
  rwp_bind _ _ _ _ _ := rfl

local instance instAnchoredId : Anchored Id Id Prop where
  rwp_pure_left _ _ _ := rfl
  rwp_pure_right _ _ _ := rfl

/-- The identity relational algebra evaluates its postcondition directly. -/
example : RelWP (m₁ := Id) (m₂ := Id) (2 : Nat) (3 : Nat)
    (fun a b => a + 1 = b) := by
  change 2 + 1 = 3
  decide

/-- The generic bind rule composes concrete identity computations. -/
example : Triple (m₁ := Id) (m₂ := Id) True (2 : Nat) (3 : Nat)
    (fun a b => a + 1 = b) := by
  apply triple_pure
  change True → 2 + 1 = 3
  intro
  decide

/-- Strict bind specializes to definitional equality for the identity model. -/
example (x y : Nat) (f g : Nat → Nat) (post : Nat → Nat → Prop) :
    RelWP (m₁ := Id) (m₂ := Id) x y
        (fun a b => RelWP (m₁ := Id) (m₂ := Id) (f a) (g b) post) =
      RelWP (m₁ := Id) (m₂ := Id) (x >>= f) (y >>= g) post :=
  StrictBind.relWP_bind (m₁ := Id) (m₂ := Id) (l := Prop) x y f g post

/-- Anchoring recovers the unary WP when the left computation is pure. -/
example (a : Nat) (y : Id Nat) (post : Nat → Nat → Prop) :
    RelWP (m₁ := Id) (m₂ := Id) (pure a) y post = MAlgOrdered.wp y (post a) :=
  Anchored.relWP_pure_left a y post

/-- The one-sided bind rules have the advertised orientation on concrete,
non-equal values. -/
example :
    RelWP (m₁ := Id) (m₂ := Id) (1 : Nat) (4 : Nat)
        (fun a b => RelWP (m₁ := Id) (m₂ := Id) (a + 2) (pure b)
          (fun left right => left + 1 = right)) ≤
      RelWP (m₁ := Id) (m₂ := Id) ((1 : Id Nat) >>= fun a => pure (a + 2)) 4
        (fun left right => left + 1 = right) :=
  relWP_bind_left_le (m₁ := Id) (m₂ := Id) (l := Prop)
    1 (fun a => pure (a + 2)) 4 (fun left right => left + 1 = right)

example :
    RelWP (m₁ := Id) (m₂ := Id) (1 : Nat) (2 : Nat)
        (fun a b => RelWP (m₁ := Id) (m₂ := Id) (pure a) (b + 2)
          (fun left right => left + 3 = right)) ≤
      RelWP (m₁ := Id) (m₂ := Id) 1 ((2 : Id Nat) >>= fun b => pure (b + 2))
        (fun left right => left + 3 = right) :=
  relWP_bind_right_le (m₁ := Id) (m₂ := Id) (l := Prop)
    1 2 (fun b => pure (b + 2)) (fun left right => left + 3 = right)

/-! ## Transformer selection and execution -/

section LeftState

noncomputable local instance instLeftState :
    MAlgRelOrdered (StateT Nat Id) Id (Nat → Prop) :=
  stateTLeft Nat

noncomputable local instance instStrictLeftState :
    StrictBind (StateT Nat Id) Id (Nat → Prop) :=
  strictBindStateTLeft Nat

#synth MAlgRelOrdered (StateT Nat Id) Id (Nat → Prop)
#synth StrictBind (StateT Nat Id) Id (Nat → Prop)

/-- A left-state lift threads the final state into the postcondition. -/
def bump : StateT Nat Id Nat :=
  fun state => (state, state + 1)

example : RelWP (m₁ := StateT Nat Id) (m₂ := Id) bump (2 : Nat)
    (fun value right finalState => value = 1 ∧ right = 2 ∧ finalState = 2) 1 := by
  change 1 = 1 ∧ 2 = 2 ∧ 2 = 2
  decide

end LeftState

section RightState

noncomputable local instance instRightState :
    MAlgRelOrdered Id (StateT Bool Id) (Bool → Prop) :=
  stateTRight Bool

noncomputable local instance instStrictRightState :
    StrictBind Id (StateT Bool Id) (Bool → Prop) :=
  strictBindStateTRight Bool

#synth MAlgRelOrdered Id (StateT Bool Id) (Bool → Prop)
#synth StrictBind Id (StateT Bool Id) (Bool → Prop)

example : (RelWP (m₁ := Id) (m₂ := StateT Bool Id) (l := Bool → Prop)
    (7 : Nat) (fun state => (if state then 8 else 6, !state))
    (fun left right finalState => left + 1 = right ∧ finalState = false)) true := by
  change 7 + 1 = 8 ∧ false = false
  decide

end RightState

section BothStates

noncomputable local instance instBothStates :
    MAlgRelOrdered (StateT Bool Id) (StateT Nat Id) (Bool → Nat → Prop) :=
  stateTBoth Bool Nat

noncomputable local instance instStrictBothStates :
    StrictBind (StateT Bool Id) (StateT Nat Id) (Bool → Nat → Prop) :=
  strictBindStateTBoth Bool Nat

#synth MAlgRelOrdered (StateT Bool Id) (StateT Nat Id) (Bool → Nat → Prop)
#synth StrictBind (StateT Bool Id) (StateT Nat Id) (Bool → Nat → Prop)

/-- The two-sided lift keeps left output, right output, left final state, and
right final state in that order. Distinct types and values make every swap
observable. -/
example : (RelWP (m₁ := StateT Bool Id) (m₂ := StateT Nat Id)
    (l := Bool → Nat → Prop)
    (fun left => (if left then 7 else 5, !left))
    (fun right => (right + 10, right + 1))
    (fun leftOut rightOut leftFinal rightFinal =>
      leftOut = 7 ∧ rightOut = 13 ∧ leftFinal = false ∧ rightFinal = 4))
    true 3 := by
  change 7 = 7 ∧ 13 = 13 ∧ false = false ∧ 4 = 4
  decide

end BothStates

section RightOption

noncomputable local instance instRightOption :
    MAlgRelOrdered Id (OptionT Id) Prop :=
  optionTRight

#synth MAlgRelOrdered Id (OptionT Id) Prop

/-- The lossy `OptionT` side lift interprets `none` as `⊥`. -/
def noRightResult : OptionT Id Nat := none

example : ¬ RelWP (m₁ := Id) (m₂ := OptionT Id) (1 : Nat) noRightResult
    (fun _ _ => True) := by
  change ¬ False
  exact not_false

example : RelWP (m₁ := Id) (m₂ := OptionT Id) (1 : Nat) (pure 2)
    (fun left right => left + 1 = right) := by
  change 1 + 1 = 2
  decide

end RightOption

section LeftOption

noncomputable local instance instLeftOption :
    MAlgRelOrdered (OptionT Id) Id Prop :=
  optionTLeft

#synth MAlgRelOrdered (OptionT Id) Id Prop

example : ¬ RelWP (m₁ := OptionT Id) (m₂ := Id) (none : OptionT Id Nat) (1 : Nat)
    (fun _ _ => True) := by
  change ¬ False
  exact not_false

example : RelWP (m₁ := OptionT Id) (m₂ := Id) (pure 2) (3 : Nat)
    (fun left right => left + 1 = right) := by
  change 2 + 1 = 3
  decide

end LeftOption

section LeftExcept

noncomputable local instance instLeftExcept :
    MAlgRelOrdered (ExceptT Unit Id) Id Prop :=
  exceptTLeft Unit

#synth MAlgRelOrdered (ExceptT Unit Id) Id Prop

/-- The lossy `ExceptT` side lift likewise interprets an error as `⊥`. -/
def leftError : ExceptT Unit Id Nat := .error ()

example : ¬ RelWP (m₁ := ExceptT Unit Id) (m₂ := Id) leftError (1 : Nat)
    (fun _ _ => True) := by
  change ¬ False
  exact not_false

example : RelWP (m₁ := ExceptT Unit Id) (m₂ := Id) (pure 2) (3 : Nat)
    (fun left right => left + 1 = right) := by
  change 2 + 1 = 3
  decide

end LeftExcept

section RightExcept

noncomputable local instance instRightExcept :
    MAlgRelOrdered Id (ExceptT Unit Id) Prop :=
  exceptTRight Unit

#synth MAlgRelOrdered Id (ExceptT Unit Id) Prop

example : ¬ RelWP (m₁ := Id) (m₂ := ExceptT Unit Id) (1 : Nat)
    (.error () : ExceptT Unit Id Nat) (fun _ _ => True) := by
  change ¬ False
  exact not_false

example : RelWP (m₁ := Id) (m₂ := ExceptT Unit Id) (2 : Nat) (pure 3)
    (fun left right => left + 1 = right) := by
  change 2 + 1 = 3
  decide

end RightExcept

section HonestRelationalExceptions

/-! `rwpExc` keeps the four success/failure combinations apart, where the `exceptTLeft` /
`exceptTRight` lifts collapse failure to `⊥`. The `Anchored` instance above is what makes
the collapse-to-unary laws available. -/

/-- Both sides succeed: the postcondition is read at the two `ok` branches. -/
example : rwpExc (m₁ := Id) (m₂ := Id) (ε₁ := Unit) (ε₂ := Unit)
    (pure 2) (pure 3) (fun ea eb => ea = Except.ok 2 ∧ eb = Except.ok 3) :=
  by simp

/-- A thrown exception is *recorded*, not collapsed. Under the lossy `ExceptT` lifts this
postcondition would be unreachable; here it is just the `error`/`ok` corner. -/
example (e : Unit) : rwpExc (m₁ := Id) (m₂ := Id) (ε₂ := Unit)
    (ExceptT.mk (pure (Except.error e)) : ExceptT Unit Id Nat) (pure 3)
    (fun ea eb => ea = Except.error e ∧ eb = Except.ok 3) :=
  by simp

/-- Anchoring: with a pure left side, the relational statement becomes the unary `wpExc`
of the right side. -/
example (y : ExceptT Unit Id Nat) (post : Except Unit Nat → Except Unit Nat → Prop) :
    rwpExc (m₁ := Id) (m₂ := Id) (pure 2 : ExceptT Unit Id Nat) y post =
      MAlgOrdered.wpExc y (fun b => post (Except.ok 2) (Except.ok b))
        (fun e => post (Except.ok 2) (Except.error e)) :=
  rwpExc_pure_left 2 y post

/-- The relational bind rule preserves an existing error instead of running that
side's continuation, while the successful side continues normally. -/
example : rwpExc (m₁ := Id) (m₂ := Id)
    ((ExceptT.mk (pure (Except.error "stop")) : ExceptT String Id Nat) >>=
      fun _ => pure 99)
    ((pure 3 : ExceptT Unit Id Nat) >>= fun n => pure (n + 1))
    (fun ea eb => ea = Except.error "stop" ∧ eb = Except.ok 4) := by
  have h := rwpExc_bind_le
    (ExceptT.mk (pure (Except.error "stop")) : ExceptT String Id Nat)
    (pure 3 : ExceptT Unit Id Nat) (fun _ => pure 99) (fun n => pure (n + 1))
    (fun ea eb => ea = Except.error "stop" ∧ eb = Except.ok 4)
  change _ → _ at h
  apply h
  change (Except.error "stop" : Except String Nat) = Except.error "stop" ∧
    (Except.ok 4 : Except Unit Nat) = Except.ok 4
  exact ⟨rfl, rfl⟩

end HonestRelationalExceptions

section Automation

/-! The relational simp set is thin by design: `MAlgRelOrdered`'s composition axiom is
an *inequality*, so the derived structural rules cannot be rewrite rules. What is
equational is the leaf, the `StrictBind` bind law, and the `rwpExc` corners. -/

/-- The leaf rule fires. -/
example (post : Nat → Nat → Prop) (h : post 1 2) :
    RelWP (m₁ := Id) (m₂ := Id) (pure 1) (pure 2) post := by
  simpa using h

/-- Under `StrictBind` the bind law is an equation, so `simp` decomposes a sequenced
relational goal — which it cannot do without that class. -/
example (f : Nat → Id Nat) (g : Nat → Id Nat) (post : Nat → Nat → Prop) :
    RelWP (m₁ := Id) (m₂ := Id) ((pure 1 : Id Nat) >>= f) ((pure 2 : Id Nat) >>= g) post =
      RelWP (f 1) (g 2) post := by
  simp

end Automation

end PolyFunTest.MonadAlgebraRelational
