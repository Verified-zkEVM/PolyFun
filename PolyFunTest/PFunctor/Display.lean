/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display

/-! Worked examples for polynomial displays and their free extension. -/

@[expose] public section

namespace PFunctor.Display.Example

def Unary : PFunctor.{0, 0} where
  A := Bool
  B _ := PUnit

def contract : Display.{0, 0, 0, 0} Unary where
  position _ := PUnit
  direction _ _ _ := PUnit

def oneStep : FreeM Unary Nat :=
  .liftBind true fun _ => .pure 7

def oneStepData :
    FreeM.Displayed (contract.toDisplayedAlgebra fun _ : Nat => PUnit.{1}) oneStep :=
  ⟨.unit, fun _ _ => contract.leaf (fun _ : Nat => PUnit.{1}) 7 .unit⟩

example :
    contract.bind oneStep oneStepData (fun n => .pure (n + 1))
      (fun _ _ => contract.leaf (fun _ : Nat => PUnit.{1}) _ .unit) =
      ⟨.unit, fun _ _ => contract.leaf (fun _ : Nat => PUnit.{1}) 8 .unit⟩ :=
  rfl

def identityHandler :
    Handler contract contract (fun a => FreeM.lift a) :=
  Handler.id contract

example :
    contract.liftM contract oneStep oneStepData
      (fun a => FreeM.lift a) identityHandler = oneStepData := by
  rfl

/-! The following example is deliberately non-constant in every local index:
the response type depends on the operation arity, displayed positions depend
on the same arity, and displayed directions depend on both the selected
position and the concrete response. -/

inductive DepOp where
  | query (arity : Nat)

def Dependent : PFunctor.{0, 0} where
  A := DepOp
  B
    | .query arity => Fin arity

def dependentContract : Display.{0, 0, 0, 0} Dependent where
  position
    | .query arity => Fin (arity + 1)
  direction
    | .query _, c, b => Fin (c.val + b.val + 1)

def dependentTree : FreeM Dependent Nat :=
  .liftBind (.query 2) fun b => .pure b.val

def dependentTreeData :
    FreeM.Displayed
      (dependentContract.toDisplayedAlgebra fun _ : Nat => Nat) dependentTree :=
  ⟨⟨2, by omega⟩, fun b direction =>
    dependentContract.leaf (fun _ : Nat => Nat) b.val (b.val + direction.val)⟩

def dependentObj : Dependent.Obj Nat :=
  ⟨.query 2, fun b => b.val⟩

def dependentObjData : dependentContract.Obj (fun _ : Nat => Nat) dependentObj :=
  ⟨⟨2, by omega⟩, fun b direction => b.val + direction.val⟩

/- If `Obj.map` selects the wrong response or displayed direction, this value
is not `b + direction + 1`. -/
example (b : Fin 2)
    (direction : dependentContract.direction (.query 2) ⟨2, by omega⟩ b) :
    (Obj.map (S := dependentContract) (fun _ n => n + 1)
      dependentObj dependentObjData).2 b direction =
      b.val + direction.val + 1 := by
  rfl

def predicateContract : Display Dependent :=
  Display.ofPredicates
    (fun | .query arity => arity = 2)
    (fun | .query arity => fun _ response => response.val < arity)

def predicatePosition : predicateContract.position (.query 2) :=
  ⟨rfl⟩

def predicateDirection (b : Fin 2) :
    predicateContract.direction (.query 2) predicatePosition b :=
  ⟨b.isLt⟩

example : predicatePosition.down = (rfl : 2 = 2) := rfl
example (b : Fin 2) : (predicateDirection b).down = b.isLt := rfl

def alternateContract : Display Dependent where
  position
    | .query _ => Bool
  direction
    | .query arity, selected, _ => if selected then Fin (arity + 1) else PUnit

def contractFamily : Bool → Display Dependent
  | false => dependentContract
  | true => alternateContract

/- These witnesses are kept separate so swapping the `sigma`, `sum.inl`, or
`sum.inr` display branch breaks elaboration or the projection tests. -/
def sigmaLeftPosition :
    (Display.sigma contractFamily).position ⟨false, .query 2⟩ :=
  ⟨2, by omega⟩

def sigmaRightPosition :
    (Display.sigma contractFamily).position ⟨true, .query 2⟩ :=
  true

def sigmaLeftDirection (b : Fin 2) :
    (Display.sigma contractFamily).direction ⟨false, .query 2⟩
      sigmaLeftPosition b :=
  ⟨2, by simp [sigmaLeftPosition]⟩

def sigmaRightDirection (b : Fin 2) :
    (Display.sigma contractFamily).direction ⟨true, .query 2⟩
      sigmaRightPosition b :=
  ⟨2, by omega⟩

example : sigmaLeftPosition.val = 2 := rfl
example : sigmaRightPosition = true := rfl
example (b : Fin 2) : (sigmaLeftDirection b).val = 2 := rfl
example (b : Fin 2) : (sigmaRightDirection b).val = 2 := rfl

def sumLeftPosition :
    (dependentContract.sum alternateContract).position (.inl (.query 2)) :=
  ULift.up ⟨2, by omega⟩

def sumRightPosition :
    (dependentContract.sum alternateContract).position (.inr (.query 2)) :=
  ULift.up true

def sumLeftDirection (b : Fin 2) :
    (dependentContract.sum alternateContract).direction (.inl (.query 2))
      sumLeftPosition b :=
  ULift.up ⟨0, by omega⟩

def sumRightDirection (b : Fin 2) :
    (dependentContract.sum alternateContract).direction (.inr (.query 2))
      sumRightPosition b :=
  ULift.up ⟨2, by omega⟩

example : sumLeftPosition.down.val = 2 := rfl
example : sumRightPosition.down = true := rfl
example (b : Fin 2) : (sumLeftDirection b).down.val = 0 := rfl
example (b : Fin 2) : (sumRightDirection b).down.val = 2 := rfl

def totalPosition : dependentContract.total.A :=
  ⟨.query 2, ⟨2, by omega⟩⟩

def totalDirection : dependentContract.total.B totalPosition :=
  ⟨⟨1, by omega⟩, ⟨2, by simp [totalPosition]⟩⟩

example : dependentContract.forget.toFunA totalPosition = .query 2 := rfl
example : dependentContract.forget.toFunB totalPosition totalDirection =
    (⟨1, by omega⟩ : Fin 2) := rfl

def chartFiberPosition :
    (Display.ofChart dependentContract.forget).total.A :=
  ⟨.query 2, ⟨totalPosition, rfl⟩⟩

def chartFiberDirection :
    (Display.ofChart dependentContract.forget).total.B chartFiberPosition :=
  ⟨⟨1, by omega⟩, ⟨totalDirection, rfl⟩⟩

/- Exercise both chart-equivalence directions and both position/direction
components; dropping an equality fiber or reversing either chart fails one of
these four projections. -/
example :
    (Display.ofChartEquiv dependentContract.forget).toChart.toFunA
      chartFiberPosition = totalPosition := rfl

example :
    (Display.ofChartEquiv dependentContract.forget).toChart.toFunB
      chartFiberPosition chartFiberDirection = totalDirection := rfl

example :
    (Display.ofChartEquiv dependentContract.forget).invChart.toFunA
      totalPosition = chartFiberPosition := rfl

example :
    (Display.ofChartEquiv dependentContract.forget).invChart.toFunB
      totalPosition totalDirection = chartFiberDirection := rfl

def indexedObjData :
    (dependentContract.action Nat).Obj (fun _ : Nat => Nat) dependentObj :=
  ⟨⟨2, by omega⟩, fun direction => direction.1.val + direction.2.val⟩

example (b : Fin 2)
    (direction : dependentContract.direction (.query 2) ⟨2, by omega⟩ b) :
    dependentContract.incidence.src (.query 2) ⟨2, by omega⟩ ⟨b, direction⟩ =
      ⟨.query 2, b⟩ := rfl

example (b : Fin 2)
    (direction : dependentContract.direction (.query 2) ⟨2, by omega⟩ b) :
    (dependentContract.action Nat).src dependentObj ⟨2, by omega⟩
      ⟨b, direction⟩ = b.val := rfl

/- Exercise both curry/uncurry directions of `actionObjEquiv`; selecting only
the base response and forgetting displayed evidence changes these results. -/
example (b : Fin 2)
    (direction : dependentContract.direction (.query 2) ⟨2, by omega⟩ b) :
    (dependentContract.actionObjEquiv (fun _ : Nat => Nat) dependentObj
      indexedObjData).2 b direction = b.val + direction.val := rfl

example (b : Fin 2)
    (direction : dependentContract.direction (.query 2) ⟨2, by omega⟩ b) :
    ((dependentContract.actionObjEquiv (fun _ : Nat => Nat) dependentObj).symm
      dependentObjData).2 ⟨b, direction⟩ = b.val + direction.val := rfl

example :
    dependentContract.bind dependentTree dependentTreeData
      (fun n => .pure (n + 10))
      (fun n evidence =>
        dependentContract.leaf (fun _ : Nat => Nat) (n + 10) (evidence + 1)) =
      ⟨⟨2, by omega⟩, fun b direction =>
        dependentContract.leaf (fun _ : Nat => Nat) (b.val + 10)
          (b.val + direction.val + 1)⟩ := by
  rfl

example :
    dependentContract.transport (fun _ : Nat => Nat)
        (FreeM.liftM_lift_eq_self dependentTree)
        (dependentContract.liftM dependentContract dependentTree dependentTreeData
          (fun a => FreeM.lift a) (Handler.id dependentContract)) =
      dependentTreeData :=
  dependentContract.liftM_id dependentTree dependentTreeData

example :
    dependentContract.transport (fun _ : Nat => Nat)
        (FreeM.liftM_comp dependentTree (fun a => FreeM.lift a)
          (fun a => FreeM.lift a))
        (dependentContract.liftM dependentContract dependentTree
          (dependentContract.liftM dependentContract dependentTree dependentTreeData
            (fun a => FreeM.lift a) (Handler.id dependentContract))
          (fun a => FreeM.lift a) (Handler.id dependentContract)) =
      dependentContract.liftM dependentContract dependentTree dependentTreeData
        (fun a => (FreeM.lift a).liftM fun a => FreeM.lift a)
        ((Handler.id dependentContract).comp (Handler.id dependentContract)) :=
  dependentContract.liftM_comp dependentContract dependentContract
    dependentTree dependentTreeData (fun a => FreeM.lift a)
      (Handler.id dependentContract) (fun a => FreeM.lift a)
      (Handler.id dependentContract)

/-! A three-interface canary for handler composition order.  The first
handler increments displayed positions, while the second doubles them; the
composite must therefore produce `(c + 1) * 2`, not `c * 2 + 1`. -/

abbrev HandlerSource : PFunctor.{0, 0} where
  A := Bool
  B _ := PUnit

abbrev HandlerMiddle : PFunctor.{0, 0} where
  A := Nat
  B _ := PUnit

abbrev HandlerTarget : PFunctor.{0, 0} where
  A := Nat
  B _ := PUnit

abbrev sourceDisplay : Display.{0, 0, 0, 0} HandlerSource where
  position _ := Nat
  direction _ _ _ := PUnit

abbrev middleDisplay : Display.{0, 0, 0, 0} HandlerMiddle where
  position _ := Nat
  direction _ _ _ := PUnit

abbrev targetDisplay : Display.{0, 0, 0, 0} HandlerTarget where
  position _ := Nat
  direction _ _ _ := PUnit

def firstProgram (a : HandlerSource.A) : FreeM HandlerMiddle (HandlerSource.B a) :=
  FreeM.lift (P := HandlerMiddle) (if a then 10 else 20)

def secondProgram (a : HandlerMiddle.A) : FreeM HandlerTarget (HandlerMiddle.B a) :=
  FreeM.lift (P := HandlerTarget) (a + 100)

def firstDisplayedHandler :
    Handler sourceDisplay middleDisplay firstProgram :=
  fun a c =>
    ⟨c + 1, fun _ _ =>
      sourceDisplay.leaf (sourceDisplay.direction a c) .unit .unit⟩

def secondDisplayedHandler :
    Handler middleDisplay targetDisplay secondProgram :=
  fun a c =>
    ⟨c * 2, fun _ _ =>
      middleDisplay.leaf (middleDisplay.direction a c) .unit .unit⟩

def composedDisplayedHandler :
    Handler sourceDisplay targetDisplay
      (fun a => (firstProgram a).liftM secondProgram) :=
  secondDisplayedHandler.comp firstDisplayedHandler

example :
    composedDisplayedHandler true 3 =
      ⟨8, fun _ _ =>
        targetDisplay.leaf (sourceDisplay.direction true 3) .unit .unit⟩ := by
  rfl

end PFunctor.Display.Example

/-! Universe-polymorphic smoke tests. These ensure operation, response,
displayed-position, displayed-direction, and leaf-value universes remain
independent in the public handler laws. -/

universe uA uA' uA'' uB uB' uC uD uC' uD' uC'' uD'' uF uG

namespace PFunctor.Display.UniverseTest

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
  {R : PFunctor.{uA'', uB}}
  (S : Display.{uA, uB, uC, uD} P)
  (T : Display.{uA', uB, uC', uD'} Q)
  (U : Display.{uA'', uB, uC'', uD''} R)
  {E E' : Type uB} {F : E → Type uF} {G : E' → Type uG}

example (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t) :=
  S.liftM_id t d

example (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t)
    (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first)
    (second : (a : Q.A) → FreeM R (Q.B a))
    (dsecond : Handler T U second) :=
  S.liftM_comp T U t d first dfirst second dsecond

example (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t)
    (g : E → FreeM P E')
    (dg : (x : E) → F x → FreeM.Displayed (S.toDisplayedAlgebra G) (g x))
    (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first) :=
  S.liftM_bind T t d g dg first dfirst

example (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first) (a : P.A) (c : S.position a) :=
  Handler.id_comp_apply dfirst a c

example (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first) (a : P.A) (c : S.position a) :=
  Handler.comp_id_apply dfirst a c

end PFunctor.Display.UniverseTest

/-! The core displayed-handler and extension APIs do not require the target
interface's response universe to equal the source response universe. For
Kleisli composition, only the source and intermediate response universes must
agree; the final target remains independent. -/

namespace PFunctor.Display.HeterogeneousResponseUniverseTest

abbrev SmallResponseInterface : PFunctor.{0, 0} where
  A := PUnit
  B _ := Bool

abbrev LargeResponseInterface : PFunctor.{0, 1} where
  A := PUnit
  B _ := ULift.{1} Bool

abbrev smallResponseDisplay : Display.{0, 0, 0, 0} SmallResponseInterface where
  position _ := Bool
  direction _ _ _ := Nat

abbrev largeResponseDisplay : Display.{0, 1, 0, 0} LargeResponseInterface where
  position _ := PUnit
  direction _ _ _ := PUnit

def heterogeneousProgram (_ : SmallResponseInterface.A) :
    FreeM LargeResponseInterface Bool :=
  .pure true

def heterogeneousHandler :
    Handler smallResponseDisplay largeResponseDisplay heterogeneousProgram :=
  fun _ _ => largeResponseDisplay.leaf (fun _ : Bool => Nat) true 7

example :
    heterogeneousHandler .unit false =
      largeResponseDisplay.leaf (fun _ : Bool => Nat) true 7 :=
  rfl

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
  (S : Display.{uA, uB, uC, uD} P)
  (T : Display.{uA', uB', uC', uD'} Q)
  {E E' : Type uB} {F : E → Type uF} {G : E' → Type uG}

example (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first) : Handler S T first :=
  dfirst

example (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t)
    (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first) :=
  S.liftM T t d first dfirst

example (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t)
    (g : E → FreeM P E')
    (dg : (x : E) → F x → FreeM.Displayed (S.toDisplayedAlgebra G) (g x))
    (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first) :=
  S.liftM_bind T t d g dg first dfirst

end PFunctor.Display.HeterogeneousResponseUniverseTest

namespace PFunctor.Display.HeterogeneousCompositionTargetUniverseTest

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
  {R : PFunctor.{uA'', uB'}}
  (S : Display.{uA, uB, uC, uD} P)
  (T : Display.{uA', uB, uC', uD'} Q)
  (U : Display.{uA'', uB', uC'', uD''} R)
  {E : Type uB} {F : E → Type uF}

example
    (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first)
    (second : (a : Q.A) → FreeM R (Q.B a))
    (dsecond : Handler T U second) :
    Handler S U (fun a ↦ (first a).liftM second) :=
  dsecond.comp dfirst

example (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t)
    (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first)
    (second : (a : Q.A) → FreeM R (Q.B a))
    (dsecond : Handler T U second) :=
  S.liftM_comp T U t d first dfirst second dsecond

end PFunctor.Display.HeterogeneousCompositionTargetUniverseTest
