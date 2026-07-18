/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Handler
public import PolyFun.PFunctor.Display.Parallel
public import PolyFun.PFunctor.Free.Parallel

/-!
# Displayed parallel free programs and handlers

This module lifts the display-independent operations from
`PolyFun.PFunctor.Free.Parallel` to Aberlé's separable parallel display.
Keeping these lifts in the display layer prevents ordinary free-program
clients from acquiring verification dependencies.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uA₄ uB uC₁ uD₁ uC₂ uD₂ uC₃ uD₃ uC₄ uD₄
  uE uV uF uG uH

namespace PFunctor
namespace FreeM
namespace Displayed

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
  {E : Type uE} {V : Type uV}
  {S : Display.{uA₁, uB, uC₁, uD₁} P}
  {T : Display.{uA₂, uB, uC₂, uD₂} Q}
  {I : E → Type uF} {J : V → Type uG}

/-- Displayed lift of the one-sided left program embedding, with a map on
leaf evidence. -/
def leftMap {K : E → Type uH} (mapLeaf : (x : E) → I x → K x)
    (program : FreeM P E)
    (displayed : FreeM.Displayed (S.toDisplayedAlgebra I) program) :
    FreeM.Displayed
      ((Display.parallelSum S T).toDisplayedAlgebra K)
      (FreeM.left (Q := Q) program) :=
  match program, displayed with
  | .pure x, d => (Display.parallelSum S T).leaf K x (mapLeaf x d.down)
  | .liftBind _ next, ⟨c, children⟩ =>
      ⟨ULift.up c, fun answer evidence =>
        leftMap mapLeaf (next answer) (children answer evidence.down)⟩

@[simp] theorem leftMap_pure {K : E → Type uH}
    (mapLeaf : (x : E) → I x → K x) (x : E) (dx : I x) :
    leftMap (S := S) (T := T) mapLeaf (pure x) (S.leaf I x dx) =
      (Display.parallelSum S T).leaf K x (mapLeaf x dx) := rfl

@[simp] theorem leftMap_liftBind {K : E → Type uH}
    (mapLeaf : (x : E) → I x → K x) (a : P.A)
    (next : P.B a → FreeM P E) (c : S.position a)
    (children : (answer : P.B a) → S.direction a c answer →
      FreeM.Displayed (S.toDisplayedAlgebra I) (next answer)) :
    leftMap (T := T) mapLeaf ((FreeM.lift a).bind next) ⟨c, children⟩ =
      ⟨ULift.up c, fun answer evidence =>
        leftMap (T := T) mapLeaf (next answer)
          (children answer evidence.down)⟩ := rfl

/-- Displayed lift of the one-sided left program embedding. -/
def left (program : FreeM P E)
    (displayed : FreeM.Displayed (S.toDisplayedAlgebra I) program) :
    FreeM.Displayed
      ((Display.parallelSum S T).toDisplayedAlgebra I)
      (FreeM.left (Q := Q) program) :=
  leftMap (fun _ value => value) program displayed

/-- Displayed lift of the one-sided right program embedding, with a map on
leaf evidence. -/
def rightMap {K : E → Type uH} (mapLeaf : (x : E) → I x → K x)
    (program : FreeM Q E)
    (displayed : FreeM.Displayed (T.toDisplayedAlgebra I) program) :
    FreeM.Displayed
      ((Display.parallelSum S T).toDisplayedAlgebra K)
      (FreeM.right (P := P) program) :=
  match program, displayed with
  | .pure x, d => (Display.parallelSum S T).leaf K x (mapLeaf x d.down)
  | .liftBind _ next, ⟨c, children⟩ =>
      ⟨ULift.up c, fun answer evidence =>
        rightMap mapLeaf (next answer) (children answer evidence.down)⟩

@[simp] theorem rightMap_pure {K : E → Type uH}
    (mapLeaf : (x : E) → I x → K x) (x : E) (dx : I x) :
    rightMap (S := S) (T := T) mapLeaf (pure x) (T.leaf I x dx) =
      (Display.parallelSum S T).leaf K x (mapLeaf x dx) := rfl

@[simp] theorem rightMap_liftBind {K : E → Type uH}
    (mapLeaf : (x : E) → I x → K x) (b : Q.A)
    (next : Q.B b → FreeM Q E) (c : T.position b)
    (children : (answer : Q.B b) → T.direction b c answer →
      FreeM.Displayed (T.toDisplayedAlgebra I) (next answer)) :
    rightMap (S := S) mapLeaf ((FreeM.lift b).bind next) ⟨c, children⟩ =
      ⟨ULift.up c, fun answer evidence =>
        rightMap (S := S) mapLeaf (next answer)
          (children answer evidence.down)⟩ := rfl

/-- Displayed lift of the one-sided right program embedding. -/
def right (program : FreeM Q E)
    (displayed : FreeM.Displayed (T.toDisplayedAlgebra I) program) :
    FreeM.Displayed
      ((Display.parallelSum S T).toDisplayedAlgebra I)
      (FreeM.right (P := P) program) :=
  rightMap (fun _ value => value) program displayed

/-- Continue displayed parallel execution after the left program has
returned. -/
def parallelAfterLeftReturn (x : E) (dx : I x)
    (rightProgram : FreeM Q V)
    (rightDisplayed : FreeM.Displayed (T.toDisplayedAlgebra J) rightProgram) :
    FreeM.Displayed
      ((Display.parallelSum S T).toDisplayedAlgebra
        (fun result => I result.1 × J result.2))
      (FreeM.parallel (.pure x) rightProgram) :=
  match rightProgram, rightDisplayed with
  | .pure y, dy =>
      (Display.parallelSum S T).leaf
        (fun result : E × V => I result.1 × J result.2)
        (x, y) (dx, dy.down)
  | .liftBind _ next, ⟨c, children⟩ =>
      ⟨ULift.up c, fun answer evidence =>
        parallelAfterLeftReturn x dx (next answer)
          (children answer evidence.down)⟩

@[simp] theorem parallelAfterLeftReturn_pure
    (x : E) (dx : I x) (y : V) (dy : J y) :
    parallelAfterLeftReturn (S := S) (T := T) x dx (pure y)
        (T.leaf J y dy) =
      (Display.parallelSum S T).leaf
        (fun result : E × V => I result.1 × J result.2)
        (x, y) (dx, dy) := rfl

@[simp] theorem parallelAfterLeftReturn_liftBind
    (x : E) (dx : I x) (b : Q.A) (next : Q.B b → FreeM Q V)
    (c : T.position b)
    (children : (answer : Q.B b) → T.direction b c answer →
      FreeM.Displayed (T.toDisplayedAlgebra J) (next answer)) :
    parallelAfterLeftReturn (S := S) x dx
        ((FreeM.lift b).bind next) ⟨c, children⟩ =
      ⟨ULift.up c, fun answer evidence =>
        parallelAfterLeftReturn (S := S) x dx (next answer)
          (children answer evidence.down)⟩ := rfl

/-- Displayed lockstep composition of two displayed free programs. -/
def parallel (leftProgram : FreeM P E) (rightProgram : FreeM Q V)
    (leftDisplayed : FreeM.Displayed (S.toDisplayedAlgebra I) leftProgram)
    (rightDisplayed : FreeM.Displayed (T.toDisplayedAlgebra J) rightProgram) :
    FreeM.Displayed
      ((Display.parallelSum S T).toDisplayedAlgebra
        (fun result => I result.1 × J result.2))
      (FreeM.parallel leftProgram rightProgram) :=
  match leftProgram, leftDisplayed with
  | .pure x, dx =>
      parallelAfterLeftReturn x dx.down rightProgram rightDisplayed
  | .liftBind _ next, ⟨cP, childrenP⟩ =>
      match rightProgram, rightDisplayed with
      | .pure y, dy =>
          ⟨ULift.up cP, fun answer evidence =>
            parallel (next answer) (.pure y)
              (childrenP answer evidence.down) dy⟩
      | .liftBind _ nextQ, ⟨cQ, childrenQ⟩ =>
          ⟨(cP, cQ), fun answer evidence =>
            parallel (next answer.1) (nextQ answer.2)
              (childrenP answer.1 evidence.1)
              (childrenQ answer.2 evidence.2)⟩

@[simp] theorem parallel_pure_pure
    (x : E) (dx : I x) (y : V) (dy : J y) :
    parallel (S := S) (T := T) (pure x) (pure y)
        (S.leaf I x dx) (T.leaf J y dy) =
      (Display.parallelSum S T).leaf
        (fun result : E × V => I result.1 × J result.2)
        (x, y) (dx, dy) := rfl

@[simp] theorem parallel_liftBind_pure
    (a : P.A) (next : P.B a → FreeM P E) (c : S.position a)
    (children : (answer : P.B a) → S.direction a c answer →
      FreeM.Displayed (S.toDisplayedAlgebra I) (next answer))
    (y : V) (dy : J y) :
    parallel (T := T) ((FreeM.lift a).bind next) (pure y) ⟨c, children⟩
        (T.leaf J y dy) =
      ⟨ULift.up c, fun answer evidence =>
        parallel (T := T) (next answer) (.pure y)
          (children answer evidence.down) (T.leaf J y dy)⟩ := rfl

@[simp] theorem parallel_pure_liftBind
    (x : E) (dx : I x) (b : Q.A) (next : Q.B b → FreeM Q V)
    (c : T.position b)
    (children : (answer : Q.B b) → T.direction b c answer →
      FreeM.Displayed (T.toDisplayedAlgebra J) (next answer)) :
    parallel (S := S) (pure x) ((FreeM.lift b).bind next) (S.leaf I x dx)
        ⟨c, children⟩ =
      ⟨ULift.up c, fun answer evidence =>
        parallel (S := S) (.pure x) (next answer) (S.leaf I x dx)
          (children answer evidence.down)⟩ := rfl

@[simp] theorem parallel_liftBind_liftBind
    (a : P.A) (nextP : P.B a → FreeM P E) (cP : S.position a)
    (childrenP : (answer : P.B a) → S.direction a cP answer →
      FreeM.Displayed (S.toDisplayedAlgebra I) (nextP answer))
    (b : Q.A) (nextQ : Q.B b → FreeM Q V) (cQ : T.position b)
    (childrenQ : (answer : Q.B b) → T.direction b cQ answer →
      FreeM.Displayed (T.toDisplayedAlgebra J) (nextQ answer)) :
    parallel ((FreeM.lift a).bind nextP) ((FreeM.lift b).bind nextQ)
        ⟨cP, childrenP⟩ ⟨cQ, childrenQ⟩ =
      ⟨(cP, cQ), fun answer evidence =>
        parallel (nextP answer.1) (nextQ answer.2)
          (childrenP answer.1 evidence.1)
          (childrenQ answer.2 evidence.2)⟩ := rfl

end Displayed
end FreeM

namespace Display
namespace Handler

/-- Displayed lift of pointwise parallel handler composition. -/
def parallel
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftHandler : PFunctor.Handler (FreeM R) P}
    {rightHandler : PFunctor.Handler (FreeM V) Q}
    (displayedLeft : Display.Handler S U leftHandler)
    (displayedRight : Display.Handler T W rightHandler) :
    Display.Handler (Display.parallelSum S T) (Display.parallelSum U W)
      (PFunctor.Handler.parallel leftHandler rightHandler)
  | .left a, contract =>
      FreeM.Displayed.leftMap (T := W) (fun _ => ULift.up) (leftHandler a)
        (displayedLeft a contract.down)
  | .right b, contract =>
      FreeM.Displayed.rightMap (S := U) (fun _ => ULift.up) (rightHandler b)
        (displayedRight b contract.down)
  | .both a b, contract =>
      FreeM.Displayed.parallel (leftHandler a) (rightHandler b)
        (displayedLeft a contract.1)
        (displayedRight b contract.2)

@[simp] theorem parallel_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftHandler : PFunctor.Handler (FreeM R) P}
    {rightHandler : PFunctor.Handler (FreeM V) Q}
    (displayedLeft : Display.Handler S U leftHandler)
    (displayedRight : Display.Handler T W rightHandler)
    (a : P.A) (contract : S.position a) :
    parallel displayedLeft displayedRight (.left a) (ULift.up contract) =
      FreeM.Displayed.leftMap (T := W) (fun _ => ULift.up) (leftHandler a)
        (displayedLeft a contract) := rfl

@[simp] theorem parallel_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftHandler : PFunctor.Handler (FreeM R) P}
    {rightHandler : PFunctor.Handler (FreeM V) Q}
    (displayedLeft : Display.Handler S U leftHandler)
    (displayedRight : Display.Handler T W rightHandler)
    (b : Q.A) (contract : T.position b) :
    parallel displayedLeft displayedRight (.right b) (ULift.up contract) =
      FreeM.Displayed.rightMap (S := U) (fun _ => ULift.up) (rightHandler b)
        (displayedRight b contract) := rfl

@[simp] theorem parallel_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftHandler : PFunctor.Handler (FreeM R) P}
    {rightHandler : PFunctor.Handler (FreeM V) Q}
    (displayedLeft : Display.Handler S U leftHandler)
    (displayedRight : Display.Handler T W rightHandler)
    (a : P.A) (b : Q.A)
    (leftContract : S.position a) (rightContract : T.position b) :
    parallel displayedLeft displayedRight (.both a b)
        (leftContract, rightContract) =
      FreeM.Displayed.parallel (leftHandler a) (rightHandler b)
        (displayedLeft a leftContract) (displayedRight b rightContract) := rfl

/-- Parallel composition preserves displayed identity handlers, after the
ordinary parallel-identity equation aligns their base-handler indices. -/
@[simp] theorem parallel_id
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    transport (PFunctor.Handler.parallel_id P Q)
        (parallel (id S) (id T)) =
      id (Display.parallelSum S T) := by
  funext operation contract
  rw [transport_apply]
  cases operation <;> rfl

end Handler
end Display
end PFunctor
