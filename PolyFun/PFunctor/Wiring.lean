/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Handler.Sigma

/-!
# Recursive wiring of polynomial handlers

`PFunctor.Wiring` is a finite, recursively nested wiring syntax. An `input`
exposes one external interface. A `box` expands an output interface through a
box implementation and recursively wires every interface in that box's
arity. Evaluation folds a wiring to a free handler; `evalDisplayed` folds the
corresponding display witnesses in lockstep.

This construction is unrelated to `DynSystem.Wiring₂`, the existing name for
a binary lens between dynamical-system interfaces.

`eval` is the intrinsic PolyFun form of Theorem 3.1 in Aberlé's
*Compositional Program Verification with Polynomial Functors in Dependent Type
Theory* ([Abe26] in `REFERENCES.md`). A base wiring does not determine a unique
display when one polynomial carries multiple contracts, so `Wiring.Displayed`
separately records compatibility with the declared domain, codomain, and
external-input displays. Folding that witness with `evalDisplayed` is
Aberlé's Theorem 5.3: local displayed handlers compose along the same wiring
as their underlying implementations.
-/

@[expose] public section

universe uBoxes uArity uInputs uInputs' uInputs'' uA uB uC uD

namespace PFunctor

/-- A recursive many-box wiring from an output interface to a family of
external input interfaces. -/
inductive Wiring
    (Boxes : Type uBoxes)
    (Arity : Boxes → Type uArity)
    (Dom : (box : Boxes) → Arity box → PFunctor.{uA, uB})
    (Cod : Boxes → PFunctor.{uA, uB})
    (Inputs : Type uInputs)
    (inputInterface : Inputs → PFunctor.{uA, uB}) :
    PFunctor.{uA, uB} → Type (max uBoxes uArity uInputs) where
  /-- Expose one external input interface. -/
  | input (i : Inputs) : Wiring Boxes Arity Dom Cod Inputs inputInterface (inputInterface i)
  /-- Place a box and recursively wire each interface in its arity. -/
  | box (b : Boxes)
      (children : (port : Arity b) →
        Wiring Boxes Arity Dom Cod Inputs inputInterface (Dom b port)) :
      Wiring Boxes Arity Dom Cod Inputs inputInterface (Cod b)

namespace Wiring

variable {Boxes : Type uBoxes} {Arity : Boxes → Type uArity}
variable {Dom : (box : Boxes) → Arity box → PFunctor.{uA, uB}}
variable {Cod : Boxes → PFunctor.{uA, uB}}
variable {Inputs : Type uInputs} {inputInterface : Inputs → PFunctor.{uA, uB}}

/-- Evaluate a recursive wiring to a free handler from its output to the
indexed coproduct of external inputs. -/
def eval
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a)) :
    {output : PFunctor.{uA, uB}} →
      Wiring Boxes Arity Dom Cod Inputs inputInterface output →
      (a : output.A) → FreeM (PFunctor.sigma inputInterface) (output.B a)
  | _, .input i => fun a =>
      FreeM.lift (P := PFunctor.sigma inputInterface) ⟨i, a⟩
  | _, .box b children => fun a =>
      (implementation b a).liftM
        (PFunctor.Handler.sigma fun port => eval implementation (children port))

@[simp]
theorem eval_input
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (i : Inputs) (a : (inputInterface i).A) :
    eval implementation (.input i) a =
      FreeM.lift (P := PFunctor.sigma inputInterface) ⟨i, a⟩ :=
  rfl

@[simp]
theorem eval_box
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (b : Boxes)
    (children : (port : Arity b) →
      Wiring Boxes Arity Dom Cod Inputs inputInterface (Dom b port))
    (a : (Cod b).A) :
    eval implementation (.box b children) a =
      (implementation b a).liftM
        (PFunctor.Handler.sigma fun port => eval implementation (children port)) :=
  rfl

/-- A display-compatible refinement of a base wiring.

This is separate data because the same base polynomial can occur with
different displays. Each box child must carry the particular display declared
for that input port. -/
inductive Displayed
    (domDisplay : (b : Boxes) → (port : Arity b) →
      Display.{uA, uB, uC, uD} (Dom b port))
    (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
    (inputDisplay : (i : Inputs) →
      Display.{uA, uB, uC, uD} (inputInterface i)) :
    {output : PFunctor.{uA, uB}} →
      Wiring Boxes Arity Dom Cod Inputs inputInterface output →
      Display.{uA, uB, uC, uD} output →
      Type (max uBoxes uArity uInputs uA uB uC uD) where
  /-- An external input carries its declared input display. -/
  | input (i : Inputs) :
      Displayed domDisplay codDisplay inputDisplay (.input i) (inputDisplay i)
  /-- A box output carries its codomain display, and every recursively wired
  port carries that port's declared domain display. -/
  | box (b : Boxes)
      (children : (port : Arity b) →
        Wiring Boxes Arity Dom Cod Inputs inputInterface (Dom b port))
      (displayedChildren : (port : Arity b) →
        Displayed domDisplay codDisplay inputDisplay
          (children port) (domDisplay b port)) :
      Displayed domDisplay codDisplay inputDisplay
        (.box b children) (codDisplay b)

/-- Evaluate all displayed box implementations through a recursive wiring. -/
def evalDisplayed
    (domDisplay : (b : Boxes) → (port : Arity b) →
      Display.{uA, uB, uC, uD} (Dom b port))
    (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
    (inputDisplay : (i : Inputs) →
      Display.{uA, uB, uC, uD} (inputInterface i))
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (displayedImplementation : (b : Boxes) →
      Display.Handler (codDisplay b) (Display.sigma (domDisplay b))
        (implementation b)) :
    {output : PFunctor.{uA, uB}} →
      {wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output} →
      {outputDisplay : Display.{uA, uB, uC, uD} output} →
      Displayed domDisplay codDisplay inputDisplay wiring outputDisplay →
      Display.Handler outputDisplay (Display.sigma inputDisplay)
        (eval implementation wiring)
  | _, _, _, .input i => Display.Handler.sigmaInj inputDisplay i
  | _, _, _, .box b children displayedChildren =>
      (Display.Handler.sigma (domDisplay b) (Display.sigma inputDisplay)
        (fun port => evalDisplayed domDisplay codDisplay inputDisplay implementation
          displayedImplementation (displayedChildren port))).comp
        (displayedImplementation b)

@[simp]
theorem evalDisplayed_input
    (domDisplay : (b : Boxes) → (port : Arity b) →
      Display.{uA, uB, uC, uD} (Dom b port))
    (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
    (inputDisplay : (i : Inputs) →
      Display.{uA, uB, uC, uD} (inputInterface i))
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (displayedImplementation : (b : Boxes) →
      Display.Handler (codDisplay b) (Display.sigma (domDisplay b))
        (implementation b))
    (i : Inputs) :
    evalDisplayed domDisplay codDisplay inputDisplay implementation
      displayedImplementation (Displayed.input i) =
        Display.Handler.sigmaInj inputDisplay i :=
  rfl

@[simp]
theorem evalDisplayed_box
    (domDisplay : (b : Boxes) → (port : Arity b) →
      Display.{uA, uB, uC, uD} (Dom b port))
    (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
    (inputDisplay : (i : Inputs) →
      Display.{uA, uB, uC, uD} (inputInterface i))
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (displayedImplementation : (b : Boxes) →
      Display.Handler (codDisplay b) (Display.sigma (domDisplay b))
        (implementation b))
    (b : Boxes)
    (children : (port : Arity b) →
      Wiring Boxes Arity Dom Cod Inputs inputInterface (Dom b port))
    (displayedChildren : (port : Arity b) →
      Displayed domDisplay codDisplay inputDisplay
        (children port) (domDisplay b port)) :
    evalDisplayed domDisplay codDisplay inputDisplay implementation
        displayedImplementation (.box b children displayedChildren) =
      (Display.Handler.sigma (domDisplay b) (Display.sigma inputDisplay)
        (fun port => evalDisplayed domDisplay codDisplay inputDisplay implementation
          displayedImplementation (displayedChildren port))).comp
        (displayedImplementation b) :=
  rfl

/-- Substitute a wiring for every external input of another wiring. -/
def substitute
    {Inputs' : Type uInputs'} {inputInterface' : Inputs' → PFunctor.{uA, uB}}
    (replacement : (i : Inputs) →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' (inputInterface i)) :
    {output : PFunctor.{uA, uB}} →
      Wiring Boxes Arity Dom Cod Inputs inputInterface output →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' output
  | _, .input i => replacement i
  | _, .box b children => .box b (fun port => substitute replacement (children port))

@[simp]
theorem substitute_input
    {Inputs' : Type uInputs'} {inputInterface' : Inputs' → PFunctor.{uA, uB}}
    (replacement : (i : Inputs) →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' (inputInterface i))
    (i : Inputs) :
    substitute replacement (.input i) = replacement i :=
  rfl

@[simp]
theorem substitute_box
    {Inputs' : Type uInputs'} {inputInterface' : Inputs' → PFunctor.{uA, uB}}
    (replacement : (i : Inputs) →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' (inputInterface i))
    (b : Boxes)
    (children : (port : Arity b) →
      Wiring Boxes Arity Dom Cod Inputs inputInterface (Dom b port)) :
    substitute replacement (.box b children) =
      .box b (fun port => substitute replacement (children port)) :=
  rfl

/-- Replacing every external input by the corresponding input wiring is the
identity substitution. -/
@[simp]
theorem substitute_id
    {output : PFunctor.{uA, uB}}
    (wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output) :
    substitute (fun i => Wiring.input i) wiring = wiring := by
  induction wiring with
  | input i => rfl
  | box b children ih =>
      simp only [substitute_box]
      congr
      funext port
      exact ih port

/-- Successive wiring substitutions agree with their pointwise composite. -/
theorem substitute_assoc
    {Inputs' : Type uInputs'} {inputInterface' : Inputs' → PFunctor.{uA, uB}}
    {Inputs'' : Type uInputs''} {inputInterface'' : Inputs'' → PFunctor.{uA, uB}}
    (first : (i : Inputs) →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' (inputInterface i))
    (second : (i : Inputs') →
      Wiring Boxes Arity Dom Cod Inputs'' inputInterface'' (inputInterface' i))
    {output : PFunctor.{uA, uB}}
    (wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output) :
    substitute second (substitute first wiring) =
      substitute (fun i => substitute second (first i)) wiring := by
  induction wiring with
  | input i => rfl
  | box b children ih =>
      simp only [substitute_box]
      congr
      funext port
      exact ih port

namespace Displayed

/-- Substitute display-compatible external wirings through a
display-compatible outer wiring. -/
def substitute
    (domDisplay : (b : Boxes) → (port : Arity b) →
      Display.{uA, uB, uC, uD} (Dom b port))
    (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
    (inputDisplay : (i : Inputs) →
      Display.{uA, uB, uC, uD} (inputInterface i))
    {Inputs' : Type uInputs'} {inputInterface' : Inputs' → PFunctor.{uA, uB}}
    (inputDisplay' : (i : Inputs') →
      Display.{uA, uB, uC, uD} (inputInterface' i))
    (replacement : (i : Inputs) →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' (inputInterface i))
    (displayedReplacement : (i : Inputs) →
      Displayed domDisplay codDisplay inputDisplay'
        (replacement i) (inputDisplay i)) :
    {output : PFunctor.{uA, uB}} →
      {wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output} →
      {outputDisplay : Display.{uA, uB, uC, uD} output} →
      Displayed domDisplay codDisplay inputDisplay wiring outputDisplay →
      Displayed domDisplay codDisplay inputDisplay'
        (Wiring.substitute replacement wiring) outputDisplay
  | _, _, _, .input i => displayedReplacement i
  | _, _, _, .box b children displayedChildren =>
      Displayed.box b
        (fun port => Wiring.substitute replacement (children port))
        (fun port => substitute domDisplay codDisplay inputDisplay inputDisplay'
          replacement displayedReplacement (displayedChildren port))

@[simp]
theorem substitute_input
    (domDisplay : (b : Boxes) → (port : Arity b) →
      Display.{uA, uB, uC, uD} (Dom b port))
    (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
    (inputDisplay : (i : Inputs) →
      Display.{uA, uB, uC, uD} (inputInterface i))
    {Inputs' : Type uInputs'} {inputInterface' : Inputs' → PFunctor.{uA, uB}}
    (inputDisplay' : (i : Inputs') →
      Display.{uA, uB, uC, uD} (inputInterface' i))
    (replacement : (i : Inputs) →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' (inputInterface i))
    (displayedReplacement : (i : Inputs) →
      Displayed domDisplay codDisplay inputDisplay'
        (replacement i) (inputDisplay i))
    (i : Inputs) :
    substitute domDisplay codDisplay inputDisplay inputDisplay' replacement
      displayedReplacement (Displayed.input i) = displayedReplacement i :=
  rfl

@[simp]
theorem substitute_box
    (domDisplay : (b : Boxes) → (port : Arity b) →
      Display.{uA, uB, uC, uD} (Dom b port))
    (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
    (inputDisplay : (i : Inputs) →
      Display.{uA, uB, uC, uD} (inputInterface i))
    {Inputs' : Type uInputs'} {inputInterface' : Inputs' → PFunctor.{uA, uB}}
    (inputDisplay' : (i : Inputs') →
      Display.{uA, uB, uC, uD} (inputInterface' i))
    (replacement : (i : Inputs) →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' (inputInterface i))
    (displayedReplacement : (i : Inputs) →
      Displayed domDisplay codDisplay inputDisplay'
        (replacement i) (inputDisplay i))
    (b : Boxes)
    (children : (port : Arity b) →
      Wiring Boxes Arity Dom Cod Inputs inputInterface (Dom b port))
    (displayedChildren : (port : Arity b) →
      Displayed domDisplay codDisplay inputDisplay
        (children port) (domDisplay b port)) :
    substitute domDisplay codDisplay inputDisplay inputDisplay' replacement
        displayedReplacement (Displayed.box b children displayedChildren) =
      Displayed.box b
        (fun port => Wiring.substitute replacement (children port))
        (fun port => substitute domDisplay codDisplay inputDisplay inputDisplay'
          replacement displayedReplacement (displayedChildren port)) :=
  rfl

end Displayed

/-- Evaluating a substitution is free-handler fusion: first evaluate the
outer wiring, then interpret each former external input by its replacement. -/
theorem eval_substitute
    {Inputs' : Type uInputs'} {inputInterface' : Inputs' → PFunctor.{uA, uB}}
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (replacement : (i : Inputs) →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' (inputInterface i))
    {output : PFunctor.{uA, uB}}
    (wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output)
    (a : output.A) :
    (eval implementation wiring a).liftM
        (PFunctor.Handler.sigma fun i => eval implementation (replacement i)) =
      eval implementation (substitute replacement wiring) a := by
  induction wiring with
  | input i =>
      exact (FreeM.liftM_lift
        (PFunctor.Handler.sigma fun i => eval implementation (replacement i))
        ⟨i, a⟩)
  | box b children ih =>
      simp only [substitute, eval]
      rw [FreeM.liftM_comp]
      congr
      funext ia
      exact ih ia.1 ia.2

/-- Displayed evaluation commutes with wiring substitution. The left side
first evaluates the outer displayed wiring and then evaluates each displayed
replacement; transport accounts for the corresponding base-tree fusion law
`eval_substitute`. -/
theorem evalDisplayed_substitute
    (domDisplay : (b : Boxes) → (port : Arity b) →
      Display.{uA, uB, uC, uD} (Dom b port))
    (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
    (inputDisplay : (i : Inputs) →
      Display.{uA, uB, uC, uD} (inputInterface i))
    {Inputs' : Type uInputs'} {inputInterface' : Inputs' → PFunctor.{uA, uB}}
    (inputDisplay' : (i : Inputs') →
      Display.{uA, uB, uC, uD} (inputInterface' i))
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (displayedImplementation : (b : Boxes) →
      Display.Handler (codDisplay b) (Display.sigma (domDisplay b))
        (implementation b))
    (replacement : (i : Inputs) →
      Wiring Boxes Arity Dom Cod Inputs' inputInterface' (inputInterface i))
    (displayedReplacement : (i : Inputs) →
      Displayed domDisplay codDisplay inputDisplay'
        (replacement i) (inputDisplay i))
    {output : PFunctor.{uA, uB}}
    {wiring : Wiring Boxes Arity Dom Cod Inputs inputInterface output}
    {outputDisplay : Display.{uA, uB, uC, uD} output}
    (displayedWiring :
      Displayed domDisplay codDisplay inputDisplay wiring outputDisplay)
    (a : output.A) (c : outputDisplay.position a) :
    (Display.sigma inputDisplay').transport (outputDisplay.direction a c)
        (eval_substitute implementation replacement wiring a)
        (((Display.Handler.sigma inputDisplay (Display.sigma inputDisplay')
          (fun i => evalDisplayed domDisplay codDisplay inputDisplay'
            implementation displayedImplementation (displayedReplacement i))).comp
          (evalDisplayed domDisplay codDisplay inputDisplay implementation
            displayedImplementation displayedWiring)) a c) =
      evalDisplayed domDisplay codDisplay inputDisplay' implementation
        displayedImplementation
        (Displayed.substitute domDisplay codDisplay inputDisplay inputDisplay'
          replacement displayedReplacement displayedWiring) a c := by
  induction displayedWiring with
  | input i =>
      exact Display.Handler.comp_id_apply
        (Display.Handler.sigma inputDisplay (Display.sigma inputDisplay')
          (fun i => evalDisplayed domDisplay codDisplay inputDisplay'
            implementation displayedImplementation (displayedReplacement i)))
        ⟨i, a⟩ c
  | box b children displayedChildren ih =>
      let first := PFunctor.Handler.sigma fun port =>
        eval implementation (children port)
      let second := PFunctor.Handler.sigma fun i =>
        eval implementation (replacement i)
      let final := PFunctor.Handler.sigma fun port =>
        eval implementation (Wiring.substitute replacement (children port))
      let dfirst := Display.Handler.sigma (domDisplay b)
        (Display.sigma inputDisplay)
        (fun port => evalDisplayed domDisplay codDisplay inputDisplay
          implementation displayedImplementation (displayedChildren port))
      let dsecond := Display.Handler.sigma inputDisplay
        (Display.sigma inputDisplay')
        (fun i => evalDisplayed domDisplay codDisplay inputDisplay'
          implementation displayedImplementation (displayedReplacement i))
      let dfinal := Display.Handler.sigma (domDisplay b)
        (Display.sigma inputDisplay')
        (fun port => evalDisplayed domDisplay codDisplay inputDisplay'
          implementation displayedImplementation
            (Displayed.substitute domDisplay codDisplay inputDisplay inputDisplay'
              replacement displayedReplacement (displayedChildren port)))
      let childEq : (fun x => (first x).liftM second) = final := by
        funext x
        exact eval_substitute implementation replacement (children x.1) x.2
      let totalEq :=
        (FreeM.liftM_comp (implementation b a) first second).trans
          (congrArg ((implementation b a).liftM ·) childEq)
      rw [(Display.sigma inputDisplay').transport_proof_irrel
        ((codDisplay b).direction a c)
        (eval_substitute implementation replacement (.box b children) a)
        totalEq]
      change (Display.sigma inputDisplay').transport
          ((codDisplay b).direction a c) totalEq
          (dsecond.comp (dfirst.comp (displayedImplementation b)) a c) =
        dfinal.comp (displayedImplementation b) a c
      calc
        _ = (Display.sigma inputDisplay').transport
              ((codDisplay b).direction a c)
              (congrArg ((implementation b a).liftM ·) childEq)
              ((Display.sigma inputDisplay').transport
                ((codDisplay b).direction a c)
                (FreeM.liftM_comp (implementation b a) first second)
                (dsecond.comp (dfirst.comp (displayedImplementation b)) a c)) :=
          ((Display.sigma inputDisplay').transport_trans
            ((codDisplay b).direction a c)
            (FreeM.liftM_comp (implementation b a) first second)
            (congrArg ((implementation b a).liftM ·) childEq) _).symm
        _ = (Display.sigma inputDisplay').transport
              ((codDisplay b).direction a c)
              (congrArg ((implementation b a).liftM ·) childEq)
              ((dsecond.comp dfirst).comp (displayedImplementation b) a c) := by
          congr 1
          exact Display.Handler.comp_assoc_apply
            (displayedImplementation b) dfirst dsecond a c
        _ = _ := by
          exact (Display.sigma (domDisplay b)).liftM_congr
            (Display.sigma inputDisplay') (implementation b a)
            (displayedImplementation b a c) childEq
            (dsecond.comp dfirst) dfinal (fun x dx => by
              rw [(Display.sigma inputDisplay').transport_proof_irrel
                ((Display.sigma (domDisplay b)).direction x dx)
                (congrFun childEq x)
                (eval_substitute implementation replacement (children x.1) x.2)]
              exact ih x.1 x.2 dx)

end Wiring
end PFunctor
