/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Wiring

/-!
Worked examples for recursive base and displayed wiring evaluation.
-/

@[expose] public section

namespace PFunctor.WiringExample

/-- All example interfaces ask one unit query and return a Boolean response. -/
abbrev Interface : PFunctor.{0, 0} := {
  A := Unit
  B := fun _ => Bool
}

/-- Two box kinds with nonconstant arity. -/
inductive Box where
  | choose
  | stop

abbrev Arity : Box → Type 0
  | .choose => Bool
  | .stop => PEmpty

abbrev Dom : (b : Box) → Arity b → PFunctor.{0, 0}
  | .choose, _ => Interface
  | .stop, port => PEmpty.elim port

abbrev Cod (_ : Box) : PFunctor.{0, 0} := Interface

def call (port : Bool) : FreeM (PFunctor.sigma (Dom .choose)) Bool :=
  FreeM.lift (P := PFunctor.sigma (Dom .choose))
    ⟨port, ()⟩

/-- The first box queries its left port. A `true` response selects a second
query at the right port; a `false` response returns immediately. -/
def implementation : (b : Box) →
    (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a)
  | .choose, _ => do
      let answer ← call false
      if answer then call true else pure false
  | .stop, _ => pure true

/-- Proof-relevant contracts: every operation carries one Boolean witness for
each response. -/
abbrev contract : Display.{0, 0, 0, 0} Interface := {
  position := fun _ => Unit
  direction := fun _ _ _ => Bool
}

/-- A deliberately different display on the same base interface. -/
abbrev alternateContract : Display.{0, 0, 0, 0} Interface := {
  position := fun _ => Bool
  direction := fun _ _ _ => Unit
}

abbrev inputDisplay : Bool → Display Interface
  | false => contract
  | true => alternateContract

abbrev domDisplay (b : Box) (port : Arity b) : Display (Dom b port) :=
  match b with
  | .choose => contract

abbrev codDisplay (_ : Box) := contract

def displayedImplementation : (b : Box) →
    Display.Handler (codDisplay b) (Display.sigma (domDisplay b))
      (implementation b)
  | .choose => fun _ _ =>
      ⟨(), fun
        | false, evidence =>
            (Display.sigma (domDisplay .choose)).leaf
              (contract.direction () ()) false evidence
        | true, _evidence =>
            ⟨(), fun answer nextEvidence =>
              (Display.sigma (domDisplay .choose)).leaf
                (contract.direction () ()) answer
                nextEvidence⟩⟩
  | .stop => fun _ _ =>
      (Display.sigma (domDisplay .stop)).leaf
        (contract.direction () ()) true false

/-- Both child wirings share the same external input family. The right child
is itself a zero-arity box. -/
def stopWiring :
    Wiring Box Arity Dom Cod Bool (fun _ => Interface) Interface :=
  .box Box.stop (fun port => PEmpty.elim port)

def stopDisplayed :
    Wiring.Displayed domDisplay codDisplay inputDisplay
      stopWiring contract :=
  by
    unfold stopWiring
    exact .box Box.stop
      (fun port : Arity Box.stop => PEmpty.elim port)
      (fun port : Arity Box.stop => PEmpty.elim port)

def children : (port : Arity .choose) →
    Wiring Box Arity Dom Cod Bool (fun _ => Interface) (Dom .choose port)
  | false => .input false
  | true => stopWiring

def wiring : Wiring Box Arity Dom Cod Bool (fun _ => Interface) Interface :=
  .box Box.choose children

def displayedChildren : (port : Arity .choose) →
    Wiring.Displayed domDisplay codDisplay inputDisplay
      (children port) (domDisplay .choose port)
  | false => .input false
  | true => stopDisplayed

def displayedWiring :
    Wiring.Displayed domDisplay codDisplay inputDisplay wiring contract :=
  .box Box.choose children displayedChildren

def program := Wiring.eval implementation wiring ()

example : program =
    (implementation Box.choose ()).liftM
      (PFunctor.Handler.sigma fun port =>
        Wiring.eval implementation (children port)) :=
  rfl

def verifiedProgram :=
  Wiring.evalDisplayed domDisplay codDisplay inputDisplay
    implementation displayedImplementation displayedWiring () ()

/-- The base response selects the immediate-return branch, while its supplied
proof witness becomes the leaf evidence. -/
example (evidence : Bool) :
    (verifiedProgram.2 false evidence).down = evidence :=
  rfl

/-- The other response selects the recursively wired zero-arity box. -/
example (evidence : Bool) :
    (verifiedProgram.2 true evidence).down = false :=
  by
    change false = false
    rfl

/-! Substitution replaces the shared external family and fuses under `eval`. -/

def replacement (i : Bool) :
    Wiring Box Arity Dom Cod Bool (fun _ => Interface) Interface :=
  .input i

def displayedReplacement (i : Bool) :
    Wiring.Displayed domDisplay codDisplay inputDisplay
      (replacement i) (inputDisplay i) :=
  .input i

example : Wiring.substitute replacement
    (Wiring.input true :
      Wiring Box Arity Dom Cod Bool (fun _ => Interface) Interface) =
      replacement true :=
  rfl

example : Wiring.Displayed.substitute domDisplay codDisplay inputDisplay
    inputDisplay replacement displayedReplacement
      (Wiring.Displayed.input true) = displayedReplacement true :=
  rfl

def substitutedWiring := Wiring.substitute replacement wiring

def substitutedDisplayed :
    Wiring.Displayed domDisplay codDisplay inputDisplay
      substitutedWiring contract :=
  Wiring.Displayed.substitute domDisplay codDisplay inputDisplay
    inputDisplay replacement displayedReplacement displayedWiring

example :
    (program.liftM (PFunctor.Handler.sigma fun i =>
      Wiring.eval implementation (replacement i))) =
      Wiring.eval implementation substitutedWiring () :=
  Wiring.eval_substitute implementation replacement wiring ()

def verifiedSubstituted :=
  Wiring.evalDisplayed domDisplay codDisplay inputDisplay
    implementation displayedImplementation substitutedDisplayed () ()

/-- Displayed fusion is exercised on the recursive box, including its
transport from sequential evaluation to evaluation after substitution. -/
example :
    (Display.sigma inputDisplay).transport (contract.direction () ())
        (Wiring.eval_substitute implementation replacement wiring ())
        (((Display.Handler.sigma inputDisplay (Display.sigma inputDisplay)
          (fun i => Wiring.evalDisplayed domDisplay codDisplay inputDisplay
            implementation displayedImplementation (displayedReplacement i))).comp
          (Wiring.evalDisplayed domDisplay codDisplay inputDisplay
            implementation displayedImplementation displayedWiring)) () ()) =
      verifiedSubstituted :=
  Wiring.evalDisplayed_substitute domDisplay codDisplay inputDisplay inputDisplay
    implementation displayedImplementation replacement displayedReplacement
    displayedWiring () ()

example (evidence : Bool) :
    (verifiedSubstituted.2 false evidence).down = evidence :=
  rfl

/-! The indexed handler combinator also covers nullary and singleton sums. -/

def noInterface (i : PEmpty) : PFunctor := PEmpty.elim i

def noHandler (i : PEmpty) :
    (a : (noInterface i).A) → FreeM Interface ((noInterface i).B a) :=
  PEmpty.elim i

def emptyHandler : (a : (PFunctor.sigma noInterface).A) →
    FreeM Interface ((PFunctor.sigma noInterface).B a) :=
  PFunctor.Handler.sigma noHandler

example (a : (PFunctor.sigma noInterface).A) : False :=
  PEmpty.elim a.1

def oneInterface (_ : Unit) := Interface

def oneHandler (_ : Unit) (a : Interface.A) : FreeM Interface (Interface.B a) :=
  FreeM.lift a

example (a : Interface.A) :
    PFunctor.Handler.sigma oneHandler ⟨(), a⟩ = oneHandler () a :=
  rfl

/-! The public producers preserve all advertised universe separation. -/

universe uBoxes uArity uInputs uA uB uC uD uM

section UniverseCanary

variable {Boxes : Type uBoxes} {Arity : Boxes → Type uArity}
variable {Dom : (box : Boxes) → Arity box → PFunctor.{uA, uB}}
variable {Cod : Boxes → PFunctor.{uA, uB}}
variable {Inputs : Type uInputs}
variable {inputInterface : Inputs → PFunctor.{uA, uB}}
variable (domDisplay : (b : Boxes) → (port : Arity b) →
  Display.{uA, uB, uC, uD} (Dom b port))
variable (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
variable (inputDisplay : (i : Inputs) →
  Display.{uA, uB, uC, uD} (inputInterface i))

def universeWiringInput (i : Inputs) :
    Wiring Boxes Arity Dom Cod Inputs inputInterface (inputInterface i) :=
  .input i

def universeDisplayedInput (i : Inputs) :
    Wiring.Displayed domDisplay codDisplay inputDisplay
      (universeWiringInput i) (inputDisplay i) :=
  .input i

def universeSigmaHandler {I : Type uInputs}
    {P : I → PFunctor.{uA, uB}} {m : Type uB → Type uM}
    (f : (i : I) → PFunctor.Handler m (P i)) :
    PFunctor.Handler m (PFunctor.sigma P) :=
  PFunctor.Handler.sigma f

def universeDisplayedSigmaHandler {I : Type uInputs}
    {P : I → PFunctor.{uA, uB}} {Q : PFunctor.{uA, uB}}
    (S : (i : I) → Display.{uA, uB, uC, uD} (P i))
    (T : Display.{uA, uB, uC, uD} Q)
    {f : (i : I) → (a : (P i).A) → FreeM Q ((P i).B a)}
    (df : (i : I) → Display.Handler (S i) T (f i)) :
    Display.Handler (Display.sigma S) T (PFunctor.Handler.sigma f) :=
  Display.Handler.sigma S T df

end UniverseCanary

end PFunctor.WiringExample
