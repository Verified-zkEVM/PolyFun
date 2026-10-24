/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.ModuleElaboration

/-!
# Materializing checked finite descriptions

Rendering consumes the checked polynomial tree, not the upstream AST. Generated
Lean constructor expressions are candidates: a separate kernel acceptance equation
checks them against elaboration of the original retained module. Keeping bodies
explicit avoids repeating frontend reduction inside downstream semantic proofs.
-/

public section

namespace Cryptol.Translation.Materialize

open Polymorphic

private def variableCode : Nat → String
  | 0 => ".zero"
  | n + 1 => s!"(.succ {variableCode n})"

private def app (name : String) (args : List String) : String :=
  "(" ++ name ++ " " ++ String.intercalate " " args ++ ")"

private def finiteCases : List String → String
  | [] => "(fun i => Fin.elim0 i)"
  | x :: xs => app "Fin.cases" [x, finiteCases xs]

private def op {w : Scope} : {s : w.ValueSort} → (head : Op w s) →
    (Fin head.arity → Except String String) → Except String String
  | _, .numAbs _, children => do
      return app "Term.numAbs" [← children 0]
  | _, .typeAbs _, children => do
      return app "Term.typeAbs" [← children 0]
  | _, .numApp s e, children => do
      return app "Term.numApp" ["(s := " ++ reprStr s ++ ")", ← children 0,
        "(" ++ reprStr e ++ ")"]
  | _, .typeApp s a, children => do
      return app "Term.typeApp" ["(s := " ++ reprStr s ++ ")", ← children 0,
        "(" ++ reprStr a ++ ")"]
  | _, .proofAbs c _, children => do
      return app "Term.proofAbs" ["(" ++ reprStr c ++ ")", ← children 0]
  | _, .proofApp c s _, children => do
      return app "Term.proofApp" ["(c := " ++ reprStr c ++ ")", "(s := " ++ reprStr s ++ ")",
        ← children 0,
      "(by with_unfolding_all exact " ++
        "Cryptol.Translation.ConstraintEvidence.of_prove (by decide))"]
  | _, .lam _ _, children => do
      return app "Term.lam" [← children 0]
  | _, .app _ _, children => do
      return app "Term.app" [← children 0, ← children 1]
  | _, .letE _ _, children => do
      return app "Term.letE" [← children 0, ← children 1]
  | _, .pair _ _, children => do
      return app "Term.pair" [← children 0, ← children 1]
  | _, .fst _ _, children => do
      return app "Term.fst" [← children 0]
  | _, .snd _ _, children => do
      return app "Term.snd" [← children 0]
  | _, .generate n _, children => do
      return app "Term.generate" ["(" ++ reprStr n ++ ")", ← children 0]
  | _, .index _ _, children => do
      return app "Term.index" [← children 0, ← children 1]
  | _, .ite _, children => do
      return app "Term.ite" [← children 0, ← children 1, ← children 2]
  | _, .fix _, children => do
      return app "Term.fix" [← children 0]
  | _, .letRec bs _, children => do
      let rhs ← (List.finRange bs.length).mapM (fun i => children i.succ)
      return app "Term.letRec" ["(" ++ reprStr bs ++ ")", finiteCases rhs, ← children 0]
  | _, .bit b, _ => do
      return app "Term.bit" [reprStr b]
  | _, .integer n, _ => do
      return app "Term.integer" ["(" ++ reprStr n ++ ")"]
  | _, _, _ => throw "constructor requires a public materialization rule"

/-- Render the accepted finite tree through its generic polynomial fold. -/
def term {w : Scope} {Γ : List w.ValueSort} {s : w.ValueSort}
    (body : Term w Γ s) : Except String String :=
  body.fold (P := signature.polynomial) (D := fun _ => Except String String)
    (fun _ x => .ok (app "Term.var" [variableCode x.index]))
    (fun _ head children => op head.code.2 children)

/-- Render each body with its actual lexical context and recursive-group identity. -/
def declarations {w : Scope} : {Γ Δ : Signatures w} → Declarations w Γ Δ →
    Except String (List Lean.Json)
  | _, _, .nil _ => .ok []
  | Γ, _, .nonrecursive name s value rest => do
      let code ← term value
      let tail ← declarations rest
      return Lean.Json.mkObj [("name", .str name.origin), ("scheme", .str (reprStr s)),
        ("scope", .str s!"(Scope.mk {w.numbers} {w.types} ({reprStr w.constraints}))"),
        ("context_schemes", .str (reprStr (Γ.map Prod.snd))),
        ("context", Lean.toJson (Γ.map fun entry => entry.1.origin)),
        ("recursive_group", Lean.toJson ([] : List String)), ("term", .str code)] :: tail
  | Γ, _, .recursive bindings values rest => do
      let group ← (List.finRange (bindings.map Prod.snd).length).mapM fun i => do
        let code ← term (values i)
        return Lean.Json.mkObj [("name", .str bindings[i].1.origin),
          ("scheme", .str (reprStr (bindings.map Prod.snd)[i])),
          ("scope", .str s!"(Scope.mk {w.numbers} {w.types} ({reprStr w.constraints}))"),
          ("context_schemes", .str (reprStr ((bindings ++ Γ).map Prod.snd))),
          ("context", Lean.toJson ((bindings ++ Γ).map fun entry => entry.1.origin)),
          ("recursive_group", Lean.toJson (bindings.map fun entry => entry.1.origin)),
          ("term", .str code)]
      return group ++ (← declarations rest)

end Cryptol.Translation.Materialize
