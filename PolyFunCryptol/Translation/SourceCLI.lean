/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunCryptol.Translation.Materialize
import PolyFunCryptol.Translation.SourceLink
import PolyFunCryptol.Translation.ModuleElaboration
import PolyFunCryptol.Translation.SourceScope
import PolyFunCryptol.Translation.SourceElaboration
import PolyFunCryptol.Translation.Export
import PolyFunCryptol.Model.Reference.Types

/-! # Source-bundle validation and inspection -/

namespace Cryptol.Translation.SourceCLI

def errorJson (error : ImportError) : Lean.Json :=
  .mkObj [("status", .str "rejected"), ("location", Lean.toJson error.location),
    ("message", .str error.message)]

/-- Decode and validate a versioned source bundle, reporting the exact checking stage. -/
public def run (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match args with
  | ["modules", file] =>
      let text ← IO.FS.readFile file
      let input : Except ImportError ModuleBundle := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        SourceBundle.decodeModuleBundle json
      match input with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok bundle =>
          let reports := bundle.scopeReport.map fun (name, result) => Lean.Json.mkObj
            [("module", .str name), ("body_retention", .str "decoded"),
             ("scope", match result with
               | .ok () => .mkObj [("status", .str "accepted")]
               | .error error => errorJson error),
             ("semantic_import", .str "not-attempted")]
          out.putStrLn (Lean.toJson reports).compress
          return if bundle.scopeReport.all (fun r => r.2 matches .ok _) then 0 else 1
  | [mode, file, moduleName] =>
      unless mode == "module-elaborate" || mode == "module-code" || mode == "module-link" ||
          mode == "module-diagnose" do
        err.putStrLn "Unknown module command"
        return 1
      let text ← IO.FS.readFile file
      let input : Except ImportError ModuleBundle := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        SourceBundle.decodeModuleBundle json
      match input with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok bundle =>
          if mode == "module-diagnose" then
            match bundle.diagnose moduleName with
            | .error error => out.putStrLn (errorJson error).compress; return 1
            | .ok diagnosis =>
                let failure : Option String → Lean.Json
                  | none => .null
                  | some message => .str message
                out.putStrLn (Lean.Json.mkObj [("module", .str moduleName),
                  ("status", .str "diagnosed"),
                  ("primitives", .arr (diagnosis.primitives.toArray.map fun (name, result) =>
                    .mkObj [("name", .str name), ("failure", failure result)])),
                  ("groups", .arr (diagnosis.groups.toArray.map fun group =>
                    .mkObj [("declarations", Lean.toJson group.names),
                      ("failure", failure group.failure)]))]).compress
                return 0
          if mode == "module-link" then
            match bundle.link moduleName with
            | .error error => out.putStrLn (errorJson error).compress; return 1
            | .ok linked =>
                out.putStrLn (Lean.Json.mkObj [("module", .str moduleName),
                  ("link", .str "accepted"), ("semantic_import", .str "not-attempted"),
                  ("groups", Lean.toJson (linked.groups.map fun group => Lean.Json.mkObj
                    [("recursive", Lean.toJson (group matches .recursive _)),
                     ("declarations", Lean.toJson
                       (group.declarations.map fun d => d.name.origin))])),
                  ("primitive_requirements", Lean.toJson (linked.requirements.map fun r =>
                    Lean.Json.mkObj [("name", .str r.declaration.name.origin),
                      ("id", Lean.toJson r.declaration.name.id),
                      ("schema", .str (reprStr r.declaration.schema))]))]).compress
                return 0
          let some source := bundle.modules.find? (fun m => m.provenance.name == moduleName)
            | out.putStrLn (errorJson ⟨[moduleName], "unknown module"⟩).compress; return 1
          match bundle.elaborate moduleName with
          | .error error => out.putStrLn (errorJson error).compress; return 1
          | .ok result =>
              let mut exports := #[]
              for name in source.exports do
                match result.exportTerm name.text with
                | .error message =>
                    out.putStrLn (errorJson ⟨[moduleName, name.text], message⟩).compress
                    return 1
                | .ok ⟨scheme, _⟩ =>
                    exports := exports.push (.mkObj [("name", .str name.text),
                      ("scheme", .str (reprStr scheme))])
              let mut bodies := #[]
              if mode == "module-code" then
                match Materialize.declarations result.code with
                | .error message =>
                    out.putStrLn (errorJson ⟨[moduleName, "materialization"], message⟩).compress
                    return 1
                | .ok code => bodies := code.toArray
              out.putStrLn (Lean.Json.mkObj [("module", .str moduleName),
                ("expression_typing", .str "accepted"),
                ("semantic_import", .str (if result.declarations.isEmpty then "no-value-definitions"
                  else if !result.requirements.isEmpty then "conditional-model"
                  else if !source.typeParameters.isEmpty || !source.valueParameters.isEmpty then
                    "parameterized-model" else "model")),
                ("module_value_parameters", Lean.toJson source.valueParameters.length),
                ("module_type_parameters", Lean.toJson source.typeParameters.length),
                ("primitive_requirements", Lean.toJson (result.requirements.map fun r =>
                  Lean.Json.mkObj [("name", .str r.declaration.name.origin),
                    ("schema", .str (reprStr r.declaration.schema))])),
                ("source_correspondence", .str "not-established"),
                ("shared_declarations", Lean.toJson result.declarations.length),
                ("exports", .arr exports), ("bodies", .arr bodies)]).compress
              return 0
  | ["elaborate", file] =>
      let text ← IO.FS.readFile file
      let input : Except ImportError SourceBundle := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        SourceBundle.decode json
      match input with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok bundle =>
          let reports : List (Except ImportError (ULift.{1} Lean.Json)) :=
            bundle.roots.map fun root => do
            let certificate ← SourceElaboration.certify bundle root
            let ⟨expected, term⟩ := certificate.result
            pure ⟨Lean.Json.mkObj [("root", .str root.text), ("status", .str "typed"),
              ("type", .str (reprStr expected)),
              ("source", .str (Export.expression term))]⟩
          let mut results := #[]
          for result in reports do
            match result with
            | .error error => out.putStrLn (errorJson error).compress; return 1
            | .ok ⟨result⟩ => results := results.push result
          out.putStrLn (Lean.Json.arr results).compress
          return 0
  | ["constraints", file] =>
      let text ← IO.FS.readFile file
      let result : Except ImportError Lean.Json := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        let cases ← json.getArr?.mapError (⟨["cases"], ·⟩)
        let checked ← cases.mapM fun entry => do
          let input ← (entry.getObjVal? "constraint").mapError (⟨["constraint"], ·⟩)
          let expression ← SourceBundle.decodeType input
          let result ← (do
            expression.checkKind 10000 [] .proposition
            expression.evaluate 10000 [] >>= Reference.TypeValue.proposition?).mapError
              (⟨["constraint"], ·⟩)
          pure (Lean.Json.mkObj [("constraint", input), ("result", Lean.toJson result)])
        return .arr checked
      match result with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok result => out.putStrLn result.compress; return 0
  | ["inspect", file] =>
      let text ← IO.FS.readFile file
      let result : Except ImportError SourceBundle := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        let bundle ← SourceBundle.decode json
        let _ ← bundle.certifyScopes
        pure bundle
      match result with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok bundle =>
          out.putStrLn (Lean.Json.mkObj [("status", .str "scoped"),
            ("roots", Lean.toJson (bundle.roots.map SourceRoot.text)),
            ("groups", Lean.toJson bundle.groups.length),
            ("declarations", Lean.toJson
              (bundle.groups.flatMap Reference.DeclGroup.declarations).length),
            ("modules", Lean.toJson bundle.modules.length)]).compress
          return 0
  | _ =>
      err.putStrLn "Usage: cryptol-interop source \
        {inspect | elaborate | constraints | modules} FILE.json; \
        {module-link | module-elaborate | module-code | module-diagnose} FILE.json MODULE"
      return 1

end Cryptol.Translation.SourceCLI
