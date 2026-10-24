/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceLink
public import PolyFunCryptol.Translation.Declarations

/-!
# Shared typed module environments

Each retained declaration has one finite polymorphic body. Global references
are positions in an ordered typed environment. Only members of a source
recursive group share a fixed point. Primitive implementations and module
parameters remain explicit inputs. Acceptance and source preservation are
separate claims.
-/

public section

namespace Cryptol.Translation

open Polymorphic

/-- A module and its shared, intrinsically typed declaration bodies. -/
structure ElaboratedModule where
  /-- Exact retained source module, including its provenance and exports. -/
  source : ModuleDefinition
  /-- Module numeric/type parameters and their assumptions. -/
  scope : Scope
  /-- Explicit primitive implementations followed by module value parameters. -/
  parameters : List (Reference.Name × scope.ValueSort)
  /-- Final named environment, with ambient inputs after the new declarations. -/
  bindings : Signatures scope
  /-- Each body is checked under its source declaration group's environment. -/
  code : Declarations scope parameters bindings
  /-- Original primitive declarations whose meanings are explicit inputs. -/
  requirements : List PrimitiveRequirement := []

namespace ElaboratedModule

/-- Interpret ordered groups before choosing any instantiation of their schemes. -/
@[expose] noncomputable def denote (m : ElaboratedModule) (ρ : m.scope.Assignment) :
    Env ρ (m.parameters.map Prod.snd) →𝒄 Env ρ (m.bindings.map Prod.snd) :=
  m.code.denote ρ

/-- Declaration identities in the final environment, excluding ambient inputs. -/
@[expose] def declarations (m : ElaboratedModule) : Signatures m.scope :=
  m.code.introduced

/-- The final module context consists of declarations followed by its explicit inputs. -/
theorem bindings_eq (m : ElaboratedModule) : m.bindings = m.declarations ++ m.parameters :=
  m.code.bindings_eq

/-- A closed consumer observes the same environment as module interpretation. -/
theorem denote_close (m : ElaboratedModule) (ρ : m.scope.Assignment)
    {s : m.scope.ValueSort} (body : Term m.scope (m.bindings.map Prod.snd) s)
    (η : Env ρ (m.parameters.map Prod.snd)) :
    (m.code.close body).denote ρ η = body.denote ρ (m.denote ρ η) :=
  m.code.denote_close ρ body η

/-- Select a public source name and retain the shared declarations around its reference. -/
@[expose] def exportTerm (m : ElaboratedModule) (name : String) :
    Except String (OpenElaboration.TypedTerm m.scope (m.parameters.map Prod.snd)) := do
  let exported := m.source.exports.filter (fun n => n.text == name)
  let [identity] := exported | throw "unknown or ambiguous public declaration"
  let globals := OpenElaboration.Names.ofSignatures (w := m.scope) m.bindings
  let ⟨s, body⟩ ← OpenElaboration.lookup globals identity
  return ⟨s, m.code.close body⟩

end ElaboratedModule

namespace ModuleBundle

/-- Module binders retain their source identities while extending the canonical parameter scope. -/
@[expose] def parameters : (w : Scope) → OpenTypes.Parameters w.numbers w.types →
    List (Reference.Name × Reference.Parameter) →
    Except String ((z : Scope) × OpenTypes.Parameters z.numbers z.types)
  | w, env, [] => .ok ⟨w, env⟩
  | w, env, (_, p) :: rest => match p.kind with
      | .number => parameters w.bindNum (env.bindNum p.id) rest
      | .value => parameters w.bindType (env.bindType p.id) rest
      | _ => .error "unsupported module parameter kind"

/-- Elaborate a complete module into one typed shared environment. -/
@[expose] def elaborate (bundle : ModuleBundle) (rootName : String)
    (fuel : Nat := 10000) : Except ImportError ElaboratedModule := do
  let linked ← match bundle.link rootName fuel with
  | .error e => throw e
  | .ok source => pure (ULift.up source)
  let root := linked.down.source
  let result : Except String ElaboratedModule := do
    let ⟨⟨w, env⟩⟩ ← OpenElaboration.liftCheck
      (parameters Scope.empty ⟨[], []⟩ root.typeParameters)
    let ⟨cs⟩ ← OpenElaboration.liftCheck (root.constraints.mapM (OpenTypes.constraint env fuel))
    let scope : Scope := ⟨w.numbers, w.types, cs ++ w.constraints⟩
    let ⟨ambient⟩ ← OpenElaboration.liftCheck
      (root.valueParameters.mapM fun (name, schema) => do
        return (name, ← OpenTypes.scheme env fuel schema))
    let ⟨primitiveInputs⟩ ← OpenElaboration.liftCheck
      (OpenElaboration.signatures (w := scope) env fuel
        (linked.down.requirements.map PrimitiveRequirement.declaration))
    let ambient := primitiveInputs ++ ambient
    let ⟨bindings, code⟩ ← OpenElaboration.declarations fuel (w := scope) env ambient
      linked.down.groups
    return ⟨root, scope, ambient, bindings, code, linked.down.requirements⟩
  result.mapError (⟨[root.provenance.name, "elaboration"], ·⟩)

/-- Every independent blocker of a module's typed elaboration. -/
structure Diagnosis where
  /-- Each explicit primitive input, with the failure of its declared scheme if any. -/
  primitives : List (String × Option String)
  /-- Each linked declaration group, checked under the schemes of the groups before it. -/
  groups : List OpenElaboration.GroupDiagnosis

/-- Diagnose a complete module, continuing past failing primitive schemes and bodies.
Failures of the module's own parameters or constraints remain whole-module errors. -/
def diagnose (bundle : ModuleBundle) (rootName : String) (fuel : Nat := 10000) :
    Except ImportError Diagnosis := do
  let linked ← match bundle.link rootName fuel with
  | .error e => throw e
  | .ok source => pure (ULift.up source)
  let root := linked.down.source
  let result : Except String Diagnosis := do
    let ⟨w, env⟩ ← parameters Scope.empty ⟨[], []⟩ root.typeParameters
    let cs ← root.constraints.mapM (OpenTypes.constraint env fuel)
    let scope : Scope := ⟨w.numbers, w.types, cs ++ w.constraints⟩
    let ambient ← root.valueParameters.mapM fun (name, schema) => do
      return (name, ← OpenTypes.scheme env fuel schema)
    let primitives := linked.down.requirements.map fun r =>
      (r.declaration.name.origin,
        OpenElaboration.signatures (w := scope) env fuel [r.declaration])
    let inputs := primitives.flatMap fun (_, result) => match result with
      | .ok sigs => sigs
      | .error _ => []
    return ⟨primitives.map fun (name, result) => (name, match result with
        | .ok _ => none
        | .error e => some e),
      OpenElaboration.diagnose fuel (w := scope) env (inputs ++ ambient) linked.down.groups⟩
  result.mapError (⟨[root.provenance.name, "elaboration"], ·⟩)

/-- An exact accepted module elaboration, independent of source-preservation claims. -/
structure ElaborationCertificate (bundle : ModuleBundle) (source : String) where
  /-- Explicit checking budget. -/
  budget : Nat
  /-- Typed module with real bodies. -/
  result : ElaboratedModule
  /-- Kernel-checked acceptance equation. -/
  accepted : bundle.elaborate source budget = .ok result

/-- Successful elaboration retains its exact acceptance equation. -/
@[expose] def certifyElaboration (bundle : ModuleBundle) (source : String)
    (fuel : Nat := 10000) : Except ImportError (bundle.ElaborationCertificate source) :=
  match h : bundle.elaborate source fuel with
  | .ok result => .ok ⟨fuel, result, h⟩
  | .error error => .error error

end ModuleBundle
end Cryptol.Translation
