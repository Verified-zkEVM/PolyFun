/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import PolyFun.IPFunctor.Scoped.Import.Driver
public meta import Lean.Data.Json.Printer
public meta import Lean.Elab.Exception

/-!
# The registry of imports

An import under a prefix `P` records what it read as the bundle declaration
`P.manifest : Import.Manifest`: the format and version of its input, provenance pairs such as the
revision of the tool that wrote the input, and a fingerprint of the input. It records each setting
of the frontend that shapes its declarations, such as whether they get native values, as a bundle
declaration `P.settings.k : String`. The manifest and the settings make the prefix a registry.
Before an import under `P` adds anything, `Registry.plan` decides how it proceeds:

* if `P.manifest` exists with another value, `P` names the import of another input, and the import
  is refused;
* if `P.manifest` records the same input but a setting differs from this import's, the import is
  refused, with a message naming the setting;
* a declaration of the import that would take the name of one of the prefix's bundle declarations
  is refused;
* a declaration whose name exists is skipped if `P.manifest` records the same input and the
  existing declaration is this import's, as a witness constant with the expected value shows, such
  as the declaration's `source`. Otherwise the import is refused.

So importing the same input again under `P` adds nothing, and an import that reaches more
declarations of the same input adds only those. `Registry.bundle` gives the manifest, the settings
and the frontend's other bundle declarations for a new prefix. When the plan reuses the prefix, it
gives the frontend's bundle declarations whose names do not exist yet, such as a table entry that
only a later import reaches.

`Select` chooses declarations by name, such as those that get equation lemmas: all, none (`off`),
only those named, or all except those named. `Select.validate` refuses a name in `only` or `except`
that the import does not have. In an import command, `importSelect` writes `off`, `only ["n", …]`
or `except ["n", …]`.
-/

public section

namespace IPFunctor.Import

/-- What an import read: the format of its input and the format's version, provenance pairs such
as the revision of the tool that wrote the input, and a fingerprint of the input. -/
structure Manifest where
  /-- The input's format. -/
  format : String
  /-- The format's version. -/
  version : Nat
  /-- Provenance fields and their values, in the order the importer reads them. -/
  provenance : List (String × String)
  /-- A fingerprint of the input, which tells two inputs apart. -/
  fingerprint : Nat

end IPFunctor.Import

end

public meta section

namespace IPFunctor.Import

open Lean Meta

deriving instance ToExpr for Manifest

/-- A 64-bit hash of the compressed JSON `j`, as a manifest's fingerprint. It tells two inputs
apart; it is not a cryptographic digest. -/
def Manifest.fingerprintOf (j : Json) : Nat :=
  (hash j.compress).toNat

/-- An import under the prefix `pfx`, relative to the current namespace: what it read, the
frontend's settings that shape its declarations, and which names, besides `pfx.manifest` and
`pfx.settings.k`, its bundle declarations take. -/
structure Registry where
  /-- The prefix, relative to the current namespace. -/
  pfx : Name
  /-- What the import read. -/
  manifest : Manifest
  /-- The frontend's settings that shape the declarations, as pairs of setting and value. -/
  settings : List (String × String) := []
  /-- Whether a name relative to the current namespace is taken by one of the frontend's bundle
  declarations. -/
  reserved : Name → Bool := fun _ => false

namespace Registry

/-- How an import under a prefix proceeds. -/
structure Plan (α : Type) where
  /-- Whether the prefix records an import of the same input with the same settings. -/
  reuse : Bool
  /-- The declarations to import, in order: those whose names do not exist yet. -/
  todo : Array α

/-- Whether the constant `name` exists with the value `value`. -/
def hasValue (name : Name) (value : Expr) : CoreM Bool := do
  match (← getEnv).find? name with
  | some info => return info.value? == some value
  | none => return false

variable (r : Registry)

/-- The name of the manifest, relative to the current namespace. -/
def manifestName : Name :=
  r.pfx ++ `manifest

/-- The name of the setting `key`, relative to the current namespace. -/
def settingName (key : String) : Name :=
  .str (r.pfx ++ `settings) key

/-- Whether the name `b`, relative to the current namespace, is one that a bundle declaration of
the prefix takes. -/
def isBundleName (b : Name) : Bool :=
  b == r.manifestName || (r.pfx ++ `settings).isPrefixOf b || r.reserved b

/-- Refuse a setting that differs from the one recorded under the prefix. -/
def checkSettings : CoreM Unit := do
  let ns ← getCurrNamespace
  for (key, value) in r.settings do
    let recorded := match (← getEnv).find? (ns ++ r.settingName key) with
      | some info => match info.value? with
        | some (.lit (.strVal v)) => some v
        | _ => none
      | none => none
    unless recorded == some value do
      let was := match recorded with
        | some v => m!"with {key} = {v}"
        | none => m!"without the setting {key}"
      throwError "`{r.pfx}` was imported {was}, where this import has {key} = {value}; an import \
        under the same prefix keeps its settings"

/-- Plan an import of `items` under the prefix. `base item` is an item's name and `witness item` a
constant with the value it has when the existing declaration is this import's, both relative to
the current namespace. The plan refuses another input under the prefix, a changed setting, a name
that a bundle declaration takes, and an existing name that is not this import's declaration. -/
def plan {α : Type} (items : Array α) (base : α → Name) (witness : α → Name × Expr) :
    CoreM (Plan α) := do
  let ns ← getCurrNamespace
  let manifest := ns ++ r.manifestName
  let reuse ← hasValue manifest (toExpr r.manifest)
  if !reuse && (← getEnv).contains manifest then
    throwError "`{r.pfx}` already names an import of another input"
  if reuse then r.checkSettings
  for item in items do
    let b := base item
    if r.isBundleName b then
      throwError "`{b}` is the name of a bundle declaration of `{r.pfx}`, so no imported \
        declaration can take it"
  let mut todo := #[]
  for item in items do
    let name := ns ++ base item
    if (← getEnv).contains name then
      let (w, value) := witness item
      unless reuse && (← hasValue (ns ++ w) value) do
        throwError "`{name}` exists, and is not this import's declaration"
    else
      todo := todo.push item
  return { reuse, todo }

/-- The bundle declarations of an import following `plan`. For a new prefix: the manifest, the
settings, and the frontend's `decls`. When the plan reuses the prefix: those of `decls` whose
names do not exist yet. -/
def bundle {α : Type} (plan : Plan α) (decls : Array BundleDecl) : CoreM (Array BundleDecl) := do
  let ns ← getCurrNamespace
  if plan.reuse then
    let env ← getEnv
    return decls.filter fun d => !env.contains (ns ++ d.base)
  let manifest := BundleDecl.defn r.manifestName (mkConst ``Manifest) (toExpr r.manifest)
    "What this import read."
  let settings := r.settings.toArray.map fun (key, value) =>
    BundleDecl.defn (r.settingName key) (mkConst ``String) (toExpr value)
      s!"The setting `{key}` of the imports under this prefix."
  return #[manifest] ++ settings ++ decls

end Registry

/-- A choice of an import's declarations by name. -/
inductive Select where
  /-- Every declaration. -/
  | all
  /-- No declaration. -/
  | off
  /-- Only the declarations named. -/
  | only (names : Array String)
  /-- Every declaration except those named. -/
  | except (names : Array String)

/-- Whether the declaration named `name` is chosen. -/
def Select.includes : Select → String → Bool
  | .all, _ => true
  | .off, _ => false
  | .only names, name => names.contains name
  | .except names, name => !names.contains name

/-- `all`, `off`, `only [n, …]` or `except [n, …]`, as an import's settings record it. -/
instance : ToString Select where
  toString
    | .all => "all"
    | .off => "off"
    | .only names => s!"only {names.toList}"
    | .except names => s!"except {names.toList}"

/-- Refuse a name in `only` or `except` that is not among `names`, the names that the import has.
`option` is the command's option that the selection qualifies, or empty, and `missing` completes
the message about such a name, as in "`except` names `n`, which is not a declaration of this
import". -/
def Select.validate (s : Select) (option : String) (names : Array String)
    (missing : String := "is not a declaration of this import") : CoreM Unit := do
  let (keyword, xs) := match s with
    | .only xs => ("only", xs)
    | .except xs => ("except", xs)
    | _ => ("", #[])
  let phrase := if option.isEmpty then keyword else s!"{option} {keyword}"
  for x in xs do
    unless names.contains x do
      throwError "`{phrase}` names `{x}`, which {missing}"

/-- `only ["n", …]` in an import command. -/
syntax importSelectOnly := &" only" " [" str,* "]"

/-- `except ["n", …]` in an import command. -/
syntax importSelectExcept := &" except" " [" str,* "]"

/-- `off`, `only ["n", …]` or `except ["n", …]`: a `Select` in an import command, after the
option it qualifies. -/
syntax importSelect := &" off" <|> importSelectOnly <|> importSelectExcept

/-- The selection that `importSelect` writes. -/
def Select.ofSyntax {m : Type → Type} [Monad m] [MonadExceptOf Exception m] :
    TSyntax ``importSelect → m Select
  | `(importSelect| off) => pure .off
  | `(importSelect| $x:importSelectOnly) => match x with
    | `(importSelectOnly| only [$xs,*]) => pure (.only (xs.getElems.map (·.getString)))
    | _ => Elab.throwUnsupportedSyntax
  | `(importSelect| $x:importSelectExcept) => match x with
    | `(importSelectExcept| except [$xs,*]) => pure (.except (xs.getElems.map (·.getString)))
    | _ => Elab.throwUnsupportedSyntax
  | _ => Elab.throwUnsupportedSyntax

end IPFunctor.Import
