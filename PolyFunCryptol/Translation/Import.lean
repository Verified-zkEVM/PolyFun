/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceElaboration
public import Mathlib.Data.Fin.VecNotation
public meta import PolyFunCryptol.Translation.SourceElaboration
public meta import Lean

/-!
# Importing exported Cryptol source

`cryptol_import Imported from "path/to/export.json"` reads a source bundle exported by the
pinned frontend, checks every root with `SourceElaboration.check` at elaboration time,
and declares, in the current namespace:
* `Imported.bundle : SourceBundle`, the decoded bundle;
* for each root `r`, `Imported.r : Resolved.Term [] T`, the checked resolved term;
* `Imported.r.root : SourceRoot`, the root as exported;
* `Imported.r.accepted : check Imported.bundle Imported.r.root = .ok ⟨T, Imported.r⟩`.

The JSON file and this command are untrusted. The kernel re-runs the checker on the
declared bundle to prove `Imported.r.accepted`. A root is named after its source text when
that text is an identifier, and `root<i>` otherwise. The path is relative to the
package root, and Lake does not track it, so regenerate the export through the
reference pipeline, whose manifest records its digest.
-/

public meta section

namespace Cryptol.Translation.Import

open Lean Elab Command Meta

/-- Closed Cryptol types have no type variables, so their variable type is `Empty`. -/
instance toExprEmpty : ToExpr Empty where
  toExpr e := e.elim
  toTypeExpr := mkConst ``Empty

deriving instance ToExpr for Length
deriving instance ToExpr for Ty
deriving instance ToExpr for EvalError
deriving instance ToExpr for BitOp
deriving instance ToExpr for ShiftOp
deriving instance ToExpr for IntOp
deriving instance ToExpr for RingOp
deriving instance ToExpr for CompareOp
deriving instance ToExpr for LogicType
deriving instance ToExpr for RingType
deriving instance ToExpr for Primitive
deriving instance ToExpr for Reference.Kind
deriving instance ToExpr for Reference.Name
deriving instance ToExpr for Reference.Parameter
deriving instance ToExpr for Reference.Selector
deriving instance ToExpr for Reference.TypeExpr
deriving instance ToExpr for Reference.Schema
deriving instance ToExpr for Reference.Expr, Reference.CaseAlt, Reference.Match,
  Reference.Definition, Reference.Decl, Reference.DeclGroup
deriving instance ToExpr for SourceRoot
deriving instance ToExpr for SourceModule
deriving instance ToExpr for SourceBundle

/-- The closed Cryptol type former. -/
def closedTy : Lean.Expr := toTypeExpr ClosedTy

/-- Quote a typed variable with its context and sort. -/
def quoteVar : {Γ : List ClosedTy} → {a : ClosedTy} → IPFunctor.ScopedVar Γ a → Lean.Expr
  | _ :: Γ, a, .zero =>
      mkAppN (mkConst ``IPFunctor.ScopedVar.zero [Level.zero]) #[closedTy, toExpr Γ, toExpr a]
  | b :: Γ, a, .succ v =>
      mkAppN (mkConst ``IPFunctor.ScopedVar.succ [Level.zero])
        #[closedTy, toExpr Γ, toExpr a, toExpr b, quoteVar v]

/-- The smart constructor of an operator and its arguments other than context and children. -/
def head : {a : ClosedTy} → Resolved.Op a → Name × Array Lean.Expr
  | _, @Resolved.Op.sequence a n => (``Resolved.Term.sequence, #[toExpr a, toExpr n])
  | _, @Resolved.Op.primitive a p => (``Resolved.Term.primitive, #[toExpr a, toExpr p])
  | _, .bit b => (``Resolved.Term.bit, #[toExpr b])
  | _, .integer i => (``Resolved.Term.integer, #[toExpr i])
  | _, .unit => (``Resolved.Term.unit, #[])
  | _, @Resolved.Op.error a e => (``Resolved.Term.error, #[toExpr a, toExpr e])
  | _, @Resolved.Op.lam a b => (``Resolved.Term.lam, #[toExpr a, toExpr b])
  | _, @Resolved.Op.app a b => (``Resolved.Term.app, #[toExpr a, toExpr b])
  | _, @Resolved.Op.letE a b => (``Resolved.Term.letE, #[toExpr a, toExpr b])
  | _, @Resolved.Op.pair a b => (``Resolved.Term.pair, #[toExpr a, toExpr b])
  | _, @Resolved.Op.fst a b => (``Resolved.Term.fst, #[toExpr a, toExpr b])
  | _, @Resolved.Op.snd a b => (``Resolved.Term.snd, #[toExpr a, toExpr b])
  | _, @Resolved.Op.generate a l => (``Resolved.Term.generate, #[toExpr a, toExpr l])
  | _, @Resolved.Op.index a l => (``Resolved.Term.index, #[toExpr a, toExpr l])
  | _, @Resolved.Op.ite a => (``Resolved.Term.ite, #[toExpr a])
  | _, @Resolved.Op.fix a => (``Resolved.Term.fix, #[toExpr a])
  | _, .bitNot => (``Resolved.Term.bitNot, #[])
  | _, .bitOp o => (``Resolved.Term.bitOp, #[toExpr o])
  | _, .intOp o => (``Resolved.Term.intOp, #[toExpr o])
  | _, .intEq => (``Resolved.Term.intEq, #[])
  | _, .intLt => (``Resolved.Term.intLt, #[])

/-- Sequence literals take their children as one vector argument. -/
def isSequence : {a : ClosedTy} → Resolved.Op a → Bool
  | _, .sequence _ => true
  | _, _ => false

mutual

/-- Quote a resolved term as applications of the `Resolved.Term` smart constructors. -/
partial def quoteTerm : {Γ : List ClosedTy} → {a : ClosedTy} → Resolved.Term Γ a → MetaM Lean.Expr
  | Γ, a, .pure v => return mkAppN (mkConst ``Resolved.Term.var) #[toExpr Γ, toExpr a, quoteVar v]
  | _, _, .liftBind op k => quoteNode op k

/-- Quote one constructor application from its children. -/
partial def quoteNode {Γ : List ClosedTy} {a : ClosedTy} (op : Resolved.Op a)
    (k : (p : Resolved.syntaxSignature.Arg op) →
      Resolved.Term (Resolved.syntaxSignature.binders op p ++ Γ)
        (Resolved.syntaxSignature.sort op p)) : MetaM Lean.Expr := do
  let (name, params) := head op
  let children ← (List.finRange op.arity).mapM fun i => quoteTerm (k i)
  let prefix_ := #[toExpr Γ] ++ params
  if isSequence op then
    let element := mkAppN (mkConst ``Resolved.Term) #[toExpr Γ, params[0]!]
    let mut items ← mkAppOptM ``Matrix.vecEmpty #[some element]
    for child in children.reverse do
      items ← mkAppM ``Matrix.vecCons #[child, items]
    return mkAppN (mkConst name) (prefix_.push items)
  else
    return mkAppN (mkConst name) (prefix_ ++ children.toArray)

end

/-- Add a definition whose body is exported, as `@[expose]` does. -/
def addExposedDefinition (name : Name) (type value : Lean.Expr) (doc : String) : CoreM Unit := do
  withExporting do
    addDecl <| .defnDecl {
      name, levelParams := [], type, value, safety := .safe
      hints := .regular (getMaxHeight (← getEnv) value + 1) }
    enableRealizationsForConst name
  addDocStringCore name doc

/-- The declaration name for a root: its source text when that is an identifier. -/
def rootName (index : Nat) (root : SourceRoot) : Name :=
  let name := root.text.toName
  if !name.isAnonymous && name.isAtomic && root.text.all (fun c => c.isAlphanum || c == '_') then
    name
  else
    .mkSimple s!"root{index}"

/-- Decode, check, and declare an exported source bundle. -/
def importBundle (prefix_ : Name) (path : String) : CommandElabM Unit := do
  let text ← IO.FS.readFile path
  let json ← match Json.parse text with
    | .ok json => pure json
    | .error e => throwError "{path}: invalid JSON: {e}"
  let bundle ← match SourceBundle.decode json with
    | .ok bundle => pure bundle
    | .error e => throwError "{path}: {String.intercalate " / " e.location}: {e.message}"
  let ns ← getCurrNamespace
  let bundleName := ns ++ prefix_ ++ `bundle
  liftCoreM <| addExposedDefinition bundleName (mkConst ``SourceBundle) (toExpr bundle)
    s!"The source bundle exported to `{path}`."
  for h : index in [0:bundle.roots.length] do
    let root := bundle.roots[index]
    let base := ns ++ prefix_ ++ rootName index root
    let rootDecl := base ++ `root
    liftCoreM <| addExposedDefinition rootDecl (mkConst ``SourceRoot) (toExpr root)
      s!"The exported root `{root.text}`."
    match SourceElaboration.check bundle root with
    | .error e =>
        throwError "{path}, root `{root.text}`: {String.intercalate " / " e.location}: \
          {e.message}"
    | .ok ⟨type, result⟩ =>
        let value ← liftTermElabM <| quoteTerm result
        let termType := mkAppN (mkConst ``Resolved.Term)
          #[toExpr ([] : List ClosedTy), toExpr type]
        liftCoreM <| addExposedDefinition base termType value
          s!"The checked resolved term of root `{root.text}`."
    let accepted := mkIdent (`_root_ ++ base ++ `accepted)
    elabCommand (← `(command|
      set_option maxRecDepth 10000 in
      /-- The kernel re-runs the checker on the declared bundle and root. -/
      theorem $accepted : Cryptol.Translation.SourceElaboration.check
          $(mkIdent bundleName) $(mkIdent rootDecl) = .ok ⟨_, $(mkIdent base)⟩ := by
        with_unfolding_all rfl))

/-- `cryptol_import Imported from "export.json"` declares a checked exported Cryptol bundle. -/
syntax (name := cryptolImport) "cryptol_import " ident " from " str : command

/-- Elaborate `cryptol_import` by `importBundle`. -/
@[command_elab cryptolImport] def elabCryptolImport : CommandElab
  | `(cryptol_import $prefix_:ident from $path:str) => importBundle prefix_.getId path.getString
  | _ => throwUnsupportedSyntax

end Cryptol.Translation.Import
