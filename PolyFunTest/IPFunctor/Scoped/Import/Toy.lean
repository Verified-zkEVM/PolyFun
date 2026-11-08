/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedVectors
public meta import PolyFun.IPFunctor.Scoped.Import.Driver
public meta import Lean.Elab.Command

/-!
# A toy JSON frontend for size-indexed vectors

A frontend of the import machinery for the language of the `ScopedVectors` tutorial. Its source
is a small typed AST in JSON: variables as de Bruijn positions, numbers, abstractions with their
argument types, applications, size abstractions and size instantiations. Each declaration lists
the earlier declarations it uses; they form its value context, nearest first.

* The kernel side is the mirror `Src` of the source and `erase : Tm Θ Γ s → Src.Expr`, an exposed
  fold. Erasure keeps every abstraction's argument type and every instantiation's size, and drops
  the coercions the elaborator inserts.
* The meta side decodes JSON into the mirror and elaborates each declaration. It infers the
  annotations every head needs from the mirror's types and inserts a coercion after each
  instantiation, from the type substitution computes to the written type. It checks scopes, and
  leaves typing to the kernel. Its JSON decoders and its elaborator are `partial`, with no
  termination proof: the decoded mirror is the source that acceptance states, and the kernel
  checks every term the elaborator builds.

`toy_import "path.json"` adds each declaration `d`, its acceptance theorem `d.accepted`, and for a
closed monomorphic declaration the equation lemma `d.evaluate_eq`, whose right side is the native
meaning written without syntax. Options: `budget n` sets the per-declaration kernel budget,
`check` only reports the kernel's verdicts, and `decide` proves acceptance by evaluating
decidable equality instead of by `Eq.refl`.

A declaration marked `"uncompiled": true` is written through `uncompiled`, a `noncomputable`
identity on terms. The kernel accepts it, and the code generator cannot compile it, so it tests
that a compilation error leaves nothing of the declaration behind.
-/

public section

namespace PolyFunTest.ToyImport

open IPFunctor IPFunctor.ScopedSignature Examples.ScopedVectors

end PolyFunTest.ToyImport

/-! ## The source mirror

Its derived decidable equality is exposed, so that the kernel can evaluate it in the importing
module when acceptance is proved by `decide`. -/

@[expose] public section

namespace PolyFunTest.ToyImport.Src

/-- Sizes of the source: literals, sums and size variables at de Bruijn positions. -/
inductive Size where
  | lit (n : ℕ)
  | add (m n : Size)
  | var (i : ℕ)
  deriving DecidableEq

/-- Types of the source. -/
inductive Ty where
  | nat
  | vec (n : Size) (a : Ty)
  | arrow (a b : Ty)
  deriving DecidableEq

/-- Schemes of the source: a type under size quantifiers. -/
inductive Scheme where
  | mono (t : Ty)
  | all (s : Scheme)
  deriving DecidableEq

/-- Expressions of the source. `rep` stands for the tutorial's primitive, which this frontend
does not import. -/
inductive Expr where
  | var (i : ℕ)
  | lit (k : ℕ)
  | rep
  | lam (a : Ty) (body : Expr)
  | app (f x : Expr)
  | sabs (e : Expr)
  | sapp (e : Expr) (n : Size)
  deriving DecidableEq

end PolyFunTest.ToyImport.Src

end

namespace PolyFunTest.ToyImport

open IPFunctor IPFunctor.ScopedSignature Examples.ScopedVectors

/-! ## Erasure -/

/-- What a type-level term of each kind erases to. -/
@[expose, reducible] def QuoteD : Kind → Type
  | .size => Src.Size
  | .type => Src.Ty
  | .scheme => Src.Scheme

/-- A type-level variable; the source has size variables only, so the others are junk. -/
@[expose] def quoteVar : (k : Kind) → ℕ → QuoteD k
  | .size, i => .var i
  | .type, _ => .nat
  | .scheme, _ => .mono .nat

/-- One type-level constructor from its erased children. -/
@[expose] def quoteOp : {k : Kind} → (o : TyOp k) → ((p : o.Arg) → QuoteD (o.sort p)) → QuoteD k
  | _, .lit n, _ => .lit n
  | _, .add, c => .add (c false) (c true)
  | _, .nat, _ => .nat
  | _, .vec, c => .vec (c false) (c true)
  | _, .arrow, c => .arrow (c false) (c true)
  | _, .mono, c => .mono (c ())
  | _, .all, c => .all (c ())

/-- Erase a type-level term. -/
@[expose] def quote {Θ : List Kind} {k : Kind} (t : TySig.Term Θ k) : QuoteD k :=
  IFreeM.fold (D := fun j => QuoteD j.2) (fun j x => quoteVar j.2 x.index)
    (fun _ o c => quoteOp o c) t

/-- Erase one head from its erased children. -/
@[expose] def eraseOp {Θ : List Kind} : (h : Shape) → heads.Ann TySig h Θ → (h.Arg → Src.Expr) →
    Src.Expr
  | .lit k, _, _ => .lit k
  | .rep, _, _ => .rep
  | .lam, a, c => .lam (quote (a _ .zero)) (c ())
  | .app, _, c => .app (c false) (c true)
  | .sabs, _, c => .sabs (c ())
  | .sapp, a, c => .sapp (c ()) (quote (a _ (.succ .zero)))
  | .conv, _, c => c ()

/-- Erase a typed term to the source mirror. -/
@[expose] def erase {Θ : List Kind} {Γ : List (TySig.Term Θ .scheme)} {s : TySig.Term Θ .scheme}
    (t : Tm Θ Γ s) : Src.Expr :=
  IFreeM.fold (P := lang.toFamily.polynomial) (D := fun _ => Src.Expr) (fun _ x => .var x.index)
    (fun _ o c => eraseOp o.1.1 o.1.2 c) t

/-- The identity on terms, `noncomputable`, so that the code generator cannot compile a
declaration written through it. -/
@[expose] noncomputable def uncompiled (Θ : List Kind) (Γ : List (TySig.Term Θ .scheme))
    (s : TySig.Term Θ .scheme) (t : Tm Θ Γ s) : Tm Θ Γ s :=
  t

end PolyFunTest.ToyImport

/-! ## The importer -/

public meta section

namespace PolyFunTest.ToyImport

open Lean Meta Elab Command IPFunctor IPFunctor.Import Examples.ScopedVectors

deriving instance ToExpr for Src.Size
deriving instance ToExpr for Src.Ty
deriving instance ToExpr for Src.Scheme
deriving instance ToExpr for Src.Expr

/-! ### Type arithmetic on the mirror -/

/-- Shift the size variables at or above `c` past one new binder. -/
def Src.Size.shift (c : ℕ) : Src.Size → Src.Size
  | .lit n => .lit n
  | .add m n => .add (m.shift c) (n.shift c)
  | .var i => .var (if i < c then i else i + 1)

/-- Shift the size variables of a type at or above `c`. -/
def Src.Ty.shift (c : ℕ) : Src.Ty → Src.Ty
  | .nat => .nat
  | .vec n a => .vec (n.shift c) (a.shift c)
  | .arrow a b => .arrow (a.shift c) (b.shift c)

/-- Shift the free size variables of a scheme past one new binder. -/
def Src.Scheme.shift (c : ℕ := 0) : Src.Scheme → Src.Scheme
  | .mono t => .mono (t.shift c)
  | .all s => .all (s.shift (c + 1))

/-- Substitute `v` for size variable `0`, lowering the others. -/
def Src.Size.inst (v : Src.Size) : Src.Size → Src.Size
  | .lit n => .lit n
  | .add m n => .add (Src.Size.inst v m) (Src.Size.inst v n)
  | .var 0 => v
  | .var (i + 1) => .var i

/-- Substitute `v` for size variable `0` in a type. -/
def Src.Ty.inst (v : Src.Size) : Src.Ty → Src.Ty
  | .nat => .nat
  | .vec n a => .vec (Src.Size.inst v n) (Src.Ty.inst v a)
  | .arrow a b => .arrow (Src.Ty.inst v a) (Src.Ty.inst v b)

/-! ### Head tables -/

/-- The kind of sizes. -/
def sizeKind : Lean.Expr := mkConst ``Kind.size

/-- The type-level scope at `depth` size parameters. -/
def tyScope (depth : ℕ) : MetaM IPFunctor.Import.Scope := do
  (← Syntax.ofSignature (mkConst ``TySig)).scope #[] (Array.replicate depth sizeKind)

/-- The type-level tree of a size. -/
def sizeTree : Src.Size → Tree
  | .lit n => .node (.const ``TyTerm.lit (scopeArgs := .ctx) (pre := #[mkNatLit n])) #[]
  | .add m n => .node (.const ``TyTerm.add (scopeArgs := .ctx))
      #[(.keep [], sizeTree m), (.keep [], sizeTree n)]
  | .var i => .var i

/-- The type-level tree of a type. -/
def tyTree : Src.Ty → Tree
  | .nat => .node (.const ``TyTerm.nat (scopeArgs := .ctx)) #[]
  | .vec n a => .node (.const ``TyTerm.vec (scopeArgs := .ctx))
      #[(.keep [], sizeTree n), (.keep [], tyTree a)]
  | .arrow a b => .node (.const ``TyTerm.arrow (scopeArgs := .ctx))
      #[(.keep [], tyTree a), (.keep [], tyTree b)]

/-- The type-level tree of a scheme; a quantifier binds a size in its body. -/
def schemeTree : Src.Scheme → Tree
  | .mono t => .node (.const ``TyTerm.mono (scopeArgs := .ctx)) #[(.keep [], tyTree t)]
  | .all s => .node (.const ``TyTerm.all (scopeArgs := .ctx)) #[(.keep [sizeKind], schemeTree s)]

/-- Quote a size, type or scheme at `depth` size parameters. -/
def quoteTree (depth : ℕ) (t : Tree) : MetaM Lean.Expr := do
  (← Syntax.ofSignature (mkConst ``TySig)).quote (← tyScope depth) t

/-- The evidence `fun ρ => rfl` of a coercion from `s` to `t` at `depth` size parameters. -/
def convEvidence (depth : ℕ) (t : Lean.Expr) : MetaM Lean.Expr := do
  let params := (listSuffixes (mkConst ``Kind) 0 (Array.replicate depth sizeKind))[0]!
  withLocalDeclD `ρ (← mkAppM ``ScopedSignature.Env #[mkConst ``Den, params]) fun ρ => do
    let shape ← mkAppM ``TValue.shape #[← mkAppM ``ScopedSignature.Term.denote
      #[mkConst ``tyAlg, t, ρ]]
    mkLambdaFVars #[ρ] (← mkEqRefl shape)

/-- A context entry: the scheme, and the number of size binders around its binding site. -/
abbrev Entry := Src.Scheme × ℕ

/-- Elaborate a source expression at `depth` size parameters in context `Γ`, nearest first:
the tree of its typed term and its scheme. -/
partial def elabExpr (depth : ℕ) (Γ : List Entry) : Src.Expr → MetaM (Tree × Src.Scheme)
  | .var i => do
    let some (s, bound) := Γ[i]? | throwError "toy: variable {i} is not in scope"
    unless bound == depth do
      throwError "toy: variable {i} is used below a size abstraction around its binding site, \
        which this frontend does not support"
    return (.var i, s)
  | .lit k => return (.node (.const ``litT (pre := #[mkNatLit k])) #[], .mono .nat)
  | .rep => throwError "toy: the primitive `rep` is not supported"
  | .lam a body => do
    let (tb, sb) ← elabExpr depth ((.mono a, depth) :: Γ) body
    let .mono b := sb | throwError "toy: a function body must be monomorphic"
    let aE ← quoteTree depth (tyTree a)
    let bE ← quoteTree depth (tyTree b)
    let monoA ← quoteTree depth (schemeTree (.mono a))
    return (.node (.const ``lamT (pre := #[aE, bE])) #[(.keep [monoA], tb)], .mono (.arrow a b))
  | .app f x => do
    let (tf, sf) ← elabExpr depth Γ f
    let (tx, _) ← elabExpr depth Γ x
    let .mono (.arrow a b) := sf | throwError "toy: applying a term that is not a function"
    let aE ← quoteTree depth (tyTree a)
    let bE ← quoteTree depth (tyTree b)
    return (.node (.const ``appT (pre := #[aE, bE])) #[(.keep [], tf), (.keep [], tx)], .mono b)
  | .sabs e => do
    let (te, se) ← elabExpr (depth + 1) (Γ.map fun (s, d) => (s.shift, d)) e
    let bodyE ← quoteTree (depth + 1) (schemeTree se)
    return (.node (.const ``sabsT (pre := #[bodyE])) #[(.enter [sizeKind] [], te)], .all se)
  | .sapp e n => do
    let (te, se) ← elabExpr depth Γ e
    let .all (.mono x) := se
      | throwError "toy: instantiating a term whose scheme is not `∀ n, t`"
    let bodyE ← quoteTree (depth + 1) (schemeTree (.mono x))
    let xE ← quoteTree (depth + 1) (tyTree x)
    let nE ← quoteTree depth (sizeTree n)
    let written := Src.Ty.inst n x
    let tE ← quoteTree depth (tyTree written)
    let params := (listSuffixes (mkConst ``Kind) 0 (Array.replicate depth sizeKind))[0]!
    let sE ← mkAppOptM ``ScopedSignature.Term.substOne
      #[none, some (mkConst ``TySig), some params, some sizeKind, some (mkConst ``Kind.type),
        some xE, some nE]
    let instantiated : Tree :=
      .node (.const ``sappT (pre := #[bodyE, nE])) #[(.keep [], te)]
    return (.node (.const ``convT (pre := #[sE, tE]) (post := #[← convEvidence depth tE]))
      #[(.keep [], instantiated)], .mono written)

/-- The native type of a source type. -/
def nativeTy : Src.Ty → Lean.Expr
  | .nat => mkConst ``Nat
  | .vec _ a => mkForall `i .default (mkConst ``Nat) (nativeTy a)
  | .arrow a b => mkForall `x .default (nativeTy a) (nativeTy b)

/-- The native meaning of a source expression without size abstractions, in a context of free
variables, nearest first. -/
def nativeExpr (Γ : List Lean.Expr) : Src.Expr → MetaM (Option Lean.Expr)
  | .var i => return Γ[i]?
  | .lit k => return some (mkNatLit k)
  | .lam a body => withLocalDeclD `x (nativeTy a) fun x => do
    let some b ← nativeExpr (x :: Γ) body | return none
    return some (← mkLambdaFVars #[x] b)
  | .app f x => do
    let some f ← nativeExpr Γ f | return none
    let some x ← nativeExpr Γ x | return none
    return some (mkApp f x)
  | _ => return none

/-- A declaration of the source. -/
structure Decl where
  /-- Its name. -/
  name : String
  /-- The earlier declarations it uses, outermost first. -/
  deps : Array String
  /-- Its scheme. -/
  scheme : Src.Scheme
  /-- Its body. -/
  body : Src.Expr
  /-- A test hook: the source acceptance compares against, when it differs from `body`. -/
  compareWith : Option Src.Expr
  /-- A test hook: write the term through `uncompiled`. -/
  uncompiled : Bool

/-! ### Decoding -/

/-- Decode a size. -/
partial def decodeSize (j : Json) : Except String Src.Size := do
  if let .ok n := j.getObjValAs? ℕ "lit" then return .lit n
  if let .ok i := j.getObjValAs? ℕ "svar" then return .var i
  if let .ok (.arr #[m, n]) := j.getObjVal? "add" then
    return .add (← decodeSize m) (← decodeSize n)
  throw s!"not a size: {j.compress}"

/-- Decode a type. -/
partial def decodeTy (j : Json) : Except String Src.Ty := do
  if j == "nat" then return .nat
  if let .ok (.arr #[n, a]) := j.getObjVal? "vec" then return .vec (← decodeSize n) (← decodeTy a)
  if let .ok (.arr #[a, b]) := j.getObjVal? "arrow" then
    return .arrow (← decodeTy a) (← decodeTy b)
  throw s!"not a type: {j.compress}"

/-- Decode a scheme. -/
partial def decodeScheme (j : Json) : Except String Src.Scheme := do
  if let .ok s := j.getObjVal? "all" then return .all (← decodeScheme s)
  return .mono (← decodeTy j)

/-- Decode an expression. -/
partial def decodeExpr (j : Json) : Except String Src.Expr := do
  if let .ok i := j.getObjValAs? ℕ "var" then return .var i
  if let .ok k := j.getObjValAs? ℕ "lit" then return .lit k
  if j == "rep" then return .rep
  if let .ok l := j.getObjVal? "lam" then
    return .lam (← decodeTy (← l.getObjVal? "arg")) (← decodeExpr (← l.getObjVal? "body"))
  if let .ok (.arr #[f, x]) := j.getObjVal? "app" then
    return .app (← decodeExpr f) (← decodeExpr x)
  if let .ok e := j.getObjVal? "sabs" then return .sabs (← decodeExpr e)
  if let .ok a := j.getObjVal? "sapp" then
    return .sapp (← decodeExpr (← a.getObjVal? "fun")) (← decodeSize (← a.getObjVal? "size"))
  throw s!"not an expression: {j.compress}"

/-- Decode a declaration. -/
def decodeDecl (j : Json) : Except String Decl := do
  let name ← j.getObjValAs? String "name"
  let deps := (j.getObjValAs? (Array String) "deps").toOption.getD #[]
  let scheme ← decodeScheme (← j.getObjVal? "scheme")
  let body ← decodeExpr (← j.getObjVal? "body")
  let compareWith ← match j.getObjVal? "compareWith" with
    | .ok c => some <$> decodeExpr c
    | .error _ => pure none
  let uncompiled := (j.getObjValAs? Bool "uncompiled").toOption.getD false
  return { name, deps, scheme, body, compareWith, uncompiled }

/-! ### The frontend -/

/-- The frontend for a list of declarations, each elaborated in the context of its
dependencies' schemes. -/
def frontend (decls : Array Decl) : MetaM (Frontend Decl) := do
  let valSyn ← Syntax.ofStacked (mkConst ``lang)
  let none := (listSuffixes (mkConst ``Kind) 0 #[])[0]!
  return { elaborate := fun d => do
    let mut Γ : List Entry := []
    for dep in d.deps do
      let some e := decls.find? (·.name == dep)
        | throwError "toy {d.name}: unknown dependency {dep}"
      Γ := (e.scheme, 0) :: Γ
    let (tree, _) ← elabExpr 0 Γ d.body
    let sorts ← Γ.toArray.mapM fun (s, _) => quoteTree 0 (schemeTree s)
    let scope ← valSyn.scope #[] sorts
    let schemeE ← quoteTree 0 (schemeTree d.scheme)
    let tree := if d.uncompiled then
        .node (.const ``uncompiled (pre := #[schemeE])) #[(.keep [], tree)]
      else tree
    let type := mkApp3 (mkConst ``Tm) none scope.ctx schemeE
    let source := toExpr (d.compareWith.getD d.body)
    return {
      base := d.name.toName
      doc := s!"The imported declaration `{d.name}`."
      syn := valSyn, scope, type, tree
      acceptance := fun c =>
        return (mkApp4 (mkConst ``erase) none scope.ctx schemeE c, source)
      equations := fun c => do
        unless d.deps.isEmpty && d.scheme matches .mono _ do return #[]
        let some rhs ← nativeExpr [] d.body | return #[]
        return #[(`evaluate_eq, mkApp2 (mkConst ``evaluate) schemeE c, rhs)] } }

/-- `toy_import "path.json" (budget n)? (check)? (decide)?` imports the declarations of a JSON
file whose path is relative to the package root. -/
syntax (name := toyImport)
  "toy_import " str (&" budget " num)? (&" check")? (&" decide")? : command

/-- Elaborate `toy_import`. -/
@[command_elab toyImport] def elabToyImport : CommandElab
  | `(toy_import $path:str $[budget $n:num]? $[check%$c]? $[decide%$dec]?) => liftTermElabM do
    let json ← readJsonFile path.getString
    let .ok items := json.getArr? | throwError "{path.getString}: expected an array"
    let decls ← match items.mapM decodeDecl with
      | .ok ds => pure ds
      | .error err => throwError "{path.getString}: {err}"
    let budget ← match n with
      | some n => pure ⟨n.getNat⟩
      | none => Budget.ambient
    importDecls (← frontend decls) decls
      { budget
        mode := if c.isSome then .check else .commit
        acceptBy := if dec.isSome then .decide else .refl }
  | _ => throwUnsupportedSyntax

end PolyFunTest.ToyImport
