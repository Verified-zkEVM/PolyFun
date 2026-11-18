/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedVectors
public meta import PolyFun.IPFunctor.Scoped.Import.Apply
public meta import PolyFun.IPFunctor.Scoped.Import.Json
public meta import PolyFun.IPFunctor.Scoped.Import.Registry
public meta import Lean.Elab.Command

/-!
# A toy JSON frontend for size-indexed vectors

A frontend of the import machinery for the language of the `ScopedVectors` tutorial. Its source
is a small typed AST in JSON: variables as de Bruijn positions, numbers, abstractions with their
argument types, applications, size abstractions and size instantiations. A file is an object
`{"format": "polyfun-toy-decls", "version": 1, "producer": p, "decls": [...]}`. Each declaration
lists the earlier declarations it uses; they form its value context, nearest first.

* The kernel side is the mirror `Src` of the source and `erase : Tm Θ Γ s → Src.Expr`, an exposed
  fold. Erasure keeps every abstraction's argument type and every instantiation's size, and drops
  the coercions the elaborator inserts.
* The meta side decodes JSON into the mirror with `JsonM` and elaborates each declaration. It
  infers the annotations every head needs from the mirror's types and inserts a coercion after
  each instantiation, from the type substitution computes to the written type. It checks scopes,
  and leaves typing to the kernel. A decoding error names the file and the path to the offending
  value; an elaboration error names the declaration and the path to the offending subterm, in the
  same segments. Its JSON decoders and its elaborator are `partial`, with no termination proof:
  the decoded mirror is the source that acceptance states, and the kernel checks every term the
  elaborator builds.

`toy_import "path.json"` adds the bundle declarations `declNames` and `declNames_length`, then
each declaration `d` with its decoded source `d.source`, its acceptance theorem
`d.accepted : erase d = d.source`, and its lazy meaning `d.meaning`, `meaningIn d η` at the
environment `η` of its dependencies' meanings (`Import.Env`). A closed monomorphic declaration also
gets the equation lemma `d.evaluate_eq`, whose right side is the native meaning written without
syntax, and a closed numeric one `d.meaning_eq`, which states its lazy meaning `d.meaning` as a
number. Options: `budget n` sets the per-declaration budget, `check` only reports the kernel's
verdicts, `decide` proves acceptance by evaluating decidable equality instead of by `Eq.refl`, and
`natives` gives each declaration its total evaluation `d.native` at its dependencies' native
values, compiled, and the theorem `d.meaning_represents : Represents _ d.meaning d.native`. Its
proof term, `meaningIn_represents` at the dependencies' theorems, is assembled by the frontend and
checked only by the kernel. With `nolint`, each declaration and its auxiliary definitions are
marked `@[nolint defsWithUnderscore]` and its equation lemmas `@[nolint checkType]`, as a frontend
marks names its source dictates. `misrepresent` replaces the proof of `d.meaning_represents` by
`True.intro`, which the kernel rejects. `lazy` gives a declaration whose size abstractions and
abstractions are outermost the equation `d.meaning_eq`, its lazy meaning written without syntax.
`equations off` leaves out every equation lemma, `equations only ["d", …]` keeps those of the
declarations named, and `equations except ["d", …]` leaves out theirs. `only ["d", …]` imports the
declarations named and those they depend on. A dependency must come earlier in the file.

`#toy_apply d` prints the application equation of `d` from `d.meaning_eq` (`Import.Apply`), as a
theorem to paste, proved by `kernel_rfl`, after a rewrite by `d.meaning_eq` when its right side
wraps a dependency.

`toy_import P from "path.json"` imports under the prefix `P`: each declaration `d` becomes `P.d`,
and the bundle declarations start with `P.manifest`, which records the file's format, version,
producer and fingerprint, and the settings `P.settings.natives`, `P.settings.lazy` and
`P.settings.equations`. The
prefix is a registry (`Import.Registry`). Importing the same file again under `P` adds only the
declarations that do not exist yet. Another file under `P` is refused, as are other settings, and a
declaration whose name exists but is not this import's or is taken by a bundle declaration.

A declaration marked `"uncompiled": true` is written through `uncompiled`, a `noncomputable`
identity on terms. The kernel accepts it, and the code generator cannot compile it, so it tests
that a compilation error rolls the import back.
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

/-! ## Meanings at the meanings of dependencies -/

/-- Lazy meanings at a closed scheme. -/
abbrev Carrier (s : TyTerm [] .scheme) : Type := SDom (s.denote tyAlg Env.empty)

/-- Native values at a closed scheme. -/
abbrev NativeCarrier (s : TyTerm [] .scheme) : Type := SNative (s.denote tyAlg Env.empty)

/-- A lazy meaning represents a native value at a closed scheme. -/
abbrev Represents (s : TyTerm [] .scheme) : Carrier s → NativeCarrier s → Prop :=
  Rep (s.denote tyAlg Env.empty)

/-- The lazy meaning of a declaration at the meanings `η` of its dependencies. -/
@[expose] noncomputable def meaningIn {Γ : List (TyTerm [] .scheme)} {s : TyTerm [] .scheme}
    (t : Tm [] Γ s) (η : Env Carrier Γ) : Carrier s :=
  model.denoteDomain SDom lazy t Env.empty η

/-- The total evaluation of a declaration at the native values `ζ` of its dependencies. -/
@[expose] def evaluateIn {Γ : List (TyTerm [] .scheme)} {s : TyTerm [] .scheme} (t : Tm [] Γ s)
    (ζ : Env NativeCarrier Γ) : NativeCarrier s :=
  model.denote SNative native t Env.empty ζ

/-- At dependencies whose meanings represent their native values, a declaration's meaning
represents its native value. -/
theorem meaningIn_represents {Γ : List (TyTerm [] .scheme)} {s : TyTerm [] .scheme}
    (t : Tm [] Γ s) {η : Env Carrier Γ} {ζ : Env NativeCarrier Γ}
    (h : Env.LiftRel Represents η ζ) : Represents s (meaningIn t η) (evaluateIn t ζ) :=
  model.denoteDomain_related lazy_related t Env.empty h

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
the tree of its typed term and its scheme. An error is reported at `loc`, the expression's place
in its declaration, whose segments follow the JSON encoding. -/
partial def elabExpr (loc : Location) (depth : ℕ) (Γ : List Entry) :
    Src.Expr → MetaM (Tree × Src.Scheme)
  | .var i => do
    let some (s, bound) := Γ[i]? | loc.fail s!"variable {i} is not in scope"
    unless bound == depth do
      loc.fail s!"variable {i} is used below a size abstraction around its binding site, \
        which this frontend does not support"
    return (.var i, s)
  | .lit k => return (.node (.const ``litT (pre := #[mkNatLit k])) #[], .mono .nat)
  | .rep => loc.fail "the primitive `rep` is not supported"
  | .lam a body => do
    let (tb, sb) ← elabExpr ((loc.into "lam").into "body") depth ((.mono a, depth) :: Γ) body
    let .mono b := sb | loc.fail "a function body must be monomorphic"
    let aE ← quoteTree depth (tyTree a)
    let bE ← quoteTree depth (tyTree b)
    let monoA ← quoteTree depth (schemeTree (.mono a))
    return (.node (.const ``lamT (pre := #[aE, bE])) #[(.keep [monoA], tb)], .mono (.arrow a b))
  | .app f x => do
    let (tf, sf) ← elabExpr ((loc.into "app").into "[0]") depth Γ f
    let (tx, _) ← elabExpr ((loc.into "app").into "[1]") depth Γ x
    let .mono (.arrow a b) := sf | loc.fail "applying a term that is not a function"
    let aE ← quoteTree depth (tyTree a)
    let bE ← quoteTree depth (tyTree b)
    return (.node (.const ``appT (pre := #[aE, bE])) #[(.keep [], tf), (.keep [], tx)], .mono b)
  | .sabs e => do
    let (te, se) ← elabExpr (loc.into "sabs") (depth + 1) (Γ.map fun (s, d) => (s.shift, d)) e
    let bodyE ← quoteTree (depth + 1) (schemeTree se)
    return (.node (.const ``sabsT (pre := #[bodyE])) #[(.enter [sizeKind] [], te)], .all se)
  | .sapp e n => do
    let (te, se) ← elabExpr ((loc.into "sapp").into "fun") depth Γ e
    let .all (.mono x) := se | loc.fail "instantiating a term whose scheme is not `∀ n, t`"
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
  /-- Its position in the file. -/
  position : ℕ := 0

/-- The source that acceptance compares against. -/
def Decl.source (d : Decl) : Src.Expr :=
  d.compareWith.getD d.body

/-- The declaration named `dep` that `d` depends on, which must come before `d` in the file. -/
def Decl.dependency (d : Decl) (decls : Array Decl) (dep : String) : Except String Decl :=
  match (decls.extract 0 d.position).find? (·.name == dep) with
  | some e => .ok e
  | none => .error <| if decls.any (·.name == dep) then s!"{dep} is not declared before {d.name}"
      else s!"unknown dependency {dep}"

/-- The declarations named `names` and those they depend on, in the order of the file. -/
def Decl.closure (decls : Array Decl) (names : Array String) : Array Decl := Id.run do
  let mut wanted := names
  for d in decls.reverse do
    if wanted.contains d.name then wanted := wanted ++ d.deps
  return decls.filter (wanted.contains ·.name)

/-! ### Decoding -/

section Decoding

open JsonM

/-- Decode a size. -/
partial def decodeSize (j : Json) : JsonM Unit Src.Size := do
  match ← variant j with
  | ("lit", some v) => return .lit (← inside "lit" (nat v))
  | ("svar", some v) => return .var (← inside "svar" (nat v))
  | ("add", some v) =>
    let (m, n) ← inside "add" (pair v decodeSize decodeSize)
    return .add m n
  | c => unknown "size" c

/-- Decode a type. -/
partial def decodeTy (j : Json) : JsonM Unit Src.Ty := do
  match ← variant j with
  | ("nat", none) => return .nat
  | ("vec", some v) =>
    let (n, a) ← inside "vec" (pair v decodeSize decodeTy)
    return .vec n a
  | ("arrow", some v) =>
    let (a, b) ← inside "arrow" (pair v decodeTy decodeTy)
    return .arrow a b
  | c => unknown "type" c

/-- Decode a scheme: `{"all": s}` or a type. -/
partial def decodeScheme (j : Json) : JsonM Unit Src.Scheme := do
  match ← variant j with
  | ("all", some s) => return .all (← inside "all" (decodeScheme s))
  | _ => return .mono (← decodeTy j)

/-- Decode an expression. -/
partial def decodeExpr (j : Json) : JsonM Unit Src.Expr := do
  match ← variant j with
  | ("var", some v) => return .var (← inside "var" (nat v))
  | ("lit", some v) => return .lit (← inside "lit" (nat v))
  | ("rep", none) => return .rep
  | ("lam", some v) =>
    inside "lam" do return .lam (← field v "arg" decodeTy) (← field v "body" decodeExpr)
  | ("app", some v) =>
    let (f, x) ← inside "app" (pair v decodeExpr decodeExpr)
    return .app f x
  | ("sabs", some v) => return .sabs (← inside "sabs" (decodeExpr v))
  | ("sapp", some v) =>
    inside "sapp" do return .sapp (← field v "fun" decodeExpr) (← field v "size" decodeSize)
  | c => unknown "expression" c

/-- Decode a declaration. -/
def decodeDecl (j : Json) : JsonM Unit Decl := do
  return {
    name := ← field j "name" str
    deps := (← optField j "deps" (elems · str)).getD #[]
    scheme := ← field j "scheme" decodeScheme
    body := ← field j "body" decodeExpr
    compareWith := ← optField j "compareWith" decodeExpr
    uncompiled := (← optField j "uncompiled" bool).getD false }

/-- The format of the toy's files. -/
def toyFormat : String := "polyfun-toy-decls"

/-- A decoded file: what the import read, and the declarations. -/
structure File where
  /-- The manifest: format, version, producer and fingerprint. -/
  manifest : Manifest
  /-- The declarations, in order. -/
  decls : Array Decl

/-- Read a file whose path is relative to the package root. -/
def readFile (path : String) : MetaM File := do
  let json ← readJsonFile path
  let decoder : JsonM Unit _ := do
    let provenance ← checkHeader json toyFormat 1 #["producer"]
    let decls ← field json "decls" (elems · decodeDecl)
    return (provenance, decls.mapIdx fun i d => { d with position := i })
  let ((provenance, decls), _) ← decoder.decode () path
  return { manifest := { format := toyFormat, version := 1, provenance := provenance.toList
                         fingerprint := Manifest.fingerprintOf json }
           decls }

end Decoding

/-! ### Lazy meanings without syntax

A declaration `Λ n₀ … Λ nⱼ₋₁, λ x₀ … λ xₖ₋₁, e` of a scheme `∀ n₀ … nⱼ₋₁, t`, whose body `e` has no
abstraction, has its lazy meaning written without syntax. Each size abstraction is a function of
its size, as the meaning of a scheme `∀ n, s` is; each abstraction is `ContinuousHom.ofFun` of its
body at the variable; and `e` is written from variables, literals, applications `asHom f x`, and
instantiations of a dependency `atSize`, followed by the coercion the elaborator inserts. A
dependency is read from the environment `η` of the dependencies' meanings, so that the kernel
meets the same lookup on both sides. Annotations stay type-level syntax, `Term.denote tyAlg t ρ`
at the size variables. The continuity proof of the abstraction at `xᵢ` is that of the meaning
applied to the earlier variables, since the kernel compares two continuous maps by their
functions. -/

/-- Apply a continuous map `hom` to `x`, through `DFunLike.coe`. -/
def mkCoeApp (hom x : Lean.Expr) : MetaM Lean.Expr := do
  let homType ← whnfR (← inferType hom)
  let #[α, β, _, _] := homType.getAppArgs | throwError "not a continuous map{indentExpr hom}"
  let βf := Lean.mkLambda `_ .default α β
  let inst ← synthInstance (← mkAppM ``DFunLike #[homType, α, βf])
  let levels := [← getLevel homType, ← getLevel α, ← getLevel β]
  return mkAppN (mkConst ``DFunLike.coe levels) #[homType, α, βf, inst, hom, x]

/-- `Term.denote tyAlg t ρ` of the type-level tree `t` at `depth` size parameters. -/
def denoteAt (depth : ℕ) (t : Tree) (ρ : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``ScopedSignature.Term.denote #[mkConst ``tyAlg, ← quoteTree depth t, ρ]

/-- The empty assignment of sizes. -/
def noSizes : MetaM Lean.Expr :=
  mkAppOptM ``ScopedSignature.Env.empty #[some (mkConst ``Kind), some (mkConst ``Den)]

/-- Where a lazy meaning is written. -/
structure LazyCtx where
  /-- The declaration's scope. -/
  scope : IPFunctor.Import.Scope
  /-- The environment of the dependencies' meanings. -/
  η : Lean.Expr
  /-- The dependencies' schemes, nearest first. -/
  deps : Array Src.Scheme
  /-- The variables of the enclosing size abstractions, nearest first. -/
  sizes : List Lean.Expr := []
  /-- The variables of the enclosing abstractions with their types, nearest first. -/
  binders : List (Lean.Expr × Src.Ty) := []

namespace LazyCtx

variable (cx : LazyCtx)

/-- `Term.denote tyAlg t ρ` of the type-level tree `t` at the size variables. -/
def denote (t : Tree) : MetaM Lean.Expr := do
  let ρ ← cx.sizes.foldrM (init := ← noSizes) fun n ρ =>
    mkAppOptM ``ScopedSignature.Env.cons
      #[some (mkConst ``Kind), some (mkConst ``Den), none, some sizeKind, some n, some ρ]
  denoteAt cx.sizes.length t ρ

/-- The shape of a type. -/
def shapeOf (t : Src.Ty) : MetaM Lean.Expr := do
  return mkApp (mkConst ``TValue.shape) (← cx.denote (tyTree t))

/-- The lazy values of a type. -/
def carrierOf (t : Src.Ty) : MetaM Lean.Expr := do
  return mkApp (mkConst ``SDom) (← cx.denote (schemeTree (.mono t)))

/-- The order on the lazy values of a type. -/
def instOf (t : Src.Ty) : MetaM Lean.Expr := do
  return mkApp (mkConst ``instSDom) (← cx.denote (schemeTree (.mono t)))

/-- The lazy meaning of an abstraction-free expression, written without syntax, with its type. A
dependency is read from `η` outside size abstractions only, as the elaborator requires. -/
partial def expr : Src.Expr → MetaM (Option (Lean.Expr × Src.Ty))
  | .var i => do
    if h : i < cx.binders.length then return some cx.binders[i]
    unless cx.sizes.isEmpty do return none
    let j := i - cx.binders.length
    let some (.mono t) := cx.deps[j]? | return none
    return some (mkApp2 cx.η cx.scope.sorts[j]! (← cx.scope.scopedVar j), t)
  | .lit k => do
    let value ← mkAppOptM ``DomainResult.value
      #[some (mkConst ``Empty), none, some (← mkAppM ``DiscreteOrder.mk #[mkNatLit k])]
    return some (value, .nat)
  | .app f x => do
    let some (f', .arrow a b) ← expr f | return none
    let some (x', _) ← expr x | return none
    let hom := mkApp3 (mkConst ``asHom) (← cx.shapeOf a) (← cx.shapeOf b) f'
    return some (← mkCoeApp hom x', b)
  | .sapp (.var i) n => do
    unless cx.sizes.isEmpty && cx.binders.length ≤ i do return none
    let j := i - cx.binders.length
    let some (.all (.mono x)) := cx.deps[j]? | return none
    let family ← withLocalDeclD `n (mkConst ``Nat) fun m => do
      let single ← mkAppOptM ``ScopedSignature.Env.single
        #[some (mkConst ``Kind), some (mkConst ``Den), some sizeKind, some m]
      mkLambdaFVars #[m] (← denoteAt 1 (schemeTree (.mono x)) single)
    let size ← denoteAt 0 (sizeTree n) (← noSizes)
    let dep := mkApp2 cx.η cx.scope.sorts[j]! (← cx.scope.scopedVar j)
    let instantiated ← mkCoeApp (mkApp2 (mkConst ``atSize) family size) dep
    let written := Src.Ty.inst n x
    let t ← denoteAt 0 (tyTree written) (← noSizes)
    let refl ← mkEqRefl (mkApp (mkConst ``TValue.shape) t)
    return some (← mkCoeApp (mkApp3 (mkConst ``convLazy) t t refl) instantiated, written)
  | _ => return none

end LazyCtx

/-- The lazy meaning of a declaration of scheme `s` whose abstractions are outermost, written
without syntax. `self` is the meaning applied to the variables bound so far. -/
partial def LazyCtx.meaning (cx : LazyCtx) (self : Lean.Expr) (s : Src.Scheme) :
    Src.Expr → MetaM (Option Lean.Expr)
  | .sabs body => do
    let .all s := s | return none
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      let cx' := { cx with sizes := n :: cx.sizes }
      let some inner ← cx'.meaning (mkApp self n) s body | return none
      return some (← mkLambdaFVars #[n] inner)
  | .lam a body => do
    let .mono (.arrow _ b) := s | return none
    let hom := mkApp3 (mkConst ``asHom) (← cx.shapeOf a) (← cx.shapeOf b) self
    withLocalDeclD `x (← cx.carrierOf a) fun x => do
      let cx' := { cx with binders := (x, a) :: cx.binders }
      let some inner ← cx'.meaning (← mkCoeApp hom x) (.mono b) body | return none
      let h ← mkAppOptM ``OmegaCompletePartialOrder.ContinuousHom.ωScottContinuous
        #[none, none, none, none, some hom]
      return some (mkAppN (mkConst ``OmegaCompletePartialOrder.ContinuousHom.ofFun [0, 0])
        #[← cx.carrierOf a, ← cx.carrierOf b, ← cx.instOf a, ← cx.instOf b,
          ← mkLambdaFVars #[x] inner, h])
  | e => do
    unless s matches .mono _ do return none
    return (← cx.expr e).map (·.1)

/-! ### The frontend -/

/-- The frontend for a list of declarations, each elaborated in the context of its
dependencies' schemes and named under the prefix `pfx`. Each declaration gets its lazy meaning at
its dependencies' meanings. With `natives`, it also gets its compiled total evaluation at its
dependencies' native values, and the theorem that its lazy meaning represents it, from its
dependencies' theorems; with `misrepresent`, that theorem's proof is wrong. With `nolint`, the
definitions and equation lemmas carry linters that skip them. With `lazy`, a declaration whose
size abstractions and abstractions are outermost gets the equation `d.meaning_eq`, its lazy
meaning written without syntax. Only the declarations that `equations` selects get equation
lemmas. -/
def frontend (decls : Array Decl) (pfx : Name := .anonymous) (natives : Bool := false)
    (nolint : Bool := false) (misrepresent : Bool := false) (equations : Select := .all)
    (lazy : Bool := false) : MetaM (Frontend Decl) := do
  let defNolint := if nolint then #[`defsWithUnderscore] else #[]
  let valSyn ← Syntax.ofStacked (mkConst ``lang)
  let none := (listSuffixes (mkConst ``Kind) 0 #[])[0]!
  return { elaborate := fun d => do
    let loc : Location := { origin := d.name }
    let mut Γ : List Entry := []
    for h : k in [0:d.deps.size] do
      let e ← ((loc.into "deps").into s!"[{k}]").check (d.dependency decls d.deps[k])
      Γ := (e.scheme, 0) :: Γ
    let (tree, _) ← elabExpr (loc.into "body") 0 Γ d.body
    let sorts ← Γ.toArray.mapM fun (s, _) => quoteTree 0 (schemeTree s)
    let scope ← valSyn.scope #[] sorts
    let schemeE ← quoteTree 0 (schemeTree d.scheme)
    let tree := if d.uncompiled then
        .node (.const ``uncompiled (pre := #[schemeE])) #[(.keep [], tree)]
      else tree
    let type := mkApp3 (mkConst ``Tm) none scope.ctx schemeE
    let closed := d.deps.isEmpty
    -- The dependencies, nearest first, and the environments of their meanings and native values.
    let ns ← getCurrNamespace
    let deps := d.deps.reverse.map fun dep => ns ++ pfx ++ dep.toName
    let depsAt (suffix : Name) := deps.map (mkConst <| · ++ suffix)
    let carrier := mkConst ``Carrier
    let nativeCarrier := mkConst ``NativeCarrier
    let η ← scope.env carrier (depsAt `meaning)
    let ζ ← scope.env nativeCarrier (depsAt `native)
    return {
      base := pfx ++ d.name.toName
      doc := s!"The imported declaration `{d.name}`."
      syn := valSyn, scope, type, tree
      nolint := defNolint
      equationNolint := if nolint then #[`checkType] else #[]
      extras := fun c => do
        let source : Extra :=
          { suffix := `source
            type := mkConst ``Src.Expr
            value := toExpr d.source
            doc := s!"The decoded source of `{d.name}`."
            nolint := defNolint }
        let meaning : Extra :=
          { suffix := `meaning, type := mkApp carrier schemeE
            value := mkAppN (mkConst ``meaningIn) #[scope.ctx, schemeE, c, η]
            doc := s!"The lazy meaning of `{d.name}` at the meanings of its dependencies."
            nolint := defNolint }
        unless natives do return #[source, meaning]
        return #[source, meaning,
          { suffix := `native, type := mkApp nativeCarrier schemeE
            value := mkAppN (mkConst ``evaluateIn) #[scope.ctx, schemeE, c, ζ], compile := true
            doc := s!"The total evaluation of `{d.name}` at the native values of its \
              dependencies, compiled."
            nolint := defNolint }]
      acceptance := fun c =>
        return (mkApp4 (mkConst ``erase) none scope.ctx schemeE c,
          mkConst (c.constName! ++ `source))
      equations := fun c => do
        unless equations.includes d.name do return #[]
        -- The left side of `meaning_eq` is the auxiliary definition `d.meaning`, not yet added.
        let meaning := mkConst (c.constName! ++ `meaning)
        let mut eqs := #[]
        if let .mono t := d.scheme then
          if closed then if let some rhs ← nativeExpr [] d.body then
            eqs := eqs.push (`evaluate_eq, mkApp2 (mkConst ``evaluate) schemeE c, rhs)
            if t matches .nat then
              let number ← mkAppOptM ``DomainResult.value
                #[some (mkConst ``Empty), Option.none, some (← mkAppM ``DiscreteOrder.mk #[rhs])]
              eqs := eqs.push (`meaning_eq, meaning, number)
        if lazy && !eqs.any (·.1 == `meaning_eq) then
          let cx : LazyCtx := { scope, η, deps := Γ.toArray.map (·.1) }
          if let some rhs ← cx.meaning meaning d.scheme d.body then
            eqs := eqs.push (`meaning_eq, meaning, rhs)
        return eqs
      theorems := fun c => do
        unless natives do return #[]
        -- The statement names `d.meaning` and `d.native`, which are not yet added.
        let type := mkApp3 (mkConst ``Represents) schemeE (mkConst (c.constName! ++ `meaning))
          (mkConst (c.constName! ++ `native))
        let proof ← if misrepresent then pure (mkConst ``True.intro) else do
          let hη ← scope.liftRel carrier nativeCarrier (mkConst ``Represents) (depsAt `meaning)
            (depsAt `native) (depsAt `meaning_represents)
          pure (mkAppN (mkConst ``meaningIn_represents) #[scope.ctx, schemeE, c, η, ζ, hη])
        return #[{ suffix := `meaning_represents, type, proof
                   doc := s!"The lazy meaning of `{d.name}` represents its total evaluation." }] } }

/-- The bundle declarations under the prefix `pfx`: `pfx.declNames`, the names the file declares,
and `pfx.declNames_length`, their number, proved by evaluation in the kernel. -/
def bundleOf (decls : Array Decl) (pfx : Name := .anonymous) : MetaM (Array BundleDecl) := do
  let names := mkConst ((← getCurrNamespace) ++ pfx ++ `declNames)
  let length := mkApp2 (mkConst ``List.length [0]) (mkConst ``String) names
  let listType ← mkAppM ``List #[mkConst ``String]
  return #[.defn (pfx ++ `declNames) listType (toExpr (decls.map (·.name)).toList)
      "The names of the imported declarations.",
    .decide (pfx ++ `declNames_length) (← mkEq length (mkNatLit decls.size))]

/-- `toy_import (P from)? "path.json" (only [d, …])? (budget n)? (check)? (decide)? (natives)?
(nolint)? (misrepresent)? (lazy)? (equations (off | only [d, …] | except [d, …]))?` imports the
declarations of a JSON file whose path is relative to the package root, under the prefix `P` if
one is given: those named after `only` and the declarations they depend on, or all of them. -/
syntax (name := toyImport)
  "toy_import " (ident " from ")? str (&" only" " [" str,* "]")? (&" budget " num)? (&" check")?
    (&" decide")? (&" natives")? (&" nolint")? (&" misrepresent")? (&" lazy")?
    (&" equations" importSelect)? : command

/-- Elaborate `toy_import`. Under a prefix, the import goes through the registry: it declares
the manifest, the settings `natives`, `lazy` and `equations`, and the other bundle declarations, and
`Registry.plan` chooses the declarations to add. -/
@[command_elab toyImport] def elabToyImport : CommandElab
  | `(toy_import $[$p:ident from]? $path:str $[only [$only,*]]? $[budget $n:num]? $[check%$c]?
      $[decide%$dec]? $[natives%$nat]? $[nolint%$nl]? $[misrepresent%$mis]? $[lazy%$lz]?
      $[equations $sel]?) =>
    liftTermElabM do
      let file ← readFile path.getString
      let names := file.decls.map (·.name)
      let decls ← match only with
        | some only =>
          let only := only.getElems.map (·.getString)
          (Select.only only).validate "" names
          pure (Decl.closure file.decls only)
        | none => pure file.decls
      let equations ← match sel with
        | some sel => Select.ofSyntax sel
        | none => pure .all
      equations.validate "equations" names
      let budget ← match n with
        | some n => pure ⟨n.getNat⟩
        | none => Budget.ambient
      let cfg : IPFunctor.Import.Config :=
        { budget
          mode := if c.isSome then .check else .commit
          acceptBy := if dec.isSome then .decide else .refl }
      let pfx := (p.map (·.getId)).getD .anonymous
      let fe ← frontend file.decls pfx nat.isSome nl.isSome mis.isSome equations lz.isSome
      let bundle ← bundleOf file.decls pfx
      if p.isNone then
        return ← importDecls fe decls cfg (bundle := bundle)
      let registry : Registry :=
        { pfx, manifest := file.manifest
          settings := [("natives", toString nat.isSome), ("lazy", toString lz.isSome),
            ("equations", toString equations)]
          reserved := fun b => bundle.any (·.base == b) }
      let base (d : Decl) : Name := pfx ++ d.name.toName
      let plan ← registry.plan decls base fun d => (base d ++ `source, toExpr d.source)
      importDecls fe plan.todo cfg (bundle := ← registry.bundle plan bundle)
  | _ => throwUnsupportedSyntax

/-- `toy_import_unscoped "path.json"` commits the declarations in one `atomically` block without
`importDecls`' per-declaration heartbeat scopes, so they share the command's heartbeats. It is the
control for the scoping test. -/
syntax (name := toyImportUnscoped) "toy_import_unscoped " str : command

/-- Elaborate `toy_import_unscoped`. -/
@[command_elab toyImportUnscoped] def elabToyImportUnscoped : CommandElab
  | `(toy_import_unscoped $path:str) => liftTermElabM do
    let decls := (← readFile path.getString).decls
    let fe ← frontend decls
    let cfg : IPFunctor.Import.Config := { budget := ← Budget.ambient }
    atomically do
      for d in decls do
        commitDecl cfg (← fe.elaborate d)
  | _ => throwUnsupportedSyntax

/-! ### Application equations -/

/-- Evaluate a type-level term at the values of its size variables, nearest first, as `tyAlg`
does: sizes to numbers, types to `TValue` and schemes to `SScheme`. -/
partial def evalTyTerm (t : Lean.Expr) (env : Array Lean.Expr) : MetaM (Option Lean.Expr) := do
  let t := t.headBeta
  let args := t.getAppArgs
  let ev (i : ℕ) := evalTyTerm args[i]! env
  let both (i : ℕ) (k : Lean.Expr → Lean.Expr → Lean.Expr) : MetaM (Option Lean.Expr) := do
    let some x ← ev i | return none
    let some y ← ev (i + 1) | return none
    return some (k x y)
  match t.getAppFn.constName? with
  | some ``ScopedSignature.Term.var => return (EnvReader.varIndex? args.back!).bind (env[·]?)
  | some ``TyTerm.lit => return args[1]?
  | some ``TyTerm.add => both 1 mkNatAdd
  | some ``TyTerm.nat => return some (mkConst ``TValue.nat)
  | some ``TyTerm.vec => both 1 (mkApp2 (mkConst ``TValue.vec))
  | some ``TyTerm.arrow => both 1 (mkApp2 (mkConst ``TValue.arrow))
  | some ``TyTerm.mono => return (← ev 1).map (mkApp (mkConst ``SScheme.mono))
  | some ``TyTerm.all => withLocalDeclD `n (mkConst ``Nat) fun n => do
    let some body ← evalTyTerm args[1]! (#[n] ++ env) | return none
    return some (mkApp (mkConst ``SScheme.all) (← mkLambdaFVars #[n] body))
  | _ => return none

/-- Fresh variables `x₀, x₁, …` for the arguments of an evaluated function type. -/
partial def withArgs {α : Type} (t : Lean.Expr) (xs : Array Lean.Expr)
    (k : Array Lean.Expr → MetaM α) : MetaM α := do
  if t.isAppOfArity ``TValue.arrow 2 then
    let type := mkApp (mkConst ``SDom) (mkApp (mkConst ``SScheme.mono) (t.getArg! 0))
    withLocalDeclD (.mkSimple s!"x{xs.size}") type fun x => withArgs (t.getArg! 1) (xs.push x) k
  else k xs

/-- Fresh size variables for the quantifiers of an evaluated scheme, named by `names` as far as
they go, and its monomorphic type. -/
partial def withSizes {α : Type} (s : Lean.Expr) (names : List Name) (ns : Array Lean.Expr)
    (k : Array Lean.Expr → Lean.Expr → MetaM α) : MetaM α := do
  if s.isAppOfArity ``SScheme.all 1 then
    withLocalDeclD (names.headD `n) (mkConst ``Nat) fun n =>
      withSizes ((s.getArg! 0).beta #[n]) names.tail (ns.push n) k
  else if s.isAppOfArity ``SScheme.mono 1 then k ns (s.getArg! 0)
  else throwError "#toy_apply: not an evaluated scheme{indentExpr s}"

/-- Whether a right side is a wrapper: below applications `asHom f x`, coercions `convLazy` and
instantiations `atSize`, the meaning of a dependency. -/
partial def isWrapper (e : Lean.Expr) : Bool :=
  if e.isAppOfArity ``DFunLike.coe 6 then
    let hom := e.getArg! 4
    if hom.isAppOfArity ``asHom 3 then isWrapper (hom.getArg! 2)
    else if hom.isAppOfArity ``convLazy 3 || hom.isAppOfArity ``atSize 2 then
      isWrapper (e.getArg! 5)
    else false
  else match e with
    | .const (.str _ "meaning") _ => true
    | _ => false

/-- How the toy prints application equations: a size quantifier is a size variable, and an
application is `asHom f x`. -/
def applyPrinter : ApplyPrinter where
  command := "#toy_apply"
  evalTerm := evalTyTerm
  telescope s names k := withSizes s names #[] fun ns t => withArgs t #[] (k ns)
  apply f xs := xs.foldlM (fun f x => do mkCoeApp (← mkAppM ``asHom #[f]) x) f
  isWrapper := isWrapper

/-- `#toy_apply d` prints the application equation of the imported declaration `d`, read from
`d.meaning_eq`, as a theorem whose proof is `kernel_rfl`. -/
syntax (name := toyApply) "#toy_apply " ident : command

/-- Elaborate `#toy_apply`. -/
@[command_elab toyApply] def elabToyApply : CommandElab
  | `(#toy_apply $id:ident) => do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    liftTermElabM (applyPrinter.logApplyEquation decl)
  | _ => throwUnsupportedSyntax

end PolyFunTest.ToyImport
