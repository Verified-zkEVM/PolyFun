/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import Lean.Elab.Command
public import Cslib.Foundations.Data.PFunctor.Free
public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.Free.Code

/-!
# The polynomial-functor signature of an inductive program type

`derive_free_sig T` reads an inductive type `T p₁ ⋯ pₘ α` of program trees and defines the
polynomial functor `T.Sig` of its operations, together with the equivalence between `T α` and
the free monad `PFunctor.FreeM T.Sig α`.

The type `T` has parameters `p₁ ⋯ pₘ α`, the last one the result type `α`, and no indices. Its
constructors are

* exactly one return `ret (a : α)`, whose only field has type `α`;
* operations `op x₁ ⋯ xₙ k` with at most one continuation `k`: a field `k : D → T p₁ ⋯ pₘ α`
  (direction `D`, which may depend on the fields `xᵢ`, including type fields such as
  `sample (β : Type) (k : β → T α)`), a field `k : T p₁ ⋯ pₘ α` (direction `PUnit`), or none
  (direction `PEmpty`).

The fields `xᵢ` of an operation do not mention `α` or `T`, and the continuation may stand at any
position among the fields. A constructor of another shape (a continuation of several arguments,
two continuations, a recursive occurrence under another type former) is refused with an error
naming it.

## Main definitions

For `derive_free_sig T`, with the generated names in the namespace `N` (by default `T`):

* `N.Op p₁ ⋯ pₘ` — the operations: one constructor `N.Op.op x₁ ⋯ xₙ` for each operation
  constructor of `T`, with its fields other than the continuation;
* `N.Op.dir` — the direction type of an operation;
* `N.Sig p₁ ⋯ pₘ : PFunctor` — the polynomial functor `⟨N.Op p₁ ⋯ pₘ, N.Op.dir⟩`;
* `N.toFreeM`, `N.ofFreeM`, `N.equivFreeM : T p₁ ⋯ pₘ α ≃ PFunctor.FreeM (N.Sig p₁ ⋯ pₘ) α`;
* `N.Sig.op` — the summand of one operation `op`: positions the tuples `Σ' x₁ ⋯, τₙ` of its
  fields, directions those of `N.Op.op x₁ ⋯ xₙ`;
* `N.SigSum` — the sum `N.Sig.op₁ + (N.Sig.op₂ + ⋯)` of the summands, PolyFun's coproduct of
  polynomial functors;
* `N.sigEquivSum : PFunctor.Equiv (N.Sig p₁ ⋯ pₘ) (N.SigSum p₁ ⋯ pₘ)`.

With the option `(code := true)`, also:

* `N.code p₁ ⋯ pₘ : PFunctor.Code` — the code of the signature, one operation code
  for each operation, its fields under `ULift` (and `PLift` for a proof field) in the universe of
  the positions of `N.Sig`;
* `N.sigEquivCode : PFunctor.Equiv (N.Sig p₁ ⋯ pₘ) (Code.interp (N.code p₁ ⋯ pₘ))`;
* `N.equivCode : T p₁ ⋯ pₘ α ≃ PFunctor.FreeM (Code.interp (N.code p₁ ⋯ pₘ)) α`, so that the
  relational lift `Code.Rel` and its theorems in `PolyFun.PFunctor.Free.Code` apply to `T`.

## Main results

* `N.ofFreeM_toFreeM`, `N.toFreeM_ofFreeM` — the two round trips;
* `N.toFreeM_bind` — with the option `(bind := f)`, `toFreeM` carries the bind `f` of `T` to
  `FreeM.bind`.

## Implementation

The command reads `T` in two steps. `toIndDesc T` computes the description `IndDesc` of `T`:
for each constructor, the kind (`FieldKind`) of each field, a parameter, a recursive field
`T p₀ ⋯ pₘ`, a recursive field under an exponent `D → T p₀ ⋯ pₘ`, or other. `readSig` reads the
program-tree shape off this description (the return constructor, the continuation of each
operation and its direction) and `sigSource` prints the declarations. When `T` is declared in a
`meta section`, `toFreeM`, `ofFreeM` and `equivFreeM` are declared `noncomputable`.

All generated proofs are tactic proofs (`induction`, `cases`, `simp only`, `rfl`) checked by the
kernel.

## Usage

```
derive_free_sig Prog
derive_free_sig Prog (namespace := ProgGen) (bind := Prog.bind)
derive_free_sig Prog (namespace := ProgCode) (code := true)
derive_free_sig? Prog
```

The namespace `N` of the option `(namespace := N)` is taken relative to the current namespace.
`derive_free_sig?` also prints the generated source. The declarations are elaborated from their
printed source, with the binder types printed under full names.
-/

public section

meta section

namespace PFunctor.DeriveFreeSig

open Lean Elab Meta Term Command

/-- The direction of an operation: the domain of a function continuation (as printed), `PUnit`
for a continuation that is not a function, `PEmpty` for no continuation. -/
inductive Dir where
  /-- No continuation: direction `PEmpty`. -/
  | empty
  /-- A continuation `k : T α`: direction `PUnit`. -/
  | unit
  /-- A continuation `k : D → T α`, with `D` printed. -/
  | fn (dom : String)
  deriving Inhabited

/-- A field of an operation other than its continuation: its name, its printed type, and whether
the direction mentions it. -/
structure OpField where
  /-- The binder name. -/
  name : Name
  /-- The printed type. -/
  type : String
  /-- Whether the direction type mentions the field. -/
  inDir : Bool
  /-- Whether the field is a proof (its type is a proposition). -/
  isProp : Bool
  /-- Whether the direction or a later field type mentions the field. -/
  used : Bool
  deriving Inhabited

/-- An operation constructor of `T`. -/
structure OpData where
  /-- The constructor of `T`. -/
  ctor : Name
  /-- The last component of the constructor name. -/
  short : Name
  /-- The fields other than the continuation, in order. -/
  fields : Array OpField
  /-- The position of the continuation among all fields of the constructor. -/
  contIdx : Option Nat
  /-- The direction. -/
  dir : Dir
  /-- The number of fields of the constructor. -/
  numFields : Nat
  deriving Inhabited

/-- What `derive_free_sig` reads off the inductive type `T`. -/
structure SigData where
  /-- The inductive type. -/
  T : Name
  /-- The parameters before the result type: names and printed types. -/
  params : Array (Name × String)
  /-- The result type parameter: name and printed type. -/
  alpha : Name × String
  /-- The return constructor. -/
  ret : Name
  /-- The operation constructors. -/
  ops : Array OpData
  /-- The printed sort of the directions. -/
  dirSort : String
  /-- The universe parameters of `T`. -/
  lvls : List Name
  /-- Whether `T` is declared `meta` (in a `meta section` of a module); the generated
  functions are then `noncomputable`. -/
  isMeta : Bool
  /-- Binder names not used by parameters and fields. -/
  freshNames : Array Name
  deriving Inhabited

/-- The source text of `e`, with full names. -/
def ppText (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true)
    (ppExpr e)
  return fmt.pretty 100000

/-- The first of `base`, `base₁`, `base₂`, … not in `used`. -/
partial def freshIn (base : Name) (used : Array Name) (i : Nat := 0) : Name :=
  let c := if i == 0 then base else base.appendIndexAfter i
  if used.contains c then freshIn base used (i + 1) else c

/-- The binder names of the first `n` binders of `t`. -/
def binderNames (t : Expr) (n : Nat) : List Name :=
  match n, t with
  | n + 1, .forallE nm _ b _ => nm :: binderNames b n
  | _, _ => []

/-- `t` with the names of its first binders replaced by `names`. -/
def renameBinders (t : Expr) : List Name → Expr
  | n :: ns =>
    match t with
    | .forallE _ d b bi => .forallE n d (renameBinders b ns) bi
    | _ => t
  | [] => t

/-- Accessible names, distinct from each other and from `used`, for the binder names `ns`. -/
def accessibleNames (ns : List Name) (used : Array Name) (pre : Name) : List Name × Array Name :=
  ns.foldl (init := ([], used)) fun (acc, used) n =>
    let base := if n.hasMacroScopes || n.isAnonymous || n.isInternal then pre
      else n
    let n' := freshIn base used
    (acc ++ [n'], used.push n')

/-- Whether the constant `T` occurs in `e`. -/
def mentions (T : Name) (e : Expr) : Bool :=
  (e.find? fun x => x.isConstOf T).isSome

/-! ## The description of an inductive type -/

/-- The kind of a constructor field, relative to the parameters `p₀ ⋯ pₘ` of the inductive type
`T`: the parameter `pᵢ` itself, the type `T p₀ ⋯ pₘ`, a function `D → T p₀ ⋯ pₘ` whose domain `D`
may depend on the earlier fields and does not mention `T`, or anything else not mentioning `T`. -/
inductive FieldKind where
  /-- The field has type `pᵢ`. -/
  | param (idx : Nat)
  /-- The field has type `T p₀ ⋯ pₘ`. -/
  | recursive
  /-- The field has type `D → T p₀ ⋯ pₘ`, with `D` not mentioning `T`. -/
  | expRecursive
  /-- The field type does not mention `T` and is not a parameter. -/
  | other
  deriving Repr, Inhabited, DecidableEq

/-- A constructor: its name and the kind of each of its fields. -/
structure CtorDesc where
  /-- The constructor. -/
  name : Name
  /-- The kinds of its fields, in order. -/
  fields : Array FieldKind
  deriving Inhabited

/-- The description of an inductive type: its name, its number of parameters and its
constructors. The signature of `derive_free_sig` is computed from it. -/
structure IndDesc where
  /-- The inductive type. -/
  name : Name
  /-- The number of parameters. -/
  numParams : Nat
  /-- The constructors. -/
  ctors : Array CtorDesc
  deriving Inhabited

/-- The kind of a field of type `ty` of a constructor of `T`, over the parameters `ps`, or an
error when `T` occurs in `ty` other than as `T ps` or `D → T ps`. -/
def classifyField (T : Name) (ps : Array Expr) (ty : Expr) : MetaM FieldKind := do
  if let some i := ps.findIdx? (· == ty) then return .param i
  unless mentions T ty do return .other
  let self := mkAppN (.const T ((← getConstInfoInduct T).levelParams.map mkLevelParam)) ps
  if ty == self then return .recursive
  forallTelescope ty fun ds body => do
    unless body == self && ds.size == 1 do
      throwError "derive_free_sig: the field type `{ty}` of `{T}` is neither `{self}` nor a \
        function `D → {self}` of one argument"
    if mentions T (← inferType ds[0]!) then
      throwError "derive_free_sig: the domain of the field type `{ty}` mentions `{T}`"
    return .expRecursive

/-- The description of the inductive type `T`. -/
def toIndDesc (T : Name) : MetaM IndDesc := do
  let iv ← getConstInfoInduct T
  let mut ctors : Array CtorDesc := #[]
  for c in iv.ctors do
    let cv ← getConstInfoCtor c
    let cd ← forallTelescopeReducing cv.type fun xs _ => do
      let ps := xs.extract 0 cv.numParams
      let mut fields : Array FieldKind := #[]
      for i in [:cv.numFields] do
        fields := fields.push (← classifyField T ps (← inferType xs[cv.numParams + i]!))
      return { name := c, fields }
    ctors := ctors.push cd
  return { name := T, numParams := iv.numParams, ctors }

/-! ## The signature -/

/-- Read the inductive type `T`, with description `desc`, as a type of program trees. -/
def readSig (desc : IndDesc) : TermElabM SigData := do
  let T := desc.name
  let iv ← getConstInfoInduct T
  unless iv.numIndices == 0 do
    throwError "derive_free_sig: `{T}` has indices; the result type must be its last parameter"
  unless iv.numParams ≥ 1 do
    throwError "derive_free_sig: `{T}` has no parameter for the result type"
  unless iv.numNested == 0 do
    throwError "derive_free_sig: `{T}` is a nested inductive type"
  -- a parameter named like a generated declaration would be shadowed by it
  let reserved := #[`Op, `Sig, `SigSum, `dir]
  let (pnames, used) := accessibleNames (binderNames iv.type (iv.numParams - 1)) reserved `p
  let (anames, used) := accessibleNames
    ((binderNames iv.type iv.numParams).drop (iv.numParams - 1)) used `α
  let pnames := pnames ++ anames
  forallBoundedTelescope (renameBinders iv.type pnames) iv.numParams fun ps _ => do
    let α := ps.back!
    let mut params := #[]
    for p in ps.pop do
      params := params.push ((← p.fvarId!.getUserName), ← ppText (← inferType p))
    let alpha := ((← α.fvarId!.getUserName), ← ppText (← inferType α))
    let pused := used
    let mut used := used
    let mut ret? : Option Name := none
    let mut ops : Array OpData := #[]
    let mut dirSort? : Option String := none
    for cd in desc.ctors do
      let ctor := cd.name
      let cv ← getConstInfoCtor ctor
      let ty ← instantiateForall cv.type ps
      let (fnames, used') := accessibleNames (binderNames ty cv.numFields) pused `x
      used := used ++ used'
      let r ← forallBoundedTelescope (renameBinders ty fnames) cv.numFields fun fs _ => do
        -- the return constructor: one field, of type `α`
        if cd.fields == #[.param (iv.numParams - 1)] then
          return Sum.inl ctor
        let mut cont? : Option (Nat × Dir × Expr) := none
        for i in [:fs.size] do
          let k := cd.fields[i]!
          unless k == .recursive || k == .expRecursive do continue
          if cont?.isSome then
            throwError "derive_free_sig: `{ctor}` has two continuations"
          if k == .recursive then
            cont? := some (i, .unit, Lean.mkConst ``True)
          else
            let D ← forallTelescope (← inferType fs[i]!) fun ds _ => inferType ds[0]!
            if D.containsFVar α.fvarId! then
              throwError "derive_free_sig: the direction `{D}` of `{ctor}` mentions the \
                result type"
            cont? := some (i, .fn (← ppText D), D)
        let mut fields := #[]
        let mut sort? : Option String := none
        for i in [:fs.size] do
          if cont?.map (·.1) == some i then continue
          let fty ← inferType fs[i]!
          if fty.containsFVar α.fvarId! then
            throwError "derive_free_sig: the field {i} of `{ctor}` mentions the result type"
          let inDir := match cont? with
            | some (_, .fn _, D) => D.containsFVar fs[i]!.fvarId!
            | _ => false
          let mut used := inDir
          for j in [i + 1:fs.size] do
            if cont?.map (·.1) != some j then
              used := used || (← inferType fs[j]!).containsFVar fs[i]!.fvarId!
          let pr ← Meta.isProp fty
          fields := fields.push
            { name := (← fs[i]!.fvarId!.getUserName), type := ← ppText fty, inDir
              isProp := pr, used }
        if let some (_, .fn _, D) := cont? then
          sort? := some (← ppText (← inferType D))
        let dir := match cont? with
          | some (_, d, _) => d
          | none => .empty
        let sh := Name.mkSimple (ctor.getString!)
        let contIdx := cont?.map (·.1)
        let op : OpData :=
          { ctor := ctor, short := sh, fields := fields, contIdx := contIdx, dir := dir,
            numFields := fs.size }
        return Sum.inr (op, sort?)
      match r with
      | .inl c =>
        if ret?.isSome then throwError "derive_free_sig: `{T}` has two return constructors"
        ret? := some c
      | .inr (op, sort?) =>
        ops := ops.push op
        if let some s := sort? then
          match dirSort? with
          | none => dirSort? := some s
          | some s' => unless s == s' do
            throwError "derive_free_sig: the directions of `{T}` lie in `{s'}` and `{s}`"
    let some ret := ret?
      | throwError "derive_free_sig: `{T}` has no return constructor `ret (a : α)`"
    let freshNames := #[`k, `d, `s, `f, `o, `q, `a, `β].map (freshIn · used)
    return {
      T := T, params := params, alpha := alpha, ret := ret, ops := ops
      dirSort := dirSort?.getD "Type", lvls := iv.levelParams
      isMeta := isMarkedMeta (← getEnv) T, freshNames := freshNames }

/-- The number of leading commands of `sigSource` that define `N.Op`, `N.Op.dir` and `N.Sig`;
they do not depend on the universe argument of `sigSource`. -/
def sigHeadSize : Nat := 3

/-- The source of the declarations of `derive_free_sig T` in the namespace `N`, one command for
each declaration. The positions of `N.Sig` lie in `Type lA`; the summand of an operation without
fields has the position type `PUnit.{lA + 1}`. -/
def sigSource (d : SigData) (N : Name) (bind? : Option Name) (lA : String) :
    Array String := Id.run do
  let k := d.freshNames[0]!.toString
  let dv := d.freshNames[1]!.toString
  let sv := d.freshNames[2]!.toString
  let fv := d.freshNames[3]!.toString
  let ov := d.freshNames[4]!.toString
  let qv := d.freshNames[5]!.toString
  let av := d.freshNames[6]!.toString
  let bv := d.freshNames[7]!.toString
  let T := d.T.toString
  let mk := if d.isMeta then "noncomputable " else ""
  let nm (s : String) := s!"{N}.{s}"
  let lv := if d.lvls.isEmpty then "" else ".{" ++ ", ".intercalate (d.lvls.map toString) ++ "}"
  let decl (s : String) := s!"_root_.{nm s}{lv}"
  let pExpl := String.join (d.params.toList.map fun (n, t) => s!" ({n} : {t})")
  let pImpl := String.join (d.params.toList.map fun (n, t) => s!" \{{n} : {t}}")
  let pArgs := String.join (d.params.toList.map fun (n, _) => s!" {n}")
  let pHoles := String.join (d.params.toList.map fun _ => " _")
  let (a, aTy) := d.alpha
  let aImpl := s!" \{{a} : {aTy}}"
  let tA := s!"{T}{pArgs} {a}"
  let sig := s!"({nm "Sig"}{pArgs})"
  let opTy := s!"{nm "Op"}{pArgs}"
  let short (o : OpData) := o.short.toString
  -- patterns of the fields of an operation, `_` where `useAll` is false and the direction does
  -- not mention the field
  let fieldPats (o : OpData) (useAll : Bool) : String :=
    String.join (o.fields.toList.map fun f =>
      if useAll || f.inDir then s!" {f.name}" else " _")
  let opApp (o : OpData) : String := s!"{nm "Op"}.{short o}" ++ fieldPats o true
  -- the fields of the constructor of `T` with the continuation replaced by `cont`
  let ctorArgs (o : OpData) (cont : String) : String := Id.run do
    let mut out := ""
    let mut j := 0
    for i in [:o.numFields] do
      if o.contIdx == some i then
        out := out ++ s!" {cont}"
      else
        out := out ++ s!" {o.fields[j]!.name}"
        j := j + 1
    return out
  let mut cmds := #[]
  -- the operations
  let ctors := String.join (d.ops.toList.map fun o =>
    s!"\n  /-- The operation `{o.ctor}`. -/\n  | {short o}" ++
      String.join (o.fields.toList.map fun f => s!" ({f.name} : {f.type})"))
  cmds := cmds.push (s!"/-- The operations of `{T}`, the positions of `{nm "Sig"}`. -/\n" ++
    s!"inductive {decl "Op"}{pExpl} : Type _ where{ctors}")
  -- the directions
  let dirCases := String.join (d.ops.toList.map fun o =>
    let rhs := match o.dir with
      | .empty => "PEmpty"
      | .unit => "PUnit"
      | .fn D => D
    s!"\n  | .{short o}{fieldPats o false} => {rhs}")
  cmds := cmds.push (s!"/-- The result type of an operation of `{T}`, the directions of " ++
    s!"`{nm "Sig"}`. -/\ndef {decl "Op.dir"}{pImpl} : {opTy} → {d.dirSort}{dirCases}")
  -- the signature
  cmds := cmds.push (s!"/-- The polynomial functor of the operations of `{T}`. -/\n" ++
    s!"def {decl "Sig"}{pExpl} : PFunctor := ⟨{opTy}, {nm "Op.dir"}⟩")
  -- `toFreeM`
  let toCases := String.join (d.ops.toList.map fun o =>
    let pat := s!"@{o.ctor}{pHoles} _" ++ ctorArgs o k
    let rhs := match o.dir with
      | .empty => s!".liftBind ({opApp o}) PEmpty.elim"
      | .unit => s!".liftBind ({opApp o}) fun _ => {nm "toFreeM"} {k}"
      | .fn _ => s!".liftBind ({opApp o}) fun {dv} => {nm "toFreeM"} ({k} {dv})"
    s!"\n  | {pat} => {rhs}")
  cmds := cmds.push (s!"/-- The free-monad tree over `{nm "Sig"}` of a tree of `{T}`. -/\n" ++
    s!"{mk}def {decl "toFreeM"}{pImpl}{aImpl} : {tA} → PFunctor.FreeM {sig} {a}\n" ++
    s!"  | @{d.ret}{pHoles} _ {av} => .pure {av}{toCases}")
  -- `ofFreeM`
  let ofCases := String.join (d.ops.toList.map fun o =>
    let kPat := match o.dir with
      | .empty => "_"
      | _ => k
    let cont := match o.dir with
      | .empty => ""
      | .unit => s!"({nm "ofFreeM"} ({k} PUnit.unit))"
      | .fn _ => s!"(fun {dv} => {nm "ofFreeM"} ({k} {dv}))"
    s!"\n  | .liftBind (.{short o}{fieldPats o true}) {kPat} => " ++
      s!"@{o.ctor}{pArgs} {a}{ctorArgs o cont}")
  cmds := cmds.push (s!"/-- The tree of `{T}` of a free-monad tree over `{nm "Sig"}`. -/\n" ++
    s!"{mk}def {decl "ofFreeM"}{pImpl}{aImpl} : PFunctor.FreeM {sig} {a} → {tA}\n" ++
    s!"  | .pure {av} => @{d.ret}{pArgs} {a} {av}{ofCases}")
  -- the round trips
  cmds := cmds.push (s!"/-- `{nm "ofFreeM"}` inverts `{nm "toFreeM"}`. -/\n" ++
    s!"theorem {decl "ofFreeM_toFreeM"}{pImpl}{aImpl} ({sv} : {tA}) :\n" ++
    s!"    {nm "ofFreeM"} ({nm "toFreeM"} {sv}) = {sv} := by\n" ++
    s!"  induction {sv} <;> simp only [{nm "toFreeM"}, {nm "ofFreeM"}, *]")
  let rtCases := String.join (d.ops.toList.map fun o =>
    let close := match o.dir with
      | .empty => s!"exact {dv}.elim"
      | _ => s!"exact {nm "toFreeM_ofFreeM"} ({k} {dv})"
    s!"\n  | .liftBind (.{short o}{fieldPats o true}) {k} => by\n" ++
      s!"    simp only [{nm "ofFreeM"}, {nm "toFreeM"}]; congr 1; funext {dv}; {close}")
  cmds := cmds.push (s!"/-- `{nm "toFreeM"}` inverts `{nm "ofFreeM"}`. -/\n" ++
    s!"theorem {decl "toFreeM_ofFreeM"}{pImpl}{aImpl} :\n" ++
    s!"    ({sv} : PFunctor.FreeM {sig} {a}) → {nm "toFreeM"} ({nm "ofFreeM"} {sv}) = {sv}\n" ++
    s!"  | .pure _ => rfl{rtCases}")
  cmds := cmds.push (s!"/-- `{T}` is equivalent to the free monad over `{nm "Sig"}`. -/\n" ++
    s!"{mk}def {decl "equivFreeM"}{pImpl}{aImpl} : {tA} ≃ PFunctor.FreeM {sig} {a} where\n" ++
    s!"  toFun := {nm "toFreeM"}\n  invFun := {nm "ofFreeM"}\n" ++
    s!"  left_inv := {nm "ofFreeM_toFreeM"}\n  right_inv := {nm "toFreeM_ofFreeM"}")
  -- the summands
  let tuple (o : OpData) (useAll : Bool) : String :=
    let ns := o.fields.toList.map fun f => if useAll || f.inDir then f.name.toString else "_"
    match ns with
    | [] => if useAll then "PUnit.unit" else "_"
    | [n] => n
    | _ => "⟨" ++ ", ".intercalate ns ++ "⟩"
  for o in d.ops do
    let pos := match o.fields.toList with
      | [] => s!"PUnit.\{({lA}) + 1}"
      | [f] => f.type
      | fs =>
        let init := fs.dropLast
        let last := fs.getLast!
        "Σ' " ++ " ".intercalate (init.map fun (f : OpField) => s!"({f.name} : {f.type})") ++
          s!", {last.type}"
    cmds := cmds.push (s!"/-- The summand of `{nm "Sig"}` at the operation `{o.ctor}`: " ++
      s!"positions its arguments, directions those of `{nm "Op"}.{short o}`. -/\n" ++
      s!"def {decl s!"Sig.{short o}"}{pExpl} : PFunctor :=\n" ++
      s!"  ⟨{pos}, fun {if o.fields.isEmpty then "_" else tuple o true} => " ++
      s!"@{nm "Op.dir"}{pArgs} (@{nm "Op"}.{short o}{pArgs}{fieldPats o true})⟩")
  -- the sum
  let summand (o : OpData) := s!"{nm "Sig"}.{short o}{pArgs}"
  let rec nest : List OpData → String
    | [] => "0"
    | [o] => summand o
    | o :: os => s!"({summand o} + {nest os})"
  cmds := cmds.push (
    s!"/-- The sum of the summands of `{nm "Sig"}`, one for each operation. -/\n" ++
    s!"def {decl "SigSum"}{pExpl} : PFunctor := {nest d.ops.toList}")
  -- the injection of a summand into the nested sum
  let n := d.ops.size
  let inj (i : Nat) (x : String) : String := Id.run do
    let mut s := if i + 1 == n then x else s!"Sum.inl {x}"
    for _ in [:i] do
      s := s!"Sum.inr ({s})"
    return s
  let toA := String.join ((List.range n).map fun i =>
    let o := d.ops[i]!
    s!"\n        | .{short o}{fieldPats o true} => {inj i (tuple o true)}")
  let ofA := String.join ((List.range n).map fun i =>
    let o := d.ops[i]!
    let pat := match o.fields.toList with
      | [] => "_"
      | _ => tuple o true
    s!"\n        | {inj i pat} => .{short o}{fieldPats o true}")
  let rcasesPat := " | ".intercalate (d.ops.toList.map fun o =>
    match o.fields.toList with
    | [] => "⟨⟩"
    | [f] => f.name.toString
    | fs => "⟨" ++ ", ".intercalate (fs.map (·.name.toString)) ++ "⟩")
  cmds := cmds.push (s!"/-- `{nm "Sig"}` is the sum of its summands. -/\n" ++
    s!"def {decl "sigEquivSum"}{pExpl} :\n" ++
    s!"    PFunctor.Equiv {sig} ({nm "SigSum"}{pArgs}) where\n" ++
    s!"  equivA :=\n" ++
    s!"    \{ toFun := fun{toA}\n" ++
    s!"      invFun := fun{ofA}\n" ++
    s!"      left_inv := fun {ov} => by cases {ov} <;> rfl\n" ++
    s!"      right_inv := fun {qv} => by rcases {qv} with {rcasesPat} <;> rfl }\n" ++
    s!"  equivB := fun {ov} => by cases {ov} <;> exact _root_.Equiv.refl _")
  -- bind
  if let some b := bind? then
    cmds := cmds.push (s!"/-- `{nm "toFreeM"}` carries `{b}` to `FreeM.bind`. -/\n" ++
      s!"theorem {decl "toFreeM_bind"}{pImpl}{aImpl} \{{bv} : {aTy}}\n" ++
      s!"    ({sv} : {tA}) ({fv} : {a} → {T}{pArgs} {bv}) :\n" ++
      s!"    {nm "toFreeM"} ({b} {sv} {fv}) =\n" ++
      s!"      ({nm "toFreeM"} {sv}).bind fun {av} => {nm "toFreeM"} ({fv} {av}) := by\n" ++
      s!"  induction {sv} <;> simp only [{nm "toFreeM"}, {b}, PFunctor.FreeM.bind, *] <;>\n" ++
      s!"    (congr 1; funext {dv}; first | exact {dv}.elim | (rename_i ih; exact ih {dv}))")
  return cmds

/-- The source of the code declarations of `derive_free_sig T (code := true)` in the namespace
`N`: the code `N.code` of the signature, the equivalence `N.sigEquivCode` of `N.Sig` with the
interpretation of the code, and `N.equivCode`. The fields of the code lie in the universe
`lA` and its directions in `lB`, the universes of `N.Sig`. -/
def codeSource (d : SigData) (N : Name) (lA lB : String) : Array String := Id.run do
  let ov := d.freshNames[4]!.toString
  let qv := d.freshNames[5]!.toString
  let T := d.T.toString
  let mk := if d.isMeta then "noncomputable " else ""
  let nm (s : String) := s!"{N}.{s}"
  let lv := if d.lvls.isEmpty then "" else ".{" ++ ", ".intercalate (d.lvls.map toString) ++ "}"
  let decl (s : String) := s!"_root_.{nm s}{lv}"
  let pExpl := String.join (d.params.toList.map fun (n, t) => s!" ({n} : {t})")
  let pImpl := String.join (d.params.toList.map fun (n, t) => s!" \{{n} : {t}}")
  let pArgs := String.join (d.params.toList.map fun (n, _) => s!" {n}")
  let (a, aTy) := d.alpha
  let short (o : OpData) := o.short.toString
  let interp := s!"(PFunctor.Code.interp ({nm "code"}{pArgs}))"
  -- the code of an operation: one `field` for each field, then the direction
  let opCode (o : OpData) : String :=
    let dir := match o.dir with
      | .empty => "PEmpty"
      | .unit => "PUnit"
      | .fn D => s!"({D})"
    o.fields.foldr (init := s!".dir {dir}") fun f rest =>
      let ty := if f.isProp then s!"(PLift ({f.type}))" else s!"({f.type})"
      let down := if f.isProp then "down.down" else "down"
      if f.used then
        s!".field (ULift.\{{lA}} {ty}) fun {f.name} => let {f.name} := {f.name}.{down};\n    {rest}"
      else s!".field (ULift.\{{lA}} {ty}) fun _ =>\n    {rest}"
  let ops := ",\n  ".intercalate (d.ops.toList.map opCode)
  let mut cmds := #[]
  cmds := cmds.push (s!"/-- The code of the signature of `{T}`. -/\n" ++
    s!"def {decl "code"}{pExpl} : PFunctor.Code.\{{lA}, {lB}} := ⟨[\n  {ops}]⟩")
  -- the position of the code at an operation, as a term and as patterns
  let posTerm (o : OpData) : String :=
    o.fields.foldr (init := "PUnit.unit") fun f rest =>
      let x := if f.isProp then s!"(PLift.up {f.name})" else f.name.toString
      s!"(Sigma.mk (ULift.up {x}) {rest})"
  let posPat (o : OpData) (last : String) : String :=
    let fs := o.fields.toList.map fun f =>
      if f.isProp then s!"⟨⟨{f.name}⟩⟩" else s!"⟨{f.name}⟩"
    match fs with
    | [] => last
    | _ => "⟨" ++ ", ".intercalate (fs ++ [last]) ++ "⟩"
  let n := d.ops.size
  let inj (i : Nat) (x : String) : String := Id.run do
    let mut s := if i + 1 == n then x else s!"Sum.inl {x}"
    for _ in [:i] do
      s := s!"Sum.inr ({s})"
    return s
  let fieldArgs (o : OpData) := String.join (o.fields.toList.map fun f => s!" {f.name}")
  let toA := String.join ((List.range n).map fun i =>
    let o := d.ops[i]!
    s!"\n        | .{short o}{fieldArgs o} => {inj i (posTerm o)}")
  let ofA := String.join ((List.range n).map fun i =>
    let o := d.ops[i]!
    s!"\n        | {inj i (posPat o "_")} => .{short o}{fieldArgs o}")
  let rcasesPat := " | ".intercalate (d.ops.toList.map fun o => posPat o "⟨⟩")
  cmds := cmds.push (s!"/-- `{nm "Sig"}` is the interpretation of the code `{nm "code"}`. -/\n" ++
    s!"def {decl "sigEquivCode"}{pExpl} :\n" ++
    s!"    PFunctor.Equiv ({nm "Sig"}{pArgs}) {interp} where\n" ++
    s!"  equivA :=\n" ++
    s!"    \{ toFun := fun{toA}\n" ++
    s!"      invFun := fun{ofA}\n" ++
    s!"      left_inv := fun {ov} => by cases {ov} <;> rfl\n" ++
    s!"      right_inv := fun {qv} => by rcases {qv} with {rcasesPat} <;> rfl }\n" ++
    s!"  equivB := fun {ov} => by cases {ov} <;> exact _root_.Equiv.refl _")
  cmds := cmds.push (s!"/-- `{T}` is equivalent to the free monad over the interpretation of " ++
    s!"`{nm "code"}`. -/\n" ++
    s!"{mk}def {decl "equivCode"}{pImpl} \{{a} : {aTy}} :\n" ++
    s!"    {T}{pArgs} {a} ≃ PFunctor.FreeM {interp} {a} :=\n" ++
    s!"  {nm "equivFreeM"}.trans\n" ++
    s!"    (PFunctor.freeMCongr " ++
    s!"(PFunctor.Equiv.toLensEquiv ({nm "sigEquivCode"}{pArgs})))")
  return cmds

/-- `stx` with every source position replaced by the synthetic position of `ref`. -/
partial def withRefInfo (info : SourceInfo) : Syntax → Syntax
  | .node _ kind args => .node info kind (args.map (withRefInfo info))
  | .atom _ v => .atom info v
  | .ident _ raw v pre => .ident info raw v pre
  | .missing => .missing

/-- Elaborate the printed command `text` at the position of `ref`. -/
def elabText (ref : Syntax) (text : String) : CommandElabM Unit := do
  let stx ← match Parser.runParserCategory (← getEnv) `command text with
    | .ok stx => pure stx
    | .error e => throwError "derive_free_sig: the generated source does not parse: {e}\n{text}"
  elabCommand (withRefInfo (SourceInfo.fromRef ref) stx)

/-- An option of `derive_free_sig`: `(namespace := N)`, `(bind := f)` or `(code := true)`. -/
syntax deriveFreeSigOpt := " (" ("namespace" <|> &"bind" <|> &"code") " := " ident ")"

/-- `derive_free_sig T (namespace := N) (bind := f)` defines the operations `N.Op`, the
polynomial functor `N.Sig`, the equivalence `N.equivFreeM` between `T` and the free monad over
`N.Sig`, and the decomposition `N.sigEquivSum` of `N.Sig` as a sum of one-operation summands;
see the module documentation. `derive_free_sig?` also prints the generated source. The
options are each optional and may be given in any order. -/
syntax (name := deriveFreeSigCmd) ("derive_free_sig " <|> "derive_free_sig? ") ident
  deriveFreeSigOpt* : command

/-- Elaborate `derive_free_sig T` and its options: generate the source of the signature, the
equivalences and, with `(code := true)`, the code of `T`, and elaborate it. -/
@[command_elab deriveFreeSigCmd]
def elabDeriveFreeSig : CommandElab := fun stx => do
  let show? := stx[0].getAtomVal.contains '?'
  let T ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ns ← getCurrNamespace
  let mut N := T
  let mut bind? : Option Name := none
  let mut code := false
  -- the options, each at most once, in any order
  let mut seen : Array String := #[]
  for opt in stx[2].getArgs do
    -- the key is the atom after the opening parenthesis and the value the identifier, read off
    -- the atoms and identifiers of the option in order, whatever nodes wrap them
    let mut atoms : Array String := #[]
    let mut val? : Option Syntax := none
    for s in opt.topDown do
      if s.isAtom then
        atoms := atoms.push s.getAtomVal.trimAscii.toString
      else if s.isIdent && val?.isNone then
        val? := some s
    let key := (atoms.filter (fun a => a != "(" && a != ":=" && a != ")"))[0]?.getD ""
    let some val := val?
      | throwErrorAt opt "derive_free_sig: the option has no value"
    if seen.contains key then
      throwErrorAt opt "derive_free_sig: the option `{key}` is given twice"
    seen := seen.push key
    match key with
    | "namespace" => N := ns ++ val.getId
    | "bind" => bind? := some (← liftCoreM (realizeGlobalConstNoOverloadWithInfo val))
    | "code" =>
      unless val.getId == `true || val.getId == `false do
        throwErrorAt val "derive_free_sig: the option `code` takes `true` or `false`"
      code := val.getId == `true
    | _ => throwErrorAt opt "derive_free_sig: unknown option `{key}`"
  let d ← liftTermElabM do readSig (← toIndDesc T)
  -- `N.Op`, `N.Op.dir` and `N.Sig` first: the later declarations use the universes of `N.Sig`
  for c in (sigSource d N bind? "0").extract 0 sigHeadSize do
    elabText stx c
  let sigTy := (← getConstInfo (N ++ `Sig)).type
  let lvls ← liftTermElabM <| forallTelescope sigTy fun _ body => do
    let .const ``PFunctor [lA, lB] := body
      | throwError "derive_free_sig: `{N ++ `Sig}` is not a `PFunctor`"
    return (toString (format lA), toString (format lB))
  let cmds := sigSource d N bind? lvls.1
  for c in cmds.extract sigHeadSize cmds.size do
    elabText stx c
  let mut shown := cmds
  if code then
    -- the universes of the fields and of the directions are those of `N.Sig`
    let ccmds := codeSource d N lvls.1 lvls.2
    for c in ccmds do
      elabText stx c
    shown := shown ++ ccmds
  if show? then logInfo m!"{"\n\n".intercalate shown.toList}"

end PFunctor.DeriveFreeSig

end

end
