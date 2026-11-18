/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import Lean.Data.Json.Basic
public meta import Lean.Exception

/-!
# Located errors and a JSON decoder

A frontend of the import machinery reads an external file in two passes: it decodes the JSON into
a mirror of the source, and it elaborates each declaration of the mirror. Both passes report an
error at a `Location`: what the path starts from, such as a file or a declaration, and the path
from there to the offending value, outermost first. A `Located` error renders as
`origin at a/b/c: message`.

`JsonM σ` decodes with a state `σ`, such as a table of names, and fails with a `Located` error.
`JsonM.inside` adds a segment to the path of every failure below it, and the combinators add their
own: `field` its key, `elems` and `pair` the position `[i]` of each element. `variant` reads a
constructor written as a string, without an argument, or as an object with one field, whose value
is the argument; `unknown` refuses a constructor that a decoder does not know, or one with an
argument it does not take. `checkHeader` checks the format and version that an input declares and
reads its provenance fields, which an import records in its manifest (`Import.Registry`).
`JsonM.decode` runs a decoder on an input and throws a failure with the input as its origin.

An elaborator keeps a `Location` as it descends into a declaration (`Location.into`) and fails at
it (`Location.fail`), so that its errors point into the source as the decoder's do;
`Location.check` places the error of a translation step there.
-/

public meta section

namespace IPFunctor.Import

open Lean

/-- A place in an import's input: what the path starts from, such as a file or a declaration, and
the path from there, outermost first. -/
structure Location where
  /-- What the path starts from; empty when the context gives it. -/
  origin : String := ""
  /-- The path, outermost first. -/
  path : Array String := #[]
  deriving Inhabited

/-- The location one segment further down. -/
def Location.into (l : Location) (seg : String) : Location :=
  { l with path := l.path.push seg }

/-- `origin at a/b/c`, without the parts that are empty. -/
instance : ToString Location where
  toString l :=
    let path := "/".intercalate l.path.toList
    if l.origin.isEmpty then path
    else if path.isEmpty then l.origin
    else s!"{l.origin} at {path}"

/-- An error at a location in an import's input. -/
structure Located where
  /-- Where the error is. -/
  location : Location := {}
  /-- What is wrong. -/
  message : String
  deriving Inhabited

/-- `location: message`, or the message alone at an empty location. -/
instance : ToString Located where
  toString e :=
    let l := toString e.location
    if l.isEmpty then e.message else s!"{l}: {e.message}"

/-- The error with `seg` in front of its path. -/
def Located.within (seg : String) (e : Located) : Located :=
  { e with location.path := #[seg] ++ e.location.path }

/-- Throw a located error as an error message. -/
def Located.throw {m : Type → Type} [Monad m] [MonadError m] {α : Type} (e : Located) : m α :=
  throwError (toString e)

/-- Fail at a location. -/
def Location.fail {m : Type → Type} [Monad m] [MonadError m] {α : Type} (l : Location)
    (msg : String) : m α :=
  Located.throw { location := l, message := msg }

/-- The result of `x`, or a failure at the location with its message. -/
def Location.check {m : Type → Type} [Monad m] [MonadError m] {α : Type} (l : Location)
    (x : Except String α) : m α :=
  match x with
  | .ok a => pure a
  | .error msg => l.fail msg

/-- A JSON decoder with state `σ`, whose failures are located errors. -/
abbrev JsonM (σ : Type) := StateT σ (Except Located)

namespace JsonM

variable {σ α β : Type}

/-- Fail with a message, at the path of the enclosing `inside` blocks. -/
def fail (msg : String) : JsonM σ α :=
  throw ({ message := msg } : Located)

/-- Run `x`, adding `seg` in front of the path of any failure. -/
def inside (seg : String) (x : JsonM σ α) : JsonM σ α := fun s =>
  match x s with
  | .error e => .error (e.within seg)
  | .ok r => .ok r

/-- An array. -/
def arr (j : Json) : JsonM σ (Array Json) :=
  match j with
  | .arr xs => pure xs
  | _ => fail "expected an array"

/-- A string. -/
def str (j : Json) : JsonM σ String :=
  match j with
  | .str s => pure s
  | _ => fail "expected a string"

/-- A natural number. -/
def nat (j : Json) : JsonM σ Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => fail "expected a natural number"

/-- A Boolean. -/
def bool (j : Json) : JsonM σ Bool :=
  match j with
  | .bool b => pure b
  | _ => fail "expected a Boolean"

/-- The field `key` of an object, decoded by `f` inside `key`. -/
def field (j : Json) (key : String) (f : Json → JsonM σ α) : JsonM σ α := do
  let .obj _ := j | fail s!"expected an object with the field `{key}`"
  let .ok v := j.getObjVal? key | fail s!"missing field `{key}`"
  inside key (f v)

/-- The field `key` of an object, decoded by `f` inside `key`, or `none` when the object lacks it
or it is `null`. -/
def optField (j : Json) (key : String) (f : Json → JsonM σ α) : JsonM σ (Option α) := do
  let .obj _ := j | fail s!"expected an object"
  match j.getObjVal? key with
  | .ok .null | .error _ => return none
  | .ok v => some <$> inside key (f v)

/-- Decode each element of an array, inside its position `[i]`. -/
def elems (j : Json) (f : Json → JsonM σ α) : JsonM σ (Array α) := do
  (← arr j).mapIdxM fun i x => inside s!"[{i}]" (f x)

/-- An array of two elements, decoded by `f` and `g` inside `[0]` and `[1]`. -/
def pair (j : Json) (f : Json → JsonM σ α) (g : Json → JsonM σ β) : JsonM σ (α × β) := do
  let #[a, b] ← arr j | fail "expected an array of two elements"
  return (← inside "[0]" (f a), ← inside "[1]" (g b))

/-- A constructor written as a string `t`, without an argument, or as an object `{t: v}` with one
field, whose value `v` is the argument. -/
def variant (j : Json) : JsonM σ (String × Option Json) :=
  match j with
  | .str t => pure (t, none)
  | .obj kvs =>
    match kvs.toList with
    | [(t, v)] => pure (t, some v)
    | _ => fail "expected an object with one field"
  | _ => fail "expected a string or an object with one field"

/-- Refuse a constructor, as `variant` reads it, that the decoder of `what`, such as `type`, does
not know with an argument, or without one. -/
def unknown (what : String) : String × Option Json → JsonM σ α
  | (t, none) => fail s!"unknown {what} `{t}` without an argument"
  | (t, some _) => fail s!"unknown {what} `{t}` with an argument"

/-- Check that an input declares the format `format` at version `version`, in its fields `format`
and `version`, and read its provenance `fields`, each a string, as pairs of field and value. -/
def checkHeader (j : Json) (format : String) (version : Nat) (fields : Array String) :
    JsonM σ (Array (String × String)) := do
  let f ← field j "format" str
  unless f == format do fail s!"format {f}, where this importer reads {format}"
  let v ← field j "version" nat
  unless v == version do
    fail s!"{format} version {v}, where this importer reads version {version}"
  fields.mapM fun key => return (key, ← field j key str)

/-- Run `x` from the state `s` on the input named `origin`. A failure is thrown as an error whose
location starts from `origin`, unless it names an origin already. -/
def decode {m : Type → Type} [Monad m] [MonadError m] (x : JsonM σ α) (s : σ) (origin : String) :
    m (α × σ) :=
  match x.run s with
  | .ok r => pure r
  | .error e =>
    if e.location.origin.isEmpty then Located.throw { e with location.origin := origin }
    else Located.throw e

end JsonM

end IPFunctor.Import
