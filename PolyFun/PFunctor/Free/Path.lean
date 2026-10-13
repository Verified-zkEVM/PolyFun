/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Displayed

/-!
# Branch paths and telescopes for `PFunctor.FreeM`

This file contains the path-dependent structure that lives on top of the
basic free monad on a polynomial functor.

For a polynomial/container `P`, `PFunctor.FreeM P α` is the inductive type of
well-founded `P`-branching trees with leaves labelled by `α`. The definitions
below isolate the branch-object pattern of such a tree:

* `FreeM.Path s` records an explicit polynomial direction at every node.
* `FreeM.PathAlong l s` is the canonical path through `s.mapLens l`, i.e. the
  runtime branch through a control tree executed along a polynomial lens.
* `FreeM.output s path` recovers the leaf payload selected by that path.
* `FreeM.append s k` grafts a suffix tree selected by the canonical path of `s`.
* `FreeM.StoppingTree` is the state-indexed initial algebra whose next state is
  selected by an abstract observation.
* `FreeM.Telescope` is the specialization where observations are canonical
  branch paths.

## Equation conventions

Each recursive definition below comes with its two constructor equations. The `_pure` equation is
tagged `@[simp]`. The `_liftBind` equation states the constructor spelling `FreeM.liftBind a rest`
produced by pattern matching and `induction`, and is deliberately not `@[simp]`: `simp` first
rewrites a node to its normal form `(FreeM.lift a).bind rest` via `FreeM.liftBind_eq`, so such a
left-hand side would never match. Use the `_liftBind` equations with `rw`.

The `head_mk` and `tail_mk` lemmas carry `no_index` on their path argument, because its hidden
sigma type reduces once the polynomial is concrete and `simp` must not key on the reduced form.

## Terminology and references

The same object appears under several names in the literature. In polynomial
functor language, the free monad on a polynomial is a type of terminating
decision trees. In container and W-type language, these are well-founded trees
and `Path` is the type of paths through such a tree. In dependent-type
presentations of games, these are dependent type trees and paths. In
programming language semantics, the coinductive analogue is an interaction
tree.

Relevant references include:

* Hancock and Setzer, *Interactive Programs in Dependent Type Theory*, for
  dependent I/O-trees over command-response worlds.
* Altenkirch, Ghani, Hancock, McBride, and Morris, *Indexed Containers*, for
  containers, indexed containers, and interaction structures.
* Libkind and Spivak, *Pattern runs on matter*, for free polynomial monads as
  terminating decision trees.
* Escardo and Oliva, *Higher-order games with dependent types*, for dependent
  type trees and paths in history-dependent games.
* Xia, Zakowski, He, Hur, Malecha, Pierce, and Zdancewic, *Interaction Trees*,
  for the coinductive programming-language analogue.
-/

@[expose] public section

universe v w z t uA uB uA₂ uB₂

namespace PFunctor
namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-! ## Canonical paths -/

variable {Q : PFunctor.{uA₂, uB₂}}

/-- Displayed algebra for canonical root-to-leaf paths: a leaf carries the trivial fiber
`PUnit`, and a node at `a : P.A` carries the dependent sum, over directions `b : P.B a`, of the
fiber chosen for the child `b`. `Path` is its evaluation; `PathAlong.algebra` is the variant
whose node directions come from a runtime polynomial along a lens. -/
@[implicit_reducible]
def Path.algebra (P : PFunctor.{uA, uB}) (α : Type v) :
    Displayed.Algebra.{uA, uB, v, uB+1} P α where
  leaf := fun _ => PUnit.{uB+1}
  node := fun a child => (b : P.B a) × child b

/-- The canonical root-to-leaf path through a `FreeM` tree. A path through `pure x` is trivial
(`PUnit`); a path through `(FreeM.lift a).bind rest` is a direction `b : P.B a` together with a
path through `rest b`. Prefer `Path.cons`, `Path.head` and `Path.tail` for node paths: they keep
statements independent of how `Displayed` unfolds. `PathAlong l s` is the runtime variant whose
node directions come from the target polynomial of the lens `l`. -/
abbrev Path {α : Type v} : FreeM P α → Type uB :=
  Displayed (Path.algebra P α)

namespace Path

/-! ### The node interface

A path through an operation node is a direction together with a path through the selected
child. `cons`, `head` and `tail` are the public interface to that structure; statements and
lemmas go through them rather than through the anonymous constructor and projections of the
underlying sigma type, so nothing outside this file depends on how `Displayed` unfolds. The
node is written in its simp normal form `(FreeM.lift a).bind rest`; the constructor spelling
`FreeM.liftBind a rest` produced by pattern matching is the same tree. -/

/-- Prepend one operation-node direction to a path through the selected child. -/
def cons (a : P.A) (rest : P.B a → FreeM P α) (b : P.B a) (path : Path (rest b)) :
    Path ((FreeM.lift a).bind rest) :=
  ⟨b, path⟩

/-- The direction selected at the root of a non-leaf path. -/
def head (a : P.A) (rest : P.B a → FreeM P α) (path : Path ((FreeM.lift a).bind rest)) : P.B a :=
  path.1

/-- The path remaining below the root direction of a non-leaf path. -/
def tail (a : P.A) (rest : P.B a → FreeM P α) (path : Path ((FreeM.lift a).bind rest)) :
    Path (rest (head a rest path)) :=
  path.2

/-- `head` computes on `cons`. For a node path written with the anonymous constructor after
pattern matching, `simp` uses `head_mk` instead. -/
@[simp]
theorem head_cons (a : P.A) (rest : P.B a → FreeM P α) (b : P.B a) (path : Path (rest b)) :
    head a rest (cons a rest b path) = b := rfl

/-- `tail` computes on `cons`. For a node path written with the anonymous constructor after
pattern matching, `simp` uses `tail_mk` instead. -/
@[simp]
theorem tail_cons (a : P.A) (rest : P.B a → FreeM P α) (b : P.B a) (path : Path (rest b)) :
    tail a rest (cons a rest b path) = path := rfl

/-- Eta law for node paths: `simp` folds a path rebuilt from its own `head` and `tail` back into
the original path. It is `Sigma.eta` seen through the node interface, so it holds by `rfl`. -/
@[simp]
theorem cons_head_tail (a : P.A) (rest : P.B a → FreeM P α)
    (path : Path ((FreeM.lift a).bind rest)) :
    cons a rest (head a rest path) (tail a rest path) = path := rfl

/-- `head` on a path destructured by pattern matching. -/
@[simp]
theorem head_mk (a : P.A) (rest : P.B a → FreeM P α) (b : P.B a) (path : Path (rest b)) :
    head a rest (no_index (⟨b, path⟩ : Path (FreeM.liftBind a rest))) = b := rfl

/-- `tail` on a path destructured by pattern matching. -/
@[simp]
theorem tail_mk (a : P.A) (rest : P.B a → FreeM P α) (b : P.B a) (path : Path (rest b)) :
    tail a rest (no_index (⟨b, path⟩ : Path (FreeM.liftBind a rest))) = path := rfl

/-- Two paths through a node agree once their directions and tails agree. The tail hypothesis is
heterogeneous because the tails live over the two heads; when the heads are already syntactically
equal, supply it with `heq_of_eq`. This is `Sigma.ext` seen through the node interface; it is
deliberately not an `@[ext]` lemma, since `Path` is an abbreviation of `Displayed`. -/
theorem ext {a : P.A} {rest : P.B a → FreeM P α} {path path' : Path ((FreeM.lift a).bind rest)}
    (hhead : head a rest path = head a rest path')
    (htail : HEq (tail a rest path) (tail a rest path')) : path = path' :=
  Sigma.ext hhead htail

end Path

/-! ## Runtime paths along a lens -/

/-- Displayed algebra for runtime paths along a lens `l : Lens P Q`: a leaf carries the trivial
fiber `PUnit`, and a node at `a : P.A` carries the dependent sum, over runtime directions
`d : Q.B (l.toFunA a)` of the target polynomial, of the fiber chosen for the source branch
`l.toFunB a d` that `d` selects. `PathAlong` is its evaluation; `Path.algebra` is the variant whose
node directions are the source directions `P.B a` themselves. -/
@[implicit_reducible]
def PathAlong.algebra (l : Lens P Q) : Displayed.Algebra.{uA, uB, v, uB₂+1} P α where
  leaf := fun _ => PUnit.{uB₂+1}
  node := fun a child => (d : Q.B (l.toFunA a)) × child (l.toFunB a d)

/-- Runtime path through a `P`-tree `s` executed along a lens `l : Lens P Q`. A path through
`pure x` is trivial (`PUnit`); a path through `(FreeM.lift a).bind rest` is a runtime direction
`d : Q.B (l.toFunA a)` together with a path through the source branch `rest (l.toFunB a d)` that `d`
selects. Prefer `PathAlong.cons`, `PathAlong.head` and `PathAlong.tail` for node paths. It is
`Path (s.mapLens l)` up to `pathAlongToMapLensPath`; `projectPathAlong` forgets it to `Path s`. -/
abbrev PathAlong (l : Lens P Q) (s : FreeM P α) : Type uB₂ :=
  Displayed (PathAlong.algebra l) s

namespace PathAlong

/-! ### The node interface

The runtime analogue of `Path.cons` / `Path.head` / `Path.tail`: a runtime path through an
operation node is a runtime direction together with a runtime path through the source branch it
selects. -/

/-- Prepend one runtime direction to a runtime path through the branch it selects. -/
def cons (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) (d : Q.B (l.toFunA a))
    (path : PathAlong l (rest (l.toFunB a d))) : PathAlong l ((FreeM.lift a).bind rest) :=
  ⟨d, path⟩

/-- The runtime direction selected at the root of a non-leaf runtime path. -/
def head (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (path : PathAlong l ((FreeM.lift a).bind rest)) : Q.B (l.toFunA a) :=
  path.1

/-- The runtime path remaining below the root direction of a non-leaf runtime path. -/
def tail (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (path : PathAlong l ((FreeM.lift a).bind rest)) :
    PathAlong l (rest (l.toFunB a (head l a rest path))) :=
  path.2

/-- `head` computes on `cons`. For a runtime node path written with the anonymous constructor
after pattern matching, `simp` uses `head_mk` instead. -/
@[simp]
theorem head_cons (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) (d : Q.B (l.toFunA a))
    (path : PathAlong l (rest (l.toFunB a d))) : head l a rest (cons l a rest d path) = d := rfl

/-- `tail` computes on `cons`. For a runtime node path written with the anonymous constructor
after pattern matching, `simp` uses `tail_mk` instead. -/
@[simp]
theorem tail_cons (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) (d : Q.B (l.toFunA a))
    (path : PathAlong l (rest (l.toFunB a d))) : tail l a rest (cons l a rest d path) = path := rfl

/-- Eta law for runtime node paths: `simp` folds a runtime path rebuilt from its own `head` and
`tail` back into the original path. Like `Path.cons_head_tail`, it is `Sigma.eta` seen through the
node interface, so it holds by `rfl`. -/
@[simp]
theorem cons_head_tail (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (path : PathAlong l ((FreeM.lift a).bind rest)) :
    cons l a rest (head l a rest path) (tail l a rest path) = path := rfl

/-- `head` on a runtime path destructured by pattern matching. -/
@[simp]
theorem head_mk (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) (d : Q.B (l.toFunA a))
    (path : PathAlong l (rest (l.toFunB a d))) :
    head l a rest (no_index (⟨d, path⟩ : PathAlong l (FreeM.liftBind a rest))) = d := rfl

/-- `tail` on a runtime path destructured by pattern matching. -/
@[simp]
theorem tail_mk (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) (d : Q.B (l.toFunA a))
    (path : PathAlong l (rest (l.toFunB a d))) :
    tail l a rest (no_index (⟨d, path⟩ : PathAlong l (FreeM.liftBind a rest))) = path := rfl

end PathAlong

/-- The leaf payload selected by a path. The path records only branch choices, but together with
the tree it determines the terminal `pure` payload. `output_pure` and `output_liftBind` are its
equations; `outputAlong` is the variant for runtime paths along a lens. -/
def output : (s : FreeM P α) → Path s → α
  | .pure x, _ => x
  | .liftBind _ rest, ⟨b, path⟩ => output (rest b) path

/-- The path through a free tree that follows a fixed direction selector `choose` at every
operation node. The selector is operation-dependent but never inspects the continuation below
the selected direction; `ofHandler_pure` and `ofHandler_liftBind` are its equations. -/
def Path.ofHandler (choose : (a : P.A) → P.B a) : (tree : FreeM P α) → Path tree
  | .pure _ => ⟨⟩
  | .liftBind operation next => ⟨choose operation, ofHandler choose (next (choose operation))⟩

/-- `Path.ofHandler` at a leaf. A leaf has no operation node, so `choose` is never consulted and
the result is the unique trivial path `⟨⟩` through `pure value`. -/
@[simp]
theorem Path.ofHandler_pure (choose : (a : P.A) → P.B a) (value : α) :
    Path.ofHandler choose (pure value : FreeM P α) = ⟨⟩ := rfl

/-- `Path.ofHandler` at an operation node: the handler picks `choose operation` and the path
continues below it through the selected child. -/
theorem Path.ofHandler_liftBind (choose : (a : P.A) → P.B a) (operation : P.A)
    (next : P.B operation → FreeM P α) :
    Path.ofHandler choose (FreeM.liftBind operation next) =
      ⟨choose operation, Path.ofHandler choose (next (choose operation))⟩ := rfl

/-- The leaf at the end of a free tree over the identity polynomial `y`: every node has exactly one
child, so the tree is a chain and reading its leaf needs no choices. `collapseUnit_pure` and
`collapseUnit_liftBind` are its equations; `FreeP.collapseUnit` is the lens form of the collapse. -/
def collapseUnit (tree : FreeM y.{uA, uB} α) : α :=
  output tree (Path.ofHandler (fun _ => PUnit.unit) tree)

/-- `collapseUnit` at a leaf: a chain with no nodes yields its payload. This is `output_pure` after
`Path.ofHandler_pure`, so it holds by `rfl`; `collapseUnit_liftBind` is the step through a node. -/
@[simp]
theorem collapseUnit_pure (value : α) :
    collapseUnit (pure value : FreeM y.{uA, uB} α) = value := rfl

/-- `collapseUnit` through a node of a chain: the sole direction is taken and the collapse
continues in the child. -/
theorem collapseUnit_liftBind (next : PUnit.{uB + 1} → FreeM y.{uA, uB} α) :
    collapseUnit (FreeM.liftBind (P := y.{uA, uB}) PUnit.unit next) =
      collapseUnit (next PUnit.unit) := rfl

/-- The leaf payload selected by a runtime path along a lens: at each node the runtime direction
`d` selects the source branch `l.toFunB a d`. `outputAlong_pure` and `outputAlong_liftBind` are its
equations; `output_projectPathAlong` identifies it with `output` on the projected control path. -/
def outputAlong (l : Lens P Q) : (s : FreeM P α) → PathAlong l s → α
  | .pure x, _ => x
  | .liftBind a rest, ⟨d, path⟩ => outputAlong l (rest (l.toFunB a d)) path

/-- `outputAlong` at a leaf: a runtime path through `pure x` makes no choices, so the payload is
`x` whatever `path` is. `outputAlong_liftBind` is the step through a node. -/
@[simp]
theorem outputAlong_pure (l : Lens P Q) (x : α) (path : PathAlong l (FreeM.pure x : FreeM P α)) :
    outputAlong l (pure x) path = x := rfl

/-- `outputAlong` through a node: the runtime direction `PathAlong.head` selects the source branch
and evaluation continues there along `PathAlong.tail`. -/
theorem outputAlong_liftBind (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (path : PathAlong l ((FreeM.lift a).bind rest)) :
    outputAlong l (FreeM.liftBind a rest) path =
      outputAlong l (rest (l.toFunB a (PathAlong.head l a rest path)))
        (PathAlong.tail l a rest path) := rfl

/-- `output` at a leaf: a path through `pure x` makes no choices, so the payload is `x` whatever
`path` is. `output_liftBind` is the step through a node. -/
@[simp]
theorem output_pure (x : α) (path : Path (FreeM.pure (P := P) x)) : output (pure x) path = x := rfl

/-- `output` through a node: the direction `Path.head` selects the child and evaluation continues
there along `Path.tail`. `outputAlong_liftBind` is the runtime variant along a lens. -/
theorem output_liftBind (a : P.A) (rest : P.B a → FreeM P α)
    (path : Path ((FreeM.lift a).bind rest)) :
    output (FreeM.liftBind a rest) path =
      output (rest (Path.head a rest path)) (Path.tail a rest path) := rfl

/-- Constructor-local projection from runtime paths along a lens `l` to control paths: a leaf
maps to the trivial path, and at a node the runtime direction `d` maps to the source direction
`l.toFunB a d` it selects. `projectPathAlong` is its `toHom` evaluation over whole trees. -/
def projectPathAlongLocalMap (l : Lens P Q) :
    Displayed.LocalMap (PathAlong.algebra (α := α) l) (Path.algebra P α) where
  mapLeaf := fun _ _ => ⟨⟩
  mapNode := fun a _ _ mapChild path => ⟨l.toFunB a path.1, mapChild (l.toFunB a path.1) path.2⟩

/-- Project a runtime path along a lens `l` back to the canonical branch path of the control tree:
at each node the runtime direction `d` becomes the source direction `l.toFunB a d` it selects.
`projectPathAlong_pure` and `projectPathAlong_liftBind` are its equations, and
`output_projectPathAlong` shows it preserves the selected payload. -/
def projectPathAlong (l : Lens P Q) : (s : FreeM P α) → PathAlong l s → Path s :=
  (projectPathAlongLocalMap l).toHom

/-- `projectPathAlong` at a leaf: `Path (pure x)` is the trivial fiber `PUnit`, so every runtime
path through a leaf projects to `⟨⟩`. `projectPathAlong_liftBind` is the step through a node. -/
@[simp]
theorem projectPathAlong_pure (l : Lens P Q) (x : α)
    (path : PathAlong l (FreeM.pure x : FreeM P α)) : projectPathAlong l (pure x) path = ⟨⟩ := rfl

/-- `projectPathAlong` through a node: the runtime direction `PathAlong.head` is pulled back
through `l.toFunB a` to a source direction and the projection continues along `PathAlong.tail`. -/
theorem projectPathAlong_liftBind (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (path : PathAlong l ((FreeM.lift a).bind rest)) :
    projectPathAlong l (FreeM.liftBind a rest) path =
      Path.cons a rest (l.toFunB a (PathAlong.head l a rest path))
        (projectPathAlong l (rest (l.toFunB a (PathAlong.head l a rest path)))
          (PathAlong.tail l a rest path)) := rfl

/-- `projectPathAlong` preserves the selected leaf: reading the control payload along the projected
path is reading the runtime payload along the original path. `simp` uses it to rewrite `output` of a
projected path to `outputAlong`; `output_mapLens_pathAlongToMapLensPath` is the variant through the
lens-mapped tree. -/
@[simp]
theorem output_projectPathAlong (l : Lens P Q) :
    (s : FreeM P α) → (path : PathAlong l s) →
      output s (projectPathAlong l s path) = outputAlong l s path
  | .pure _, _ => rfl
  | .liftBind a rest, ⟨d, path⟩ => output_projectPathAlong l (rest (l.toFunB a d)) path

/-! ## Runtime paths and lens-mapped trees -/

/-- View a runtime path through `s` along `l` as the canonical path through the lens-mapped
runtime tree `s.mapLens l`. Both types have the same constructor shape, but `PathAlong` lives over
the source tree while `Path (s.mapLens l)` lives over the lens-mapped tree. Its equations are
`pathAlongToMapLensPath_pure` and `pathAlongToMapLensPath_liftBind`; `mapLensPathToPathAlong` is
its inverse by `mapLensPathToPathAlong_toMapLensPath` and `pathAlongToMapLensPath_toPathAlong`. -/
def pathAlongToMapLensPath (l : Lens P Q) : (s : FreeM P α) → PathAlong l s → Path (s.mapLens l)
  | .pure _, _ => ⟨⟩
  | .liftBind a rest, ⟨d, path⟩ => ⟨d, pathAlongToMapLensPath l (rest (l.toFunB a d)) path⟩

/-- `pathAlongToMapLensPath` at a leaf: `Path ((pure x).mapLens l)` reduces to `Path (pure x)`, the
trivial fiber `PUnit`, so every runtime path through a leaf maps to `⟨⟩`.
`pathAlongToMapLensPath_liftBind` is the step through a node. -/
@[simp]
theorem pathAlongToMapLensPath_pure (l : Lens P Q) (x : α)
    (path : PathAlong l (FreeM.pure x : FreeM P α)) :
    pathAlongToMapLensPath l (pure x) path = ⟨⟩ := rfl

/-- `pathAlongToMapLensPath` through a node: the runtime direction `PathAlong.head` becomes the
direction at the mapped node `l.toFunA a` and the view continues along `PathAlong.tail`. -/
theorem pathAlongToMapLensPath_liftBind (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (path : PathAlong l ((FreeM.lift a).bind rest)) :
    pathAlongToMapLensPath l (FreeM.liftBind a rest) path =
      Path.cons (l.toFunA a) (fun d => (rest (l.toFunB a d)).mapLens l)
        (PathAlong.head l a rest path)
        (pathAlongToMapLensPath l (rest (l.toFunB a (PathAlong.head l a rest path)))
          (PathAlong.tail l a rest path)) := rfl

/-- View a canonical path through the lens-mapped runtime tree `s.mapLens l` as a runtime path
through the original control tree `s` along `l`. This is the inverse constructor-by-constructor
view of `pathAlongToMapLensPath`. Its equations are `mapLensPathToPathAlong_pure` and
`mapLensPathToPathAlong_liftBind`; the round trips are `mapLensPathToPathAlong_toMapLensPath` and
`pathAlongToMapLensPath_toPathAlong`. -/
def mapLensPathToPathAlong (l : Lens P Q) : (s : FreeM P α) → Path (s.mapLens l) → PathAlong l s
  | .pure _, _ => ⟨⟩
  | .liftBind a rest, ⟨d, path⟩ => ⟨d, mapLensPathToPathAlong l (rest (l.toFunB a d)) path⟩

/-- `mapLensPathToPathAlong` at a leaf: `PathAlong l (pure x)` is the trivial fiber `PUnit`, so
every path through the mapped leaf `(pure x).mapLens l` maps to `⟨⟩`.
`mapLensPathToPathAlong_liftBind` is the step through a node. -/
@[simp]
theorem mapLensPathToPathAlong_pure (l : Lens P Q) (x : α)
    (path : Path ((FreeM.pure x : FreeM P α).mapLens l)) :
    mapLensPathToPathAlong l (pure x) path = ⟨⟩ := rfl

/-- `mapLensPathToPathAlong` through a node: the direction `Path.head` at the mapped node
`l.toFunA a` becomes the runtime direction of `PathAlong.cons` and the view continues along
`Path.tail`. -/
theorem mapLensPathToPathAlong_liftBind (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (path : Path ((FreeM.lift (l.toFunA a)).bind fun d => (rest (l.toFunB a d)).mapLens l)) :
    mapLensPathToPathAlong l (FreeM.liftBind a rest) path =
      let d := Path.head (l.toFunA a) (fun d => (rest (l.toFunB a d)).mapLens l) path
      PathAlong.cons l a rest d
        (mapLensPathToPathAlong l (rest (l.toFunB a d))
          (Path.tail (l.toFunA a) (fun d => (rest (l.toFunB a d)).mapLens l) path)) := rfl

/-- `mapLensPathToPathAlong` undoes `pathAlongToMapLensPath`: viewing a runtime path through the
lens-mapped tree and back returns it unchanged. `simp` uses it to cancel the round trip;
`pathAlongToMapLensPath_toPathAlong` is the other direction. -/
@[simp]
theorem mapLensPathToPathAlong_toMapLensPath (l : Lens P Q) :
    (s : FreeM P α) → (path : PathAlong l s) →
      mapLensPathToPathAlong l s (pathAlongToMapLensPath l s path) = path
  | .pure _, _ => rfl
  | .liftBind a rest, ⟨d, path⟩ =>
      congrArg (PathAlong.cons l a rest d)
        (mapLensPathToPathAlong_toMapLensPath l (rest (l.toFunB a d)) path)

/-- `pathAlongToMapLensPath` undoes `mapLensPathToPathAlong`: viewing a path through the
lens-mapped tree as a runtime path and back returns it unchanged. `simp` uses it to cancel the
round trip; `mapLensPathToPathAlong_toMapLensPath` is the other direction. -/
@[simp]
theorem pathAlongToMapLensPath_toPathAlong (l : Lens P Q) :
    (s : FreeM P α) → (path : Path (s.mapLens l)) →
      pathAlongToMapLensPath l s (mapLensPathToPathAlong l s path) = path
  | .pure _, _ => rfl
  | .liftBind a rest, ⟨d, path⟩ =>
      congrArg (Path.cons (l.toFunA a) (fun d => (rest (l.toFunB a d)).mapLens l) d)
        (pathAlongToMapLensPath_toPathAlong l (rest (l.toFunB a d)) path)

/-- Viewing a runtime path in the lens-mapped tree preserves the selected leaf: `simp` uses it to
rewrite `output` of `s.mapLens l` along the viewed path to `outputAlong`. The converse view is
`outputAlong_mapLensPathToPathAlong`; `output_projectPathAlong` is the variant by projection. -/
@[simp]
theorem output_mapLens_pathAlongToMapLensPath (l : Lens P Q) :
    (s : FreeM P α) → (path : PathAlong l s) →
      output (s.mapLens l) (pathAlongToMapLensPath l s path) = outputAlong l s path
  | .pure _, _ => rfl
  | .liftBind a rest, ⟨d, path⟩ =>
      output_mapLens_pathAlongToMapLensPath l (rest (l.toFunB a d)) path

/-- Viewing a path through the lens-mapped tree as a runtime path preserves the selected leaf:
`simp` uses it to rewrite `outputAlong` along the viewed path to `output` of `s.mapLens l`. The
converse view is `output_mapLens_pathAlongToMapLensPath`; `output_projectPathAlong` is the variant
by projection. -/
@[simp]
theorem outputAlong_mapLensPathToPathAlong (l : Lens P Q) :
    (s : FreeM P α) → (path : Path (s.mapLens l)) →
      outputAlong l s (mapLensPathToPathAlong l s path) = output (s.mapLens l) path
  | .pure _, _ => rfl
  | .liftBind a rest, ⟨d, path⟩ => outputAlong_mapLensPathToPathAlong l (rest (l.toFunB a d)) path

/-- Pull a canonical path through the lens-mapped tree `s.mapLens l` back to the source tree `s`:
at each node the mapped direction `d` becomes the source direction `l.toFunB a d`. Its equations
are `pullMapLens_pure` and `pullMapLens_liftBind`; `pullMapLens_eq_projectPathAlong` factors it
through `mapLensPathToPathAlong`. `Path.pullMap` is the analogue for leaf relabelling. -/
def Path.pullMapLens (l : Lens P Q) : (s : FreeM P α) → Path (s.mapLens l) → Path s
  | .pure _, _ => ⟨⟩
  | .liftBind a rest, ⟨d, path⟩ => ⟨l.toFunB a d, pullMapLens l (rest (l.toFunB a d)) path⟩

/-- `Path.pullMapLens` at a leaf: `Path (pure x)` is the trivial fiber `PUnit`, so every path
through the mapped leaf `(pure x).mapLens l` pulls back to `⟨⟩`. `Path.pullMapLens_liftBind` is the
step through a node. -/
@[simp]
theorem Path.pullMapLens_pure (l : Lens P Q) (x : α)
    (path : Path ((FreeM.pure x : FreeM P α).mapLens l)) :
    Path.pullMapLens l (pure x) path = ⟨⟩ := rfl

/-- `Path.pullMapLens` through a node: the direction `Path.head` at the mapped node `l.toFunA a`
is pulled back through `l.toFunB a` to a source direction and the pullback continues along
`Path.tail`. -/
theorem Path.pullMapLens_liftBind (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (path : Path ((FreeM.lift (l.toFunA a)).bind fun d => (rest (l.toFunB a d)).mapLens l)) :
    Path.pullMapLens l (FreeM.liftBind a rest) path =
      let d := Path.head (l.toFunA a) (fun d => (rest (l.toFunB a d)).mapLens l) path
      Path.cons a rest (l.toFunB a d)
        (Path.pullMapLens l (rest (l.toFunB a d))
          (Path.tail (l.toFunA a) (fun d => (rest (l.toFunB a d)).mapLens l) path)) := rfl

/-- `Path.pullMapLens` factors through the runtime view: pulling a path through the lens-mapped
tree back directly agrees with viewing it as a runtime path by `mapLensPathToPathAlong` and then
projecting by `projectPathAlong`. Not `@[simp]`, since the right-hand side is the longer form. -/
theorem Path.pullMapLens_eq_projectPathAlong (l : Lens P Q) :
    (s : FreeM P α) → (path : Path (s.mapLens l)) →
      Path.pullMapLens l s path = projectPathAlong l s (mapLensPathToPathAlong l s path)
  | .pure _, _ => rfl
  | .liftBind a rest, ⟨d, path⟩ =>
      congrArg (Path.cons a rest (l.toFunB a d))
        (pullMapLens_eq_projectPathAlong l (rest (l.toFunB a d)) path)

/-- Pull a canonical path through the leaf-relabelled tree `s.map f` back to the original tree `s`:
relabelling touches no operation node, so every direction transports unchanged. Its equations are
`Path.pullMap_pure` and `Path.pullMap_liftBind`; `Path.pullMapLens` is the lens-mapped variant. -/
def Path.pullMap {β : Type t} (f : α → β) : (s : FreeM P α) → Path (s.map f) → Path s
  | .pure _, _ => ⟨⟩
  | .liftBind _ rest, ⟨b, path⟩ => ⟨b, pullMap f (rest b) path⟩

/-- `Path.pullMap` at a leaf: `Path (pure x)` is the trivial fiber `PUnit`, so every path through
the relabelled leaf `(pure x).map f` pulls back to `⟨⟩`. `Path.pullMap_liftBind` is the step through
a node; `Path.pullMapLens_pure` is the lens-mapped variant. -/
@[simp]
theorem Path.pullMap_pure {β : Type t} (f : α → β) (x : α)
    (path : Path ((FreeM.pure x : FreeM P α).map f)) : Path.pullMap f (pure x) path = ⟨⟩ := rfl

/-- `Path.pullMap` through a node: the direction `Path.head` at the relabelled node is reused
unchanged and the pullback continues along `Path.tail`. `Path.pullMapLens_liftBind` is the
lens-mapped variant. -/
theorem Path.pullMap_liftBind {β : Type t} (f : α → β) (a : P.A) (rest : P.B a → FreeM P α)
    (path : Path ((FreeM.lift a).bind fun b => (rest b).map f)) :
    Path.pullMap f (FreeM.liftBind a rest) path =
      Path.cons a rest (Path.head a (fun b => (rest b).map f) path)
        (Path.pullMap f (rest (Path.head a (fun b => (rest b).map f) path))
          (Path.tail a (fun b => (rest b).map f) path)) := rfl

/-- Dependent sequential composition of `FreeM` trees: `append s₁ s₂` grafts onto each leaf of `s₁`
the tree `s₂` selects for the canonical path that reached it, so a suffix may inspect the whole
branch and not merely the payload. `append_pure` and `append_liftBind` are its equations and
`append_output_eq_bind` its overlap with `>>=`. `Path.append_tree_assoc` makes grafting associative,
reindexing by the path pairing `Path.append` and its inverse `Path.split`. -/
@[implicit_reducible]
def append {β : Type t} : (s₁ : FreeM P α) → (Path s₁ → FreeM P β) → FreeM P β
  | .pure _, s₂ => s₂ ⟨⟩
  | .liftBind a rest, s₂ => .liftBind a fun b => append (rest b) (fun path => s₂ ⟨b, path⟩)

/-- `append` at a leaf: `Path (pure x)` is trivial, so the graft collapses to the suffix `s₂ ⟨⟩`.
`append_liftBind` is the step through a node, and `append_output_eq_bind` pins the bind overlap. -/
@[simp, freeM_unfold]
theorem append_pure {β : Type t} (x : α) (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β) :
    append (pure x) s₂ = s₂ ⟨⟩ := rfl

/-- `append` through an operation node: the node at `a` is rebuilt and grafting continues in every
child, the suffix selector being reindexed by prefixing the direction taken. `append_pure` is the
leaf case, and `append_output_eq_bind` pins the bind overlap. -/
@[freeM_unfold]
theorem append_liftBind {β : Type t} (a : P.A) (rest : P.B a → FreeM P α)
    (s₂ : Path (FreeM.liftBind a rest) → FreeM P β) :
    append (FreeM.liftBind a rest) s₂ =
      FreeM.liftBind a fun b => append (rest b) (fun path => s₂ ⟨b, path⟩) := rfl

/-- Grafting a suffix selected only by the leaf payload is ordinary free-monad bind: `append` is
the more general operation because its selector reads the whole branch, while `output` extracts
exactly the payload `>>=` passes on. The recursion runs on `append_pure` and `append_liftBind`, and
`β` shares the universe of `α` because the monadic `>>=` admits only one. -/
@[simp]
theorem append_output_eq_bind {β : Type v} :
    (s : FreeM P α) → (k : α → FreeM P β) → append s (fun path => k (output s path)) = s >>= k
  | .pure _, _ => rfl
  | .liftBind a rest, k =>
      congrArg (FreeM.liftBind a) (funext fun b => append_output_eq_bind (rest b) k)

namespace Path

/-! ## Canonical paths through appended trees -/

/-- Lift a two-argument family indexed by a canonical prefix path and a canonical suffix path to a
family on the appended tree, by recursion on the prefix. `liftAppend_append` cancels it against
`Path.append`, `liftAppend_split` restates it through `split`, and `packAppend`/`unpackAppend`
transport values across it. `PathAlong.liftAppend` is the runtime form along a lens. -/
def liftAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → ((path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    Path (FreeM.append s₁ s₂) → Type w
  | .pure _, _, F, path => F ⟨⟩ path
  | .liftBind _ rest, s₂, F, ⟨b, path⟩ =>
      liftAppend (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path

/-- Combine a canonical prefix path through `s₁` with a canonical suffix path through the tree `s₂`
grafts there, by recursion on the prefix; the leaf case is `append_done`. `split` is the two-sided
inverse, with round trips `split_append` and `append_split`; `append_tree_assoc` reindexes an
iterated graft by it, and `PathAlong.append` is the runtime form along a lens. -/
def append {β : Type t} : (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path₁ : Path s₁) →
    Path (s₂ path₁) → Path (FreeM.append s₁ s₂)
  | .pure _, _, _, path₂ => path₂
  | .liftBind _ rest, s₂, ⟨b, path₁⟩, path₂ =>
      ⟨b, append (rest b) (fun path => s₂ ⟨b, path⟩) path₁ path₂⟩

/-- The `pure` case of `Path.append`: a leaf prefix contributes no directions, so appending the
trivial prefix path `⟨⟩` to a suffix path returns that suffix unchanged. The `_done` suffix names
the `pure` case throughout the `append` family; `Path.split` inverts `Path.append`, and
`packAppend_done` is the sibling equation transporting payloads across `liftAppend`. -/
@[simp]
theorem append_done {β : Type t} (x : α) (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β)
    (path₂ : Path (s₂ ⟨⟩)) : append (pure x) s₂ ⟨⟩ path₂ = path₂ := rfl

/-- Associativity of path-indexed tree grafting. The suffix continuation on the right is reindexed
by `Path.append`, which pairs the outer and middle canonical paths; `Path.split` inverts it. -/
theorem append_tree_assoc {β : Type t} {γ : Type z} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (s₃ : Path (FreeM.append s₁ s₂) → FreeM P γ) →
      FreeM.append (FreeM.append s₁ s₂) s₃ = FreeM.append s₁ (fun path₁ =>
        FreeM.append (s₂ path₁) (fun path₂ => s₃ (append s₁ s₂ path₁ path₂)))
  | .pure _, _, _ => rfl
  | .liftBind a rest, s₂, s₃ => congrArg (FreeM.liftBind a) (funext fun b =>
      append_tree_assoc (rest b) (fun path => s₂ ⟨b, path⟩) (fun path => s₃ ⟨b, path⟩))

/-- Split a canonical path through `FreeM.append s₁ s₂` into a prefix path through `s₁` and a
suffix path through the tree `s₂` grafts there. It is a two-sided inverse of `append`, with
round trips `split_append` and `append_split`; `liftAppend_split` and `unliftAppend` consume it.
`PathAlong.split` is the runtime form along a lens. -/
def split {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → Path (FreeM.append s₁ s₂) →
      (path₁ : Path s₁) × Path (s₂ path₁)
  | .pure _, _, path => ⟨⟨⟩, path⟩
  | .liftBind _ rest, s₂, ⟨b, path⟩ =>
      let splitRest := split (rest b) (fun path₁ => s₂ ⟨b, path₁⟩) path
      ⟨⟨b, splitRest.1⟩, splitRest.2⟩

/-- `liftAppend` on an appended canonical path reduces to the original two-argument family, so
`simp` cancels a `liftAppend`/`append` pair. `liftAppend_split` rebuilds the same family from the
pieces `split` returns; `PathAlong.liftAppend_append` is the runtime form along a lens. -/
@[simp]
theorem liftAppend_append {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path₁ : Path s₁) →
    (path₂ : Path (s₂ path₁)) →
      liftAppend s₁ s₂ F (append s₁ s₂ path₁ path₂) = F path₁ path₂
  | .pure _, _, _, ⟨⟩, _ => rfl
  | .liftBind _ rest, s₂, F, ⟨b, path₁⟩, path₂ =>
      liftAppend_append (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂

/-- Splitting after appending recovers the original canonical prefix and suffix, so `split` is a
left inverse of `append`. `append_split` is the other round trip. -/
@[simp]
theorem split_append {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
      split s₁ s₂ (append s₁ s₂ path₁ path₂) = ⟨path₁, path₂⟩
  | .pure _, _, ⟨⟩, _ => rfl
  | .liftBind _ rest, s₂, ⟨b, path₁⟩, path₂ => by
      rw [append, split, split_append]

/-- Appending the components that `Path.split` produces recovers the original canonical path, so
`Path.append` is a left inverse of `Path.split`. `Path.split_append` is the other round trip, and
`PathAlong.append_split` is the runtime form along a lens. -/
@[simp]
theorem append_split {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path : Path (FreeM.append s₁ s₂)) →
      let splitPath := split s₁ s₂ path
      append s₁ s₂ splitPath.1 splitPath.2 = path
  | .pure _, _, _ => rfl
  | .liftBind _ rest, s₂, ⟨b, path⟩ => by
      simp only [split, append, append_split]

/-- Transport a value of `F path₁ path₂` to the `liftAppend` family at the appended canonical path,
following the recursion of `liftAppend` so that no explicit equality transport is needed; the leaf
case is `packAppend_done`. `unpackAppend` is the inverse, with `unpackAppend_packAppend` and
`packAppend_unpackAppend` the two round trips; `PathAlong.packAppend` is the runtime form
along a lens. -/
def packAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path₁ : Path s₁) →
    (path₂ : Path (s₂ path₁)) → F path₁ path₂ → liftAppend s₁ s₂ F (append s₁ s₂ path₁ path₂)
  | .pure _, _, _, ⟨⟩, _, x => x
  | .liftBind _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      packAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- The `pure` case of `packAppend`: over a leaf prefix the appended path is the suffix path
itself, so the payload crosses `liftAppend` unchanged. `append_done` is the sibling equation and
`unpackAppend` is the inverse transport. -/
@[simp]
theorem packAppend_done {β : Type t} (x : α) (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β)
    (F : (path₁ : Path (FreeM.pure (P := P) x)) → Path (s₂ path₁) → Type w) (path₂ : Path (s₂ ⟨⟩))
    (y : F ⟨⟩ path₂) : packAppend (pure x) s₂ F ⟨⟩ path₂ y = y := rfl

/-- Transport a value from the `liftAppend` family at an appended canonical path back to the
original two-argument family, undoing the recursion of `liftAppend` with no equality transport.
`packAppend` is the inverse, with `unpackAppend_packAppend` and `packAppend_unpackAppend` the round
trips; `collapseAppend_append` reduces to it and `PathAlong.unpackAppend` is the runtime form
along a lens. -/
def unpackAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path₁ : Path s₁) →
    (path₂ : Path (s₂ path₁)) → liftAppend s₁ s₂ F (append s₁ s₂ path₁ path₂) → F path₁ path₂
  | .pure _, _, _, ⟨⟩, _, x => x
  | .liftBind _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      unpackAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- Pointwise congruence for `Path.liftAppend`: families agreeing at every pair of a canonical
prefix and suffix path lift to the same family on the appended tree, so the pair-indexed family
may be swapped for a pointwise-equal one. Hypothesis and conclusion are equalities of types, not
`Iff`s, so it is applied by `rw`/`Eq.mpr`, not `simp`. -/
theorem liftAppend_congr {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F G : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (∀ path₁ path₂, F path₁ path₂ = G path₁ path₂) → (path : Path (FreeM.append s₁ s₂)) →
      liftAppend s₁ s₂ F path = liftAppend s₁ s₂ G path :=
  fun s₁ s₂ _ _ h path =>
    congrArg (fun F => liftAppend s₁ s₂ F path) (funext₂ h)

/-- `Path.liftAppend` leaves a constant family alone: a family ignoring both the canonical prefix
and the canonical suffix path lifts to that same constant on the appended tree. It is the constant
case of `liftAppend_split`, and unlike `liftAppend_congr` it is `@[simp]`: the right-hand side `γ`
is closed, so `simp` always has a target to rewrite to. -/
@[simp]
theorem liftAppend_const {β : Type t} (γ : Type w) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path : Path (FreeM.append s₁ s₂)) →
      liftAppend s₁ s₂ (fun _ _ => γ) path = γ
  | .pure _, _, _ => rfl
  | .liftBind _ rest, s₂, ⟨b, path⟩ => liftAppend_const γ (rest b) (fun path₁ => s₂ ⟨b, path₁⟩) path

/-- `liftAppend` at a canonical path is the two-argument family evaluated at the pieces `split`
returns. This is the `split`-side reconstruction, while `liftAppend_append` is the `append`-side
cancellation; `unliftAppend` witnesses the equation by transport, and `PathAlong.liftAppend_split`
is the runtime form along a lens. -/
theorem liftAppend_split {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path : Path (FreeM.append s₁ s₂)) →
      let splitPath := split s₁ s₂ path
      liftAppend s₁ s₂ F path = F splitPath.1 splitPath.2
  | .pure _, _, _, _ => rfl
  | .liftBind _ rest, s₂, F, ⟨b, path⟩ =>
      liftAppend_split (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path

/-- Transport a value of `liftAppend` at a canonical path through `FreeM.append s₁ s₂` to the
two-argument family at the pieces `split` returns, following the recursion of `liftAppend` so that
no explicit equality transport is needed. `liftAppend_split` is the equation it witnesses;
`PathAlong.unliftAppend` is the runtime form along a lens. -/
def unliftAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ F path →
      let splitPath := split s₁ s₂ path
      F splitPath.1 splitPath.2
  | .pure _, _, _, _, x => x
  | .liftBind _ rest, s₂, F, ⟨b, path⟩, x =>
      unliftAppend (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path x

/-- One of the two round trips between `packAppend` and `unpackAppend`: at an appended canonical
path, packing a value of the two-argument family and unpacking it again returns it unchanged.
`packAppend_unpackAppend` is the round trip in the other order and
`PathAlong.unpackAppend_packAppend` is the runtime form along a lens. -/
@[simp]
theorem unpackAppend_packAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path₁ : Path s₁) →
    (path₂ : Path (s₂ path₁)) → (x : F path₁ path₂) →
      unpackAppend s₁ s₂ F path₁ path₂ (packAppend s₁ s₂ F path₁ path₂ x) = x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .liftBind _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      unpackAppend_packAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- One of the two round trips between `packAppend` and `unpackAppend`: at an appended canonical
path, unpacking a `liftAppend` value and packing it again returns it unchanged.
`unpackAppend_packAppend` is the round trip in the other order and
`PathAlong.packAppend_unpackAppend` is the runtime form along a lens. -/
@[simp]
theorem packAppend_unpackAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path₁ : Path s₁) →
    (path₂ : Path (s₂ path₁)) → (x : liftAppend s₁ s₂ F (append s₁ s₂ path₁ path₂)) →
      packAppend s₁ s₂ F path₁ path₂ (unpackAppend s₁ s₂ F path₁ path₂ x) = x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .liftBind _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      packAppend_unpackAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- Collapse a `liftAppend` family whose pair index passes through `append`: a payload of
`liftAppend s₁ s₂ (fun path₁ path₂ => F (append s₁ s₂ path₁ path₂)) path` is a payload of `F` at
the fused path `path` itself. `collapseAppend_append` is the computation rule at an appended path,
reducing it to `unpackAppend` on the same family. -/
def collapseAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (F : Path (FreeM.append s₁ s₂) → Type w) →
    (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ (fun path₁ path₂ => F (append s₁ s₂ path₁ path₂)) path → F path
  | .pure _, _, _, _, x => x
  | .liftBind _ rest, s₂, F, ⟨b, path⟩, x =>
      collapseAppend (rest b) (fun path₁ => s₂ ⟨b, path₁⟩) (fun tail => F ⟨b, tail⟩) path x

/-- The computation rule for `collapseAppend` at a fused path: collapsing at
`append s₁ s₂ path₁ path₂` is `unpackAppend` at the pair `path₁`, `path₂` on the same family.
Together with `append_split`, which presents any canonical path through `FreeM.append s₁ s₂` in
that form, this evaluates `collapseAppend` everywhere. -/
@[simp]
theorem collapseAppend_append {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (F : Path (FreeM.append s₁ s₂) → Type w) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) → (x : liftAppend s₁ s₂
      (fun path₁ path₂ => F (append s₁ s₂ path₁ path₂)) (append s₁ s₂ path₁ path₂)) →
    collapseAppend s₁ s₂ F (append s₁ s₂ path₁ path₂) x =
      unpackAppend s₁ s₂ (fun path₁ path₂ => F (append s₁ s₂ path₁ path₂)) path₁ path₂ x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .liftBind _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      collapseAppend_append (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun tail => F ⟨b, tail⟩) path₁ path₂ x

/-- Split a fused `liftAppend` product payload into separately lifted payloads. The payload passes
through every node unchanged, so this is definitionally the identity and inverse to
`liftAppendProdMk`: `liftAppendProdMk_liftAppendProd` and `liftAppendProd_liftAppendProdMk` are its
round trips, both by `rfl`, and `liftAppendProd_packAppend` evaluates it on an appended path. -/
def liftAppendProd {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path →
      liftAppend s₁ s₂ A path × liftAppend s₁ s₂ B path
  | .pure _, _, _, _, _, x => x
  | .liftBind _ rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProd (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

/-- Fuse separately lifted payloads into a `liftAppend` product payload. The payload passes through
every node unchanged, so this is definitionally the identity and inverse to `liftAppendProd`, with
round trips `liftAppendProdMk_liftAppendProd` and `liftAppendProd_liftAppendProdMk`, both `rfl`. -/
def liftAppendProdMk {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ A path × liftAppend s₁ s₂ B path →
      liftAppend s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path
  | .pure _, _, _, _, _, x => x
  | .liftBind _ rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProdMk (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

/-- `liftAppendProdMk` undoes `liftAppendProd`: fusing a split product payload returns it
unchanged. Both maps are definitionally the identity, so the structural recursion transports the
equation through each node and bottoms out at `rfl`. `simp` uses it to cancel the round trip;
`liftAppendProd_liftAppendProdMk` is the other direction. -/
@[simp]
theorem liftAppendProdMk_liftAppendProd {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path : Path (FreeM.append s₁ s₂)) →
    (x : liftAppend s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path) →
      liftAppendProdMk s₁ s₂ A B path (liftAppendProd s₁ s₂ A B path x) = x
  | .pure _, _, _, _, _, _ => rfl
  | .liftBind _ rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProdMk_liftAppendProd (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

/-- `liftAppendProd` undoes `liftAppendProdMk`: splitting a fused product payload returns it
unchanged. Both maps are definitionally the identity, so the structural recursion transports the
equation through each node and bottoms out at `rfl`. `simp` uses it to cancel the round trip;
`liftAppendProdMk_liftAppendProd` is the other direction. -/
@[simp]
theorem liftAppendProd_liftAppendProdMk {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path : Path (FreeM.append s₁ s₂)) →
    (x : liftAppend s₁ s₂ A path × liftAppend s₁ s₂ B path) →
      liftAppendProd s₁ s₂ A B path (liftAppendProdMk s₁ s₂ A B path x) = x
  | .pure _, _, _, _, _, _ => rfl
  | .liftBind _ rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProd_liftAppendProdMk (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

/-- The computation rule for `liftAppendProd` at an appended canonical path: splitting the product
payload that `packAppend` transports to `append s₁ s₂ path₁ path₂` yields the two components, each
packed on its own. The round trips `liftAppendProdMk_liftAppendProd` and
`liftAppendProd_liftAppendProdMk` instead cancel `liftAppendProd` against `liftAppendProdMk`. -/
@[simp]
theorem liftAppendProd_packAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path₁ : Path s₁) →
    (path₂ : Path (s₂ path₁)) → (x : A path₁ path₂ × B path₁ path₂) →
      liftAppendProd s₁ s₂ A B (append s₁ s₂ path₁ path₂)
        (packAppend s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path₁ path₂ x) =
          (packAppend s₁ s₂ A path₁ path₂ x.1, packAppend s₁ s₂ B path₁ path₂ x.2)
  | .pure _, _, _, _, ⟨⟩, _, _ => rfl
  | .liftBind _ rest, s₂, A, B, ⟨b, path₁⟩, path₂, x =>
      liftAppendProd_packAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- The round trip `packAppend` then `unliftAppend` is the identity at the path `append` fuses
from `path₁` and `path₂`: an arbitrary relation `R` at the pair `split` recovers, applied to the
round-tripped payloads, agrees with `R` at `path₁`, `path₂` on `x` and `y`. Wrapping in `R`
sidesteps the index mismatch between the `split`-recovered pair and `path₁`, `path₂`;
`liftAppendRel_iff` produces exactly this left-hand side. -/
theorem rel_unliftAppend_append {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F G : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (R : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)), F path₁ path₂ → G path₁ path₂ → Prop) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) → (x : F path₁ path₂) → (y : G path₁ path₂) →
    let path := append s₁ s₂ path₁ path₂
    R (split s₁ s₂ path).1 (split s₁ s₂ path).2
      (unliftAppend s₁ s₂ F path (packAppend s₁ s₂ F path₁ path₂ x))
      (unliftAppend s₁ s₂ G path (packAppend s₁ s₂ G path₁ path₂ y)) = R path₁ path₂ x y
  | .pure _, _, _, _, _, ⟨⟩, _, _, _ => rfl
  | .liftBind _ rest, s₂, F, G, R, ⟨b, path₁⟩, path₂, x, y =>
      rel_unliftAppend_append (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => G ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => R ⟨b, path₁⟩ path₂) path₁ path₂ x y

/-- Lift a binary relation on pair-indexed families to the fused appended path: at a leaf it is
`R` on the trivial prefix, and at a node the recursion descends under the chosen direction.
`liftAppendRel_iff` characterises it as `R` at the path pair `split` recovers, on the payloads
`unliftAppend` extracts from the two `liftAppend` families. `liftAppendPred` is the unary form. -/
def liftAppendRel {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F G : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (R : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)), F path₁ path₂ → G path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) → liftAppend s₁ s₂ F path → liftAppend s₁ s₂ G path → Prop
  | .pure _, _, _, _, R, path, x, y => R ⟨⟩ path x y
  | .liftBind _ rest, s₂, F, G, R, ⟨b, path⟩, x, y =>
      liftAppendRel (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => G ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => R ⟨b, path₁⟩ path₂) path x y

/-- `liftAppendRel` unfolds to `R` at the path pair `split` recovers from the fused path, applied
to the payloads `unliftAppend` extracts from the two `liftAppend` families; use it to turn a
`liftAppendRel` goal into a plain `R` goal. `liftAppendPred_iff` is the unary form. -/
theorem liftAppendRel_iff {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F G : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (R : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)), F path₁ path₂ → G path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) → (x : liftAppend s₁ s₂ F path) →
    (y : liftAppend s₁ s₂ G path) →
      liftAppendRel s₁ s₂ F G R path x y ↔
        R (split s₁ s₂ path).1 (split s₁ s₂ path).2 (unliftAppend s₁ s₂ F path x)
          (unliftAppend s₁ s₂ G path y)
  | .pure _, _, _, _, _, _, _, _ => Iff.rfl
  | .liftBind _ rest, s₂, F, G, R, ⟨b, path⟩, x, y =>
      liftAppendRel_iff (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => G ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => R ⟨b, path₁⟩ path₂) path x y

/-- Lift a unary predicate on a pair-indexed family to the fused appended path: at a leaf it is
`Pred` on the trivial prefix, and at a node the recursion descends under the chosen direction.
`liftAppendPred_iff` characterises it as `Pred` at the path pair `split` recovers, on the payload
`unliftAppend` extracts from the `liftAppend` family. `liftAppendRel` is the binary form. -/
def liftAppendPred {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (Pred : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)), F path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) → liftAppend s₁ s₂ F path → Prop
  | .pure _, _, _, Pred, path, x => Pred ⟨⟩ path x
  | .liftBind _ rest, s₂, F, Pred, ⟨b, path⟩, x =>
      liftAppendPred (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => Pred ⟨b, path₁⟩ path₂) path x

/-- `liftAppendPred` unfolds to `Pred` at the path pair `split` recovers from the fused path,
applied to the payload `unliftAppend` extracts from the `liftAppend` family; use it to turn a
`liftAppendPred` goal into a plain `Pred` goal. `liftAppendRel_iff` is the binary form. -/
theorem liftAppendPred_iff {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (Pred : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)), F path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) → (x : liftAppend s₁ s₂ F path) →
      liftAppendPred s₁ s₂ F Pred path x ↔
        Pred (split s₁ s₂ path).1 (split s₁ s₂ path).2 (unliftAppend s₁ s₂ F path x)
  | .pure _, _, _, _, _, _ => Iff.rfl
  | .liftBind _ rest, s₂, F, Pred, ⟨b, path⟩, x =>
      liftAppendPred_iff (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => Pred ⟨b, path₁⟩ path₂) path x

end Path

namespace PathAlong

/-! ## Lens-executed paths through appended trees

Every declaration below mirrors the `Path` declaration of the same name, with one difference: the
suffix tree is indexed by the control projection `projectPathAlong l s₁ path₁` of the runtime
prefix rather than by the prefix path itself. The two families are genuinely separate. `Path s` and
`PathAlong (Lens.id P) s` agree as types, but `projectPathAlong (Lens.id P) s₁` is a structural
recursion on `s₁`, so for a variable tree it is stuck: deriving one family from the other would
reintroduce exactly the equality transports these definitions are shaped to avoid.
-/

/-- Lift a two-argument family indexed by a runtime prefix path and a runtime suffix path to a
family on the appended tree, by recursion on the prefix; the suffix is selected by the control
projection of the runtime prefix. `PathAlong.liftAppend_append` cancels it against `append`,
`PathAlong.liftAppend_split` restates it through `split`, and `packAppend`, `unpackAppend` and
`unliftAppend` transport values across it. `Path.liftAppend` is the control-path form. -/
def liftAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    ((path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    PathAlong l (FreeM.append s₁ s₂) → Type w
  | .pure _, _, F, path => F ⟨⟩ path
  | .liftBind a rest, s₂, F, ⟨d, path⟩ =>
      liftAppend l (rest (l.toFunB a d)) (fun path₁ => s₂ ⟨l.toFunB a d, path₁⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path

/-- Combine a runtime prefix path through `s₁` with a runtime suffix path through the tree `s₂`
grafts at the control projection `projectPathAlong l s₁ path₁` of that prefix, by recursion on the
prefix. `split` is the two-sided inverse, with round trips `split_append` and `append_split`, and
`liftAppend_append` cancels the fused family. `projectPathAlong_append` sends an appended runtime
path to `Path.append`, the control-path form whose suffix is indexed by the control path itself. -/
def append {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path₁ : PathAlong l s₁) →
    PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → PathAlong l (FreeM.append s₁ s₂)
  | .pure _, _, _, path₂ => path₂
  | .liftBind a rest, s₂, ⟨d, path₁⟩, path₂ =>
      ⟨d, append l (rest (l.toFunB a d)) (fun path => s₂ ⟨l.toFunB a d, path⟩) path₁ path₂⟩

/-- Split a runtime path through `FreeM.append s₁ s₂` into a prefix runtime path `path₁` through
`s₁` and a suffix runtime path through the tree `s₂` grafts at the control projection
`projectPathAlong l s₁ path₁` of that prefix. It is the two-sided inverse of `append`, with round
trips `split_append` and `append_split`; `liftAppend_split`
and `PathAlong.unliftAppend` consume it. `Path.split` is the control-path form. -/
def split {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → PathAlong l (FreeM.append s₁ s₂) →
      (path₁ : PathAlong l s₁) × PathAlong l (s₂ (projectPathAlong l s₁ path₁))
  | .pure _, _, path => ⟨⟨⟩, path⟩
  | .liftBind a rest, s₂, ⟨d, path⟩ =>
      let splitRest := split l (rest (l.toFunB a d)) (fun path₁ => s₂ ⟨l.toFunB a d, path₁⟩) path
      ⟨⟨d, splitRest.1⟩, splitRest.2⟩

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
relating source and runtime paths across `split`/`append` needs
`projectPathAlong` (and the `LocalMap.toHom` machinery it elaborates to)
to unfold there. -/
attribute [local implicit_reducible] Displayed.LocalMap.toHom
  Displayed.LocalMap.toHomFun projectPathAlongLocalMap projectPathAlong

/-- `liftAppend` on an appended runtime path reduces to the original two-argument family, so `simp`
cancels a `liftAppend`/`append` pair. `Path.liftAppend_append` is the control-path form, where the
suffix is indexed by the control path directly; `packAppend` and `unpackAppend` transport values
across this equality without an explicit transport. -/
@[simp]
theorem liftAppend_append {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) → (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
      liftAppend l s₁ s₂ F (append l s₁ s₂ path₁ path₂) = F path₁ path₂
  | .pure _, _, _, ⟨⟩, _ => rfl
  | .liftBind a rest, s₂, F, ⟨d, path₁⟩, path₂ =>
      liftAppend_append l (rest (l.toFunB a d)) (fun path => s₂ ⟨l.toFunB a d, path⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path₁ path₂

/-- Splitting after appending recovers the original runtime prefix and suffix, so `split` is a left
inverse of `append` along `l`. `Path.split_append` is the control-path form, whose suffix is indexed
by the control path directly; `PathAlong.append_split` is the other round trip. -/
@[simp]
theorem split_append {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
      split l s₁ s₂ (append l s₁ s₂ path₁ path₂) = ⟨path₁, path₂⟩
  | .pure _, _, ⟨⟩, _ => rfl
  | .liftBind a rest, s₂, ⟨d, path₁⟩, path₂ => by
      rw [append, split, split_append]

/-- Appending the components produced by `split` recovers the original runtime path, so `append` is
a left inverse of `split` along `l`. `Path.append_split` is the control-path form, whose suffix is
indexed by the control path directly; `PathAlong.split_append` is the other round trip. -/
@[simp]
theorem append_split {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path : PathAlong l (FreeM.append s₁ s₂)) →
      let splitPath := split l s₁ s₂ path
      append l s₁ s₂ splitPath.1 splitPath.2 = path
  | .pure _, _, _ => rfl
  | .liftBind a rest, s₂, ⟨d, path⟩ => by
      simp only [split, append, append_split]

/-- Transport a value of `F path₁ path₂` to the `liftAppend` family at the appended runtime path,
following the recursion of `liftAppend` so that no explicit equality transport is needed.
`unpackAppend` is the inverse, with `unpackAppend_packAppend` and `packAppend_unpackAppend` the two
round trips; `Path.packAppend` is the control-path form. -/
def packAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) → (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    F path₁ path₂ → liftAppend l s₁ s₂ F (append l s₁ s₂ path₁ path₂)
  | .pure _, _, _, ⟨⟩, _, x => x
  | .liftBind a rest, s₂, F, ⟨d, path₁⟩, path₂, x =>
      packAppend l (rest (l.toFunB a d)) (fun path => s₂ ⟨l.toFunB a d, path⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path₁ path₂ x

/-- Transport a value from the `liftAppend` family at an appended runtime path back to the original
two-argument family, undoing the recursion of `liftAppend` with no explicit equality transport.
`packAppend` is the inverse, with `unpackAppend_packAppend` and `packAppend_unpackAppend` the two
round trips; `Path.unpackAppend` is the control-path form. -/
def unpackAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) → (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    liftAppend l s₁ s₂ F (append l s₁ s₂ path₁ path₂) → F path₁ path₂
  | .pure _, _, _, ⟨⟩, _, x => x
  | .liftBind a rest, s₂, F, ⟨d, path₁⟩, path₂, x =>
      unpackAppend l (rest (l.toFunB a d)) (fun path => s₂ ⟨l.toFunB a d, path⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path₁ path₂ x

/-- `liftAppend` at a runtime path is the two-argument family evaluated at the pieces
`PathAlong.split` returns, so the family is recovered from a path never presented as an `append`.
This is the `split`-side reconstruction; `PathAlong.liftAppend_append` is the `append`-side
cancellation, and `Path.liftAppend_split` is the control-path form. -/
theorem liftAppend_split {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path : PathAlong l (FreeM.append s₁ s₂)) →
      let splitPath := split l s₁ s₂ path
      liftAppend l s₁ s₂ F path = F splitPath.1 splitPath.2
  | .pure _, _, _, _ => rfl
  | .liftBind a rest, s₂, F, ⟨d, path⟩ =>
      liftAppend_split l (rest (l.toFunB a d)) (fun path₁ => s₂ ⟨l.toFunB a d, path₁⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path

/-- Transport a value of `PathAlong.liftAppend` at a runtime path through `FreeM.append s₁ s₂` to
the two-argument family at the pieces `PathAlong.split` returns, following the recursion of
`liftAppend` so that no explicit equality transport is needed. `PathAlong.liftAppend_split` is the
equation it witnesses; `Path.unliftAppend` is the control-path form. -/
def unliftAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path : PathAlong l (FreeM.append s₁ s₂)) → liftAppend l s₁ s₂ F path →
      let splitPath := split l s₁ s₂ path
      F splitPath.1 splitPath.2
  | .pure _, _, _, _, x => x
  | .liftBind a rest, s₂, F, ⟨d, path⟩, x =>
      unliftAppend l (rest (l.toFunB a d)) (fun path₁ => s₂ ⟨l.toFunB a d, path₁⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path x

/-- One of the two round trips between `PathAlong.packAppend` and `PathAlong.unpackAppend`: at an
appended runtime path, packing a value of the two-argument family and unpacking it again returns
it unchanged. `PathAlong.packAppend_unpackAppend` is the round trip in the other order and
`Path.unpackAppend_packAppend` is the control-path form. -/
@[simp]
theorem unpackAppend_packAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) → (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    (x : F path₁ path₂) →
      unpackAppend l s₁ s₂ F path₁ path₂ (packAppend l s₁ s₂ F path₁ path₂ x) = x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .liftBind a rest, s₂, F, ⟨d, path₁⟩, path₂, x =>
      unpackAppend_packAppend l (rest (l.toFunB a d)) (fun path => s₂ ⟨l.toFunB a d, path⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path₁ path₂ x

/-- One of the two round trips between `PathAlong.packAppend` and `PathAlong.unpackAppend`: at an
appended runtime path, unpacking a `liftAppend` value and packing it again returns it unchanged.
`PathAlong.unpackAppend_packAppend` is the round trip in the other order and
`Path.packAppend_unpackAppend` is the control-path form. -/
@[simp]
theorem packAppend_unpackAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) → (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    (x : liftAppend l s₁ s₂ F (append l s₁ s₂ path₁ path₂)) →
      packAppend l s₁ s₂ F path₁ path₂ (unpackAppend l s₁ s₂ F path₁ path₂ x) = x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .liftBind a rest, s₂, F, ⟨d, path₁⟩, path₂, x =>
      packAppend_unpackAppend l (rest (l.toFunB a d)) (fun path => s₂ ⟨l.toFunB a d, path⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path₁ path₂ x

/-- Projecting a runtime path built by `PathAlong.append` gives the `Path.append` of the projected
prefix and suffix, so `simp` pushes `projectPathAlong` past a graft. The suffix is projected at the
control path `projectPathAlong l s₁ path₁` indexing it; `PathAlong.split_append` is the round trip
that takes an appended runtime path apart again. -/
@[simp]
theorem projectPathAlong_append {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
      projectPathAlong l (FreeM.append s₁ s₂) (append l s₁ s₂ path₁ path₂) =
        Path.append s₁ s₂ (projectPathAlong l s₁ path₁)
          (projectPathAlong l (s₂ (projectPathAlong l s₁ path₁)) path₂)
  | .pure _, _, ⟨⟩, _ => rfl
  | .liftBind a rest, s₂, ⟨d, path₁⟩, path₂ =>
      congrArg
        (Path.cons a (fun b => FreeM.append (rest b) fun path => s₂ (Path.cons a rest b path))
          (l.toFunB a d))
        (projectPathAlong_append l (rest (l.toFunB a d))
          (fun path => s₂ (Path.cons a rest (l.toFunB a d) path)) path₁ path₂)

end PathAlong

/-! ## Well-founded stopping trees -/

/-- Indexed W-type of stopping trees for a transition system observed through an arbitrary family
`Obs`: at each state an inhabitant either stops or extends into the state `step s obs` selected by
each observation. Because `done s` is available at every state, inhabitation alone does not assert
termination. It is the initial `StoppingTree.Algebra`, with catamorphism `StoppingTree.fold` and
uniqueness lemma `StoppingTree.eq_fold`; `Telescope` specializes `Obs` to path fibres. -/
inductive StoppingTree {St : Type z} (Obs : St → Type w) (step : (s : St) → Obs s → St) :
    St → Type (max w z)
  /-- Stop at the current state, running no further transition. -/
  | done (s : St) : StoppingTree Obs step s
  /-- Run one transition layer, recursing into the state selected by each observation. -/
  | extend (s : St) (cont : (obs : Obs s) → StoppingTree Obs step (step s obs)) :
      StoppingTree Obs step s

namespace StoppingTree

variable {St : Type z} {Obs : St → Type w} {step : (s : St) → Obs s → St}

/-- Algebra for the indexed polynomial `y ↦ (fun s => PUnit ⊕ ((obs : Obs s) → y (step s obs)))`: a
`done` interpretation at each state and an `extend` interpretation of one transition layer.
`StoppingTree` is its initial algebra: `fold` is the unique homomorphism into `Carrier`, with
`fold_done` and `fold_extend` its computation rules and `eq_fold` its uniqueness. -/
structure Algebra (Carrier : St → Type t) where
  /-- Interpretation of the `StoppingTree.done` leaf at a state. -/
  done : (s : St) → Carrier s
  /-- Interpretation of a `StoppingTree.extend` layer from the value chosen by each observation. -/
  extend : (s : St) → ((obs : Obs s) → Carrier (step s obs)) → Carrier s

/-- Catamorphism out of the initial stopping-tree algebra: recursion over a `StoppingTree` that
interprets each `done` leaf and each `extend` layer by the matching field of the `Algebra` `alg`.
Its computation rules `fold_done` and `fold_extend` hold by `rfl`, and `eq_fold` is the uniqueness
half of the universal property. `Telescope.toFreeM` is `fold` at the `FreeM.append` algebra. -/
def fold {Carrier : St → Type t} (alg : Algebra (Obs := Obs) (step := step) Carrier) :
    {s : St} → StoppingTree Obs step s → Carrier s
  | _, .done s => alg.done s
  | _, .extend s cont => alg.extend s fun obs => fold alg (cont obs)

/-- `fold` at a stopping leaf: the catamorphism reads off the algebra's `done` interpretation and
recurses no further. `fold_extend` is the equation through a transition layer, and `eq_fold` is
the uniqueness half of the initial-algebra universal property. -/
@[simp]
theorem fold_done {Carrier : St → Type t} (alg : Algebra (Obs := Obs) (step := step) Carrier)
    (s : St) : fold alg (StoppingTree.done s) = alg.done s := rfl

/-- `fold` through a transition layer: one `extend` node is interpreted by the algebra's `extend`,
with the fold applied under every observation. `fold_done` is the equation at a stopping leaf, and
`eq_fold` is the uniqueness half of the initial-algebra universal property. -/
@[simp]
theorem fold_extend {Carrier : St → Type t} (alg : Algebra (Obs := Obs) (step := step) Carrier)
    (s : St) (cont : (obs : Obs s) → StoppingTree Obs step (step s obs)) :
    fold alg (StoppingTree.extend s cont) = alg.extend s (fun obs => fold alg (cont obs)) := rfl

/-- Uniqueness half of the initial-algebra universal property: any `f` satisfying the algebra
equations `hDone` and `hExtend` agrees pointwise with `fold`. `fold_done` and `fold_extend` say
that `fold alg` itself satisfies them, so it is the unique such algebra homomorphism. -/
theorem eq_fold {Carrier : St → Type t} (alg : Algebra (Obs := Obs) (step := step) Carrier)
    (f : {s : St} → StoppingTree Obs step s → Carrier s)
    (hDone : (s : St) → f (StoppingTree.done s) = alg.done s)
    (hExtend : (s : St) → (cont : (obs : Obs s) → StoppingTree Obs step (step s obs)) →
      f (StoppingTree.extend s cont) = alg.extend s (fun obs => f (cont obs))) :
    {s : St} → (tree : StoppingTree Obs step s) → f tree = fold alg tree
  | _, .done s => hDone s
  | _, .extend s cont => (hExtend s cont).trans
      (congrArg (alg.extend s) (funext fun obs => eq_fold alg f hDone hExtend (cont obs)))

end StoppingTree

/-- `StoppingTree` with observations instantiated to the canonical path fibres `Path (round s)`:
each layer runs the round `round s` and branches on the path taken through it. `Telescope.done` and
`Telescope.extend` are the constructor wrappers, `Telescope.toFreeM` flattens a telescope into one
`FreeM` tree, and a more compact observation type should use `StoppingTree` directly. -/
abbrev Telescope {St : Type z} {Out : St → Type v} (round : (s : St) → FreeM P (Out s))
    (step : (s : St) → Path (round s) → St) : St → Type (max uB z) :=
  StoppingTree (fun s => Path (round s)) step

namespace Telescope

variable {St : Type z} {Out : St → Type v} {round : (s : St) → FreeM P (Out s)}
    {step : (s : St) → Path (round s) → St}

/-- Terminating constructor for a canonical-path telescope: `StoppingTree.done` at the observation
family `Path (round s)`, available at every state. `toFreeM_done` flattens this telescope to
`finish s`, and `Telescope.extend` runs one more round instead. -/
abbrev done (s : St) : Telescope round step s := StoppingTree.done s

/-- Extending constructor for a canonical-path telescope: `StoppingTree.extend` at the observation
family `Path (round s)`, so `cont` is indexed by the canonical branch path through the round
`round s` and resumes at the next state `step s path`. `toFreeM_extend` flattens this telescope to
an `append` of that round, and `Telescope.done` stops there instead. -/
abbrev extend (s : St) (cont : (path : Path (round s)) → Telescope round step (step s path)) :
    Telescope round step s := StoppingTree.extend s cont

/-- Flatten a canonical-path telescope into a single `FreeM` tree by iterated dependent append,
using `finish` at terminal states. It is `StoppingTree.fold` at the algebra whose `extend` is
`FreeM.append`, so `toFreeM_done` and `toFreeM_extend` hold by `rfl`. -/
def toFreeM {β : Type t} (finish : St → FreeM P β) :
    {s : St} → Telescope round step s → FreeM P β :=
  StoppingTree.fold { done := finish, extend := fun s => append (round s) }

/-- `toFreeM` at a terminating telescope: `Telescope.done s` runs no rounds, so flattening it
yields `finish s` with no append. This is `StoppingTree.fold_done` at the append algebra;
`toFreeM_extend` is the equation for a telescope that runs one more round. -/
@[simp]
theorem toFreeM_done {β : Type t} (finish : St → FreeM P β) (s : St) :
    (Telescope.done (round := round) (step := step) s).toFreeM finish = finish s := rfl

/-- `toFreeM` at a telescope running one more round: `Telescope.extend s cont` runs `round s` and
flattens `cont path` under every canonical path `path` of that round, which is `FreeM.append`. It
is `StoppingTree.fold_extend` at the append algebra; `toFreeM_done` is the terminating case. -/
@[simp]
theorem toFreeM_extend {β : Type t} (finish : St → FreeM P β) (s : St)
    (cont : (path : Path (round s)) → Telescope round step (step s path)) :
    (Telescope.extend s cont).toFreeM finish =
      append (round s) (fun path => (cont path).toFreeM finish) := rfl

end Telescope

end FreeM
end PFunctor
