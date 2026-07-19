/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Basic

/-!
# Displayed families over `PFunctor.FreeM`

This file defines displayed algebras over the free monad of a polynomial
functor.

For a polynomial/container `P`, a payload type `α`, and a tree
`s : PFunctor.FreeM P α`, `FreeM.Displayed D s` is the family obtained by
interpreting terminal payloads through `D.leaf` and internal positions through
`D.node`.

This is the common substrate behind several familiar structures:

* decorations, where each node stores metadata and recursively decorates every
  child;
* paths, where each node chooses one child and recursively follows that child;
* compact observations, where some nodes may be skipped or otherwise
  reinterpreted.

Categorically, this is the displayed algebra generated over the initial
`FreeM` algebra. A `Displayed.Section D` is a global dependent section: it
chooses data in the displayed fiber over every tree. Constructor-local fold
data produces such a section via `Displayed.Section.ofConstructors`.
-/

@[expose] public section

universe uA uB v w w₂ w₃ w₄ w₅ w₆

namespace PFunctor
namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

namespace Displayed

/--
A large algebra generating displayed fibers over `FreeM P α`.

The `leaf` argument interprets terminal payloads. The `node` argument
interprets a polynomial position `a : P.A`, given the already-generated
displayed fibers for each child `b : P.B a`.

Special cases include node decorations, branch paths, and compact observation
views that suppress uninformative nodes.
-/
structure Algebra (P : PFunctor.{uA, uB}) (α : Type v) where
  /-- The fiber assigned to a terminal payload `x : α`. -/
  leaf : α → Sort w
  /-- The fiber assigned to a node at position `a`, given the fibers already chosen for
  each child `b : P.B a`. -/
  node : (a : P.A) → ((b : P.B a) → Sort w) → Sort w

end Displayed

/--
Evaluate a displayed algebra over a concrete `FreeM` tree.

This generates the displayed fiber at every tree by recursion on the free
polynomial structure.
-/
def Displayed (D : Displayed.Algebra P α) :
    FreeM P α → Sort w
  | .pure x => D.leaf x
  | .liftBind a rest => D.node a (fun b => Displayed D (rest b))

namespace Displayed

@[simp]
theorem pure_eq (D : Algebra P α) (x : α) :
    Displayed D (pure x) = D.leaf x :=
  rfl

@[simp]
theorem liftBind_eq (D : Algebra P α) (a : P.A) (rest : P.B a → FreeM P α) :
    Displayed D ((FreeM.lift a).bind rest) =
      D.node a (fun b => Displayed D (rest b)) :=
  rfl

variable {D : Displayed.Algebra.{uA, uB, v, w} P α}

/--
A dependent displayed algebra over an existing displayed algebra.

If `D` assigns a fiber to each `FreeM` tree, then an `Over.Algebra D` assigns a
second-layer fiber over each inhabitant of `Displayed D s`. This is the
generic form of a dependent decoration over a base decoration.
-/
structure Over.Algebra
    (D : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w} P α) where
  /-- The second-layer fiber over a base leaf fiber at payload `x : α`. -/
  leaf : (x : α) → D.leaf x → Sort w₂
  /-- The second-layer fiber over a base node fiber at position `a`, given the second-layer
  fibers already chosen over each child. -/
  node :
    (a : P.A) →
    (children : (b : P.B a) → Sort w) →
    ((b : P.B a) → children b → Sort w₂) →
    D.node a children → Sort w₂

/--
Evaluate a dependent displayed algebra over concrete displayed data.

This is the dependent analogue of `Displayed`: the base displayed data chooses
which second-layer fiber is available at every node.
-/
def Over (E : Over.Algebra D) :
    (s : FreeM P α) → Displayed D s → Sort w₂
  | .pure x, d => E.leaf x d
  | .liftBind a rest, d =>
      E.node a (fun b => Displayed D (rest b))
        (fun b d => Over E (rest b) d) d

namespace Over

@[simp]
theorem pure_eq
    (E : _root_.PFunctor.FreeM.Displayed.Over.Algebra D)
    (x : α) (d : D.leaf x) :
    _root_.PFunctor.FreeM.Displayed.Over E (pure x) d = E.leaf x d :=
  rfl

@[simp]
theorem liftBind_eq
    (E : _root_.PFunctor.FreeM.Displayed.Over.Algebra D)
    (a : P.A) (rest : P.B a → FreeM P α)
    (d : D.node a (fun b => Displayed D (rest b))) :
    _root_.PFunctor.FreeM.Displayed.Over E ((FreeM.lift a).bind rest) d =
      E.node a (fun b => Displayed D (rest b))
        (fun b d => _root_.PFunctor.FreeM.Displayed.Over E (rest b) d) d :=
  rfl

end Over

/-- The total space of a displayed family together with one displayed-over layer. -/
abbrev Over.Total (E : Over.Algebra D) (s : FreeM P α) :=
  PSigma fun d : Displayed D s => _root_.PFunctor.FreeM.Displayed.Over E s d

/-- A section chooses displayed data over every `FreeM` tree. -/
abbrev Section (D : _root_.PFunctor.FreeM.Displayed.Algebra P α) :=
  (s : FreeM P α) → Displayed D s

namespace Section

/--
Construct a section from constructor-local data.

This is the displayed-family specialization of the dependent recursor for
`FreeM`.
-/
def ofConstructors
    (onLeaf : (x : α) → D.leaf x)
    (onNode :
      (a : P.A) →
      (children : (b : P.B a) → Sort w) →
      ((b : P.B a) → children b) →
      D.node a children) :
    Section D
  | .pure x => onLeaf x
  | .liftBind a rest => onNode a _ (fun b => ofConstructors onLeaf onNode (rest b))

@[simp]
theorem ofConstructors_pure
    (onLeaf : (x : α) → D.leaf x)
    (onNode :
      (a : P.A) →
      (children : (b : P.B a) → Sort w) →
      ((b : P.B a) → children b) →
      D.node a children)
    (x : α) :
    ofConstructors onLeaf onNode (pure x) = onLeaf x :=
  rfl

@[simp]
theorem ofConstructors_liftBind
    (onLeaf : (x : α) → D.leaf x)
    (onNode :
      (a : P.A) →
      (children : (b : P.B a) → Sort w) →
      ((b : P.B a) → children b) →
      D.node a children)
    (a : P.A) (rest : P.B a → FreeM P α) :
    ofConstructors onLeaf onNode ((FreeM.lift a).bind rest) =
      onNode a (fun b => Displayed D (rest b))
        (fun b => ofConstructors onLeaf onNode (rest b)) :=
  rfl

end Section

variable
    {E : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w₂} P α}
    {F : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w₃} P α}
    {G : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w₄} P α}

/-- A morphism between two displayed families over the same `FreeM` tree. -/
structure Hom
    (D : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w} P α)
    (E : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w₂} P α) where
  /-- The fiberwise action, mapping the `D`-fiber to the `E`-fiber over each tree `s`. -/
  toFun : (s : FreeM P α) → Displayed D s → Displayed E s

instance : CoeFun (Hom D E)
    (fun _ => (s : FreeM P α) → Displayed D s → Displayed E s) where
  coe f := f.toFun

namespace Hom

@[ext]
theorem ext (f g : Hom D E)
    (h : ∀ s d, f s d = g s d) : f = g := by
  cases f
  cases g
  congr
  funext s d
  exact h s d

/-- Identity morphism of a displayed family. -/
protected def id : Hom D D where
  toFun := fun _ d => d

/-- Composition of displayed-family morphisms. -/
def comp (g : Hom E F) (f : Hom D E) :
    Hom D F where
  toFun := fun s d => g s (f s d)

@[simp]
theorem id_apply (s : FreeM P α) (d : Displayed D s) :
    Hom.id s d = d :=
  rfl

@[simp]
theorem comp_apply (g : Hom E F) (f : Hom D E)
    (s : FreeM P α) (d : Displayed D s) :
    comp g f s d = g s (f s d) :=
  rfl

@[simp]
theorem comp_id (f : Hom D E) :
    comp Hom.id f = f := by
  ext s d
  rfl

@[simp]
theorem id_comp (f : Hom D E) :
    comp f Hom.id = f := by
  ext s d
  rfl

theorem comp_assoc (h : Hom F G) (g : Hom E F) (f : Hom D E) :
    comp h (comp g f) = comp (comp h g) f := by
  ext s d
  rfl

end Hom

/--
A constructor-local map between displayed algebras.

The `mapNode` field maps one node layer, given already-mapped recursive child
data. This is transformation data sufficient to recursively produce a
tree-indexed `Displayed.Hom` via `LocalMap.toHom`; it is intentionally not
called a homomorphism because an arbitrary, potentially negative `Algebra.node`
need not admit identity or composition at this local level.
-/
structure LocalMap
    (D : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w} P α)
    (E : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w₂} P α) where
  /-- The action on leaf fibers, mapping `D.leaf x` to `E.leaf x`. -/
  mapLeaf : (x : α) → D.leaf x → E.leaf x
  /-- The action on one node layer, mapping `D.node` to `E.node` given the already-mapped
  child data. -/
  mapNode :
    (a : P.A) →
    (sourceChildren : (b : P.B a) → Sort w) →
    (targetChildren : (b : P.B a) → Sort w₂) →
    ((b : P.B a) → sourceChildren b → targetChildren b) →
    D.node a sourceChildren → E.node a targetChildren

namespace LocalMap

/-- The recursive function underlying `LocalMap.toHom`. -/
def toHomFun (η : LocalMap D E) :
    (s : FreeM P α) → Displayed D s → Displayed E s
  | .pure x, d => η.mapLeaf x d
  | .liftBind a rest, d =>
      η.mapNode a _ _ (fun b => toHomFun η (rest b)) d

/-- Interpret a constructor-local map as a tree-indexed displayed morphism. -/
def toHom (η : LocalMap D E) : Hom D E where
  toFun := toHomFun η

@[simp]
theorem toHom_pure (η : LocalMap D E) (x : α) (d : D.leaf x) :
    η.toHom (pure x) d = η.mapLeaf x d :=
  rfl

@[simp]
theorem toHom_liftBind (η : LocalMap D E)
    (a : P.A) (rest : P.B a → FreeM P α)
    (d : D.node a (fun b => Displayed D (rest b))) :
    η.toHom ((FreeM.lift a).bind rest) d =
      η.mapNode a (fun b => Displayed D (rest b))
        (fun b => Displayed E (rest b))
        (fun b => η.toHom (rest b)) d :=
  rfl

end LocalMap

variable
    {R : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w, w₅} D}
    {S : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w₂, w₆} E}
    {T : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w₃, w₄} F}

/--
A morphism between displayed-over families, lying over a morphism between their
base displayed families.

When the base morphism is `Displayed.Hom.id`, this is a fiberwise morphism over
the same displayed data.
-/
structure Over.Hom
    {D : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w} P α}
    {E : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w₂} P α}
    (η : Displayed.Hom D E)
    (R : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w, w₅} D)
    (S : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w₂, w₆} E) where
  /-- The fiberwise action on second-layer fibers, sending the `R`-fiber over `d` to the
  `S`-fiber over `η s d`. -/
  toFun :
    (s : FreeM P α) →
    (d : Displayed D s) →
    _root_.PFunctor.FreeM.Displayed.Over R s d →
    _root_.PFunctor.FreeM.Displayed.Over S s (η s d)

namespace Over

instance {η : Displayed.Hom D E} : CoeFun (Displayed.Over.Hom η R S)
    (fun _ =>
      (s : FreeM P α) →
      (d : Displayed D s) →
      _root_.PFunctor.FreeM.Displayed.Over R s d →
      _root_.PFunctor.FreeM.Displayed.Over S s (η s d)) where
  coe f := f.toFun

namespace Hom

@[ext]
theorem ext {η : Displayed.Hom D E} (f g : Displayed.Over.Hom η R S)
    (h : ∀ s d r, f s d r = g s d r) : f = g := by
  cases f
  cases g
  congr
  funext s d r
  exact h s d r

/-- Identity morphism of a displayed-over family. -/
protected def id
    (R : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w, w₅} D) :
    Displayed.Over.Hom (Displayed.Hom.id (D := D)) R R where
  toFun := fun _ _ r => r

/-- Composition of displayed-over morphisms over composed base morphisms. -/
def comp {η : Displayed.Hom D E} {θ : Displayed.Hom E F}
    (g : Displayed.Over.Hom θ S T) (f : Displayed.Over.Hom η R S) :
    Displayed.Over.Hom (Displayed.Hom.comp θ η) R T where
  toFun := fun s d r => g s (η s d) (f s d r)

@[simp]
theorem id_apply (s : FreeM P α) (d : Displayed D s)
    (r : _root_.PFunctor.FreeM.Displayed.Over R s d) :
    Displayed.Over.Hom.id R s d r = r :=
  rfl

@[simp]
theorem comp_apply {η : Displayed.Hom D E} {θ : Displayed.Hom E F}
    (g : Displayed.Over.Hom θ S T) (f : Displayed.Over.Hom η R S)
    (s : FreeM P α) (d : Displayed D s) (r : _root_.PFunctor.FreeM.Displayed.Over R s d) :
    comp g f s d r = g s (η s d) (f s d r) :=
  rfl

@[simp]
theorem comp_id {η : Displayed.Hom D E} (f : Displayed.Over.Hom η R S) :
    comp (Displayed.Over.Hom.id S) f = f := by
  ext s d r
  rfl

@[simp]
theorem id_comp {η : Displayed.Hom D E} (f : Displayed.Over.Hom η R S) :
    comp f (Displayed.Over.Hom.id R) = f := by
  ext s d r
  rfl

theorem comp_assoc {η : Displayed.Hom D E} {θ : Displayed.Hom E F}
    {ι : Displayed.Hom F G}
    {U : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w₄, w₅} G}
    (h : Displayed.Over.Hom ι T U) (g : Displayed.Over.Hom θ S T)
    (f : Displayed.Over.Hom η R S) :
    comp h (comp g f) = comp (comp h g) f := by
  ext s d r
  rfl

end Hom

/-- Map displayed-over data by a displayed-over morphism. -/
def map {η : Displayed.Hom D E} (f : Displayed.Over.Hom η R S) :
    (s : FreeM P α) →
    (d : Displayed D s) →
    _root_.PFunctor.FreeM.Displayed.Over R s d →
    _root_.PFunctor.FreeM.Displayed.Over S s (η s d)
  | s, d, r => f s d r

@[simp]
theorem map_apply {η : Displayed.Hom D E} (f : Displayed.Over.Hom η R S)
    (s : FreeM P α) (d : Displayed D s) (r : _root_.PFunctor.FreeM.Displayed.Over R s d) :
    map f s d r = f s d r :=
  rfl

@[simp]
theorem map_id (s : FreeM P α) (d : Displayed D s)
    (r : _root_.PFunctor.FreeM.Displayed.Over R s d) :
    map (Displayed.Over.Hom.id R) s d r = r :=
  rfl

@[simp]
theorem map_comp {η : Displayed.Hom D E} {θ : Displayed.Hom E F}
    (g : Displayed.Over.Hom θ S T) (f : Displayed.Over.Hom η R S)
    (s : FreeM P α) (d : Displayed D s) (r : _root_.PFunctor.FreeM.Displayed.Over R s d) :
    map (Displayed.Over.Hom.comp g f) s d r = map g s (η s d) (map f s d r) :=
  rfl

/--
A constructor-local fiber map between dependent displayed algebras over the
same base displayed algebra.

This is transformation data for recursively mapping only the over-layer while
keeping the base displayed data fixed. `FiberLocalMap.toHom` interprets it as a
genuine tree-indexed `Displayed.Over.Hom`.
-/
structure FiberLocalMap
    (R : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w, w₅} D)
    (S : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w, w₆} D) where
  /-- The action on leaf fibers, mapping `R.leaf` to `S.leaf` over the same base leaf data. -/
  mapLeaf : (x : α) → (d : D.leaf x) → R.leaf x d → S.leaf x d
  /-- The action on one node layer, mapping `R.node` to `S.node` over the same base node data,
  given the already-mapped child data. -/
  mapNode :
    (a : P.A) →
    (children : (b : P.B a) → Sort w) →
    (sourceOver : (b : P.B a) → children b → Sort w₅) →
    (targetOver : (b : P.B a) → children b → Sort w₆) →
    ((b : P.B a) → (d : children b) → sourceOver b d → targetOver b d) →
    (d : D.node a children) →
    R.node a children sourceOver d →
    S.node a children targetOver d

namespace FiberLocalMap

variable
    {R' : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w, w₅} D}
    {S' : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w, w₆} D}

/-- The recursive function underlying `FiberLocalMap.toHom`. -/
def toHomFun (η : FiberLocalMap R' S') :
    (s : FreeM P α) →
    (d : Displayed D s) →
    _root_.PFunctor.FreeM.Displayed.Over R' s d →
    _root_.PFunctor.FreeM.Displayed.Over S' s d
  | .pure x, d, r => η.mapLeaf x d r
  | .liftBind a rest, d, r =>
      η.mapNode a (fun b => Displayed D (rest b))
        (fun b d => _root_.PFunctor.FreeM.Displayed.Over R' (rest b) d)
        (fun b d => _root_.PFunctor.FreeM.Displayed.Over S' (rest b) d)
        (fun b d => toHomFun η (rest b) d) d r

/-- Interpret a constructor-local fiber map as a displayed-over morphism. -/
def toHom (η : FiberLocalMap R' S') :
    Displayed.Over.Hom (Displayed.Hom.id (D := D)) R' S' where
  toFun := toHomFun η

@[simp]
theorem toHom_pure (η : FiberLocalMap R' S') (x : α)
    (d : D.leaf x) (r : R'.leaf x d) :
    η.toHom (pure x) d r = η.mapLeaf x d r :=
  rfl

@[simp]
theorem toHom_liftBind (η : FiberLocalMap R' S')
    (a : P.A) (rest : P.B a → FreeM P α)
    (d : D.node a (fun b => Displayed D (rest b)))
    (r : R'.node a (fun b => Displayed D (rest b))
      (fun b d => _root_.PFunctor.FreeM.Displayed.Over R' (rest b) d) d) :
    η.toHom ((FreeM.lift a).bind rest) d r =
      η.mapNode a (fun b => Displayed D (rest b))
        (fun b d => _root_.PFunctor.FreeM.Displayed.Over R' (rest b) d)
        (fun b d => _root_.PFunctor.FreeM.Displayed.Over S' (rest b) d)
        (fun b d => η.toHom (rest b) d) d r :=
  rfl

end FiberLocalMap

/--
A constructor-local map between dependent displayed algebras, lying over a
constructor-local map between their base displayed algebras.

Its interpretation by `Over.LocalMap.toHom` is a genuine tree-indexed
`Displayed.Over.Hom` over the interpreted base map.
-/
structure LocalMap
    {D : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w} P α}
    {E : _root_.PFunctor.FreeM.Displayed.Algebra.{uA, uB, v, w₂} P α}
    (η : Displayed.LocalMap D E)
    (R : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w, w₅} D)
    (S : _root_.PFunctor.FreeM.Displayed.Over.Algebra.{uA, uB, v, w₂, w₆} E) where
  /-- The action on leaf fibers, mapping `R.leaf` to `S.leaf` over the base leaf morphism
  `η.mapLeaf`. -/
  mapLeaf :
    (x : α) →
    (d : D.leaf x) →
    R.leaf x d →
    S.leaf x (η.mapLeaf x d)
  /-- The action on one node layer, mapping `R.node` to `S.node` over the base node morphism
  `η.mapNode`, given the already-mapped child data. -/
  mapNode :
    (a : P.A) →
    (sourceChildren : (b : P.B a) → Sort w) →
    (targetChildren : (b : P.B a) → Sort w₂) →
    (mapChild : (b : P.B a) → sourceChildren b → targetChildren b) →
    (sourceOver : (b : P.B a) → sourceChildren b → Sort w₅) →
    (targetOver : (b : P.B a) → targetChildren b → Sort w₆) →
    ((b : P.B a) → (d : sourceChildren b) →
      sourceOver b d → targetOver b (mapChild b d)) →
    (d : D.node a sourceChildren) →
    R.node a sourceChildren sourceOver d →
    S.node a targetChildren targetOver
      (η.mapNode a sourceChildren targetChildren mapChild d)

namespace LocalMap

/-- The recursive function underlying `Over.LocalMap.toHom`. -/
def toHomFun
    {η : Displayed.LocalMap D E} (φ : LocalMap η R S) :
    (s : FreeM P α) →
    (d : Displayed D s) →
    _root_.PFunctor.FreeM.Displayed.Over R s d →
    _root_.PFunctor.FreeM.Displayed.Over S s (η.toHom s d)
  | .pure x, d, r => φ.mapLeaf x d r
  | .liftBind a rest, d, r =>
      φ.mapNode a (fun b => Displayed D (rest b))
        (fun b => Displayed E (rest b))
        (fun b => η.toHom (rest b))
        (fun b d => _root_.PFunctor.FreeM.Displayed.Over R (rest b) d)
        (fun b d => _root_.PFunctor.FreeM.Displayed.Over S (rest b) d)
        (fun b d => toHomFun φ (rest b) d) d r

/--
Interpret a constructor-local over map as a displayed-over morphism over
the interpreted base morphism.
-/
def toHom {η : Displayed.LocalMap D E} (φ : LocalMap η R S) :
    Displayed.Over.Hom η.toHom R S where
  toFun := toHomFun φ

@[simp]
theorem toHom_pure {η : Displayed.LocalMap D E} (φ : LocalMap η R S)
    (x : α) (d : D.leaf x) (r : R.leaf x d) :
    φ.toHom (pure x) d r = φ.mapLeaf x d r :=
  rfl

@[simp]
theorem toHom_liftBind {η : Displayed.LocalMap D E} (φ : LocalMap η R S)
    (a : P.A) (rest : P.B a → FreeM P α)
    (d : D.node a (fun b => Displayed D (rest b)))
    (r : R.node a (fun b => Displayed D (rest b))
      (fun b d => _root_.PFunctor.FreeM.Displayed.Over R (rest b) d) d) :
    φ.toHom ((FreeM.lift a).bind rest) d r =
      φ.mapNode a (fun b => Displayed D (rest b))
        (fun b => Displayed E (rest b))
        (fun b => η.toHom (rest b))
        (fun b d => _root_.PFunctor.FreeM.Displayed.Over R (rest b) d)
        (fun b d => _root_.PFunctor.FreeM.Displayed.Over S (rest b) d)
        (fun b d => φ.toHom (rest b) d) d r :=
  rfl

end LocalMap

end Over

/-- Map displayed data by an interpreted morphism. -/
def map (f : Hom D E) :
    (s : FreeM P α) → Displayed D s → Displayed E s
  | s, d => f s d

@[simp]
theorem map_apply (f : Hom D E) (s : FreeM P α) (d : Displayed D s) :
    map f s d = f s d :=
  rfl

@[simp]
theorem map_id (s : FreeM P α) (d : Displayed D s) :
    map Hom.id s d = d :=
  rfl

@[simp]
theorem map_comp (g : Hom E F) (f : Hom D E)
    (s : FreeM P α) (d : Displayed D s) :
    map (Hom.comp g f) s d = map g s (map f s d) :=
  rfl

end Displayed

end FreeM
end PFunctor
