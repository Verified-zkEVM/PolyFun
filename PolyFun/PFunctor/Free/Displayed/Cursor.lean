/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Cursor
public import PolyFun.PFunctor.Free.Displayed.Decoration

/-!
# Restricting displayed data along free-program cursors

A displayed shape can be restricted to a cursor residual when each node value
exposes the displayed value at a selected child. This capability is explicit:
an arbitrary `Displayed.Shape` need not permit such a projection.

The generic restriction algorithm follows `Cursor.Spine` once. Node
decorations and dependent over-decorations supply their canonical child
projections as thin specializations.
-/

@[expose] public section

universe uA uB v w w₂ w₃ w₄ w₅

namespace PFunctor
namespace FreeM
namespace Displayed

variable {P : PFunctor.{uA, uB}} {α : Type v}

namespace Shape

/-- Capability for selecting one recursive child from a displayed node value. -/
structure ChildProjection (D : Shape.{uA, uB, v, w} P α) where
  /-- Project the displayed value stored at child `b`. -/
  child :
    (a : P.A) →
    (children : P.B a → Sort w) →
    D.node a children →
    (b : P.B a) → children b

end Shape

namespace OverShape

/-- Dependent child projection for a displayed-over shape. -/
structure ChildProjection
    {D : Shape.{uA, uB, v, w} P α}
    (base : Shape.ChildProjection D)
    (R : OverShape.{uA, uB, v, w, w₂} D) where
  /-- Project the over-value lying above the selected base child. -/
  child :
    (a : P.A) →
    (children : P.B a → Sort w) →
    (overChildren : (b : P.B a) → children b → Sort w₂) →
    (d : D.node a children) →
    R.node a children overChildren d →
    (b : P.B a) → overChildren b (base.child a children d b)

end OverShape

variable {D : Shape.{uA, uB, v, w} P α}

/-- Restrict displayed data along an indexed cursor spine. -/
def restrictSpine (projection : Shape.ChildProjection D) :
    {program residual : FreeM P α} →
    Cursor.Spine program residual →
    Displayed D program → Displayed D residual
  | _, _, .root _, d => d
  | _, _, .down (a := a) answer tail, d =>
      restrictSpine projection tail
        (projection.child a _ d answer)

@[simp]
theorem restrictSpine_root (projection : Shape.ChildProjection D)
    (program : FreeM P α) (d : Displayed D program) :
    restrictSpine projection (.root program) d = d :=
  rfl

@[simp]
theorem restrictSpine_down (projection : Shape.ChildProjection D)
    {a : P.A} {next : P.B a → FreeM P α}
    {residual : FreeM P α} (answer : P.B a)
    (tail : Cursor.Spine (next answer) residual)
    (d : Displayed D (FreeM.liftBind a next)) :
    restrictSpine projection (.down answer tail) d =
      restrictSpine projection tail
        (projection.child a (fun b => Displayed D (next b)) d answer) :=
  rfl

theorem restrictSpine_comp (projection : Shape.ChildProjection D)
    {program middle residual : FreeM P α}
    (first : Cursor.Spine program middle)
    (second : Cursor.Spine middle residual)
    (d : Displayed D program) :
    restrictSpine projection (first.comp second) d =
      restrictSpine projection second (restrictSpine projection first d) := by
  induction first with
  | root => rfl
  | down answer tail ih =>
      exact ih second (projection.child _ _ d answer)

/-- Restrict displayed data to the residual selected by a cursor. -/
def restrict (projection : Shape.ChildProjection D)
    {program : FreeM P α} (cursor : Cursor program)
    (d : Displayed D program) : Displayed D cursor.residual :=
  restrictSpine projection cursor.spine d

@[simp]
theorem restrict_root (projection : Shape.ChildProjection D)
    (program : FreeM P α) (d : Displayed D program) :
    restrict projection (Cursor.root program) d = d :=
  rfl

@[simp]
theorem restrict_down (projection : Shape.ChildProjection D)
    {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer))
    (d : Displayed D (FreeM.liftBind a next)) :
    restrict projection (Cursor.down answer tail) d =
      restrict projection tail
        (projection.child a (fun b => Displayed D (next b)) d answer) :=
  rfl

theorem restrict_comp (projection : Shape.ChildProjection D)
    {program : FreeM P α} (first : Cursor program)
    (second : Cursor first.residual) (d : Displayed D program) :
    restrict projection (first.comp second) d =
      restrict projection second (restrict projection first d) :=
  restrictSpine_comp projection first.spine second.spine d

namespace Over

variable {R : OverShape.{uA, uB, v, w, w₂} D}

/-- Restrict displayed-over data along an indexed cursor spine. -/
def restrictSpine (base : Shape.ChildProjection D)
    (projection : OverShape.ChildProjection base R) :
    {program residual : FreeM P α} →
    (spine : Cursor.Spine program residual) →
    (d : Displayed D program) →
    Over R program d →
    Over R residual (Displayed.restrictSpine base spine d)
  | _, _, .root _, _, r => r
  | _, _, .down (a := a) answer tail, d, r =>
      restrictSpine base projection tail
        (base.child a _ d answer)
        (projection.child a _ _ d r answer)

@[simp]
theorem restrictSpine_root (base : Shape.ChildProjection D)
    (projection : OverShape.ChildProjection base R)
    (program : FreeM P α) (d : Displayed D program)
    (r : Over R program d) :
    restrictSpine base projection (.root program) d r = r :=
  rfl

@[simp]
theorem restrictSpine_down (base : Shape.ChildProjection D)
    (projection : OverShape.ChildProjection base R)
    {a : P.A} {next : P.B a → FreeM P α}
    {residual : FreeM P α} (answer : P.B a)
    (tail : Cursor.Spine (next answer) residual)
    (d : Displayed D (FreeM.liftBind a next))
    (r : Over R (FreeM.liftBind a next) d) :
    restrictSpine base projection (.down answer tail) d r =
      restrictSpine base projection tail
        (base.child a (fun b => Displayed D (next b)) d answer)
        (projection.child a (fun b => Displayed D (next b))
          (fun b d => Over R (next b) d) d r answer) :=
  rfl

theorem restrictSpine_comp (base : Shape.ChildProjection D)
    (projection : OverShape.ChildProjection base R)
    {program middle residual : FreeM P α}
    (first : Cursor.Spine program middle)
    (second : Cursor.Spine middle residual)
    (d : Displayed D program) (r : Over R program d) :
    HEq
      (restrictSpine base projection (first.comp second) d r)
      (restrictSpine base projection second
        (Displayed.restrictSpine base first d)
        (restrictSpine base projection first d r)) := by
  induction first with
  | root => exact HEq.rfl
  | down answer tail ih =>
      exact ih second (base.child _ _ d answer)
        (projection.child _ _ _ d r answer)

/-- Restrict displayed-over data to the residual selected by a cursor. -/
def restrict (base : Shape.ChildProjection D)
    (projection : OverShape.ChildProjection base R)
    {program : FreeM P α} (cursor : Cursor program)
    (d : Displayed D program) (r : Over R program d) :
    Over R cursor.residual (Displayed.restrict base cursor d) :=
  restrictSpine base projection cursor.spine d r

@[simp]
theorem restrict_root (base : Shape.ChildProjection D)
    (projection : OverShape.ChildProjection base R)
    (program : FreeM P α) (d : Displayed D program)
    (r : Over R program d) :
    restrict base projection (Cursor.root program) d r = r :=
  rfl

@[simp]
theorem restrict_down (base : Shape.ChildProjection D)
    (projection : OverShape.ChildProjection base R)
    {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer))
    (d : Displayed D (FreeM.liftBind a next))
    (r : Over R (FreeM.liftBind a next) d) :
    restrict base projection (Cursor.down answer tail) d r =
      restrict base projection tail
        (base.child a (fun b => Displayed D (next b)) d answer)
        (projection.child a (fun b => Displayed D (next b))
          (fun b d => Over R (next b) d) d r answer) :=
  rfl

theorem restrict_comp (base : Shape.ChildProjection D)
    (projection : OverShape.ChildProjection base R)
    {program : FreeM P α} (first : Cursor program)
    (second : Cursor first.residual)
    (d : Displayed D program) (r : Over R program d) :
    HEq
      (restrict base projection (first.comp second) d r)
      (restrict base projection second
        (Displayed.restrict base first d)
        (restrict base projection first d r)) :=
  restrictSpine_comp base projection first.spine second.spine d r

end Over

namespace Decoration

variable {Γ : P.A → Type w₂}

/-- Node decorations expose the decoration stored at every child. -/
def childProjection :
    Shape.ChildProjection (Decoration.shape (P := P) (α := α) Γ) where
  child := fun _ _ d b => d.2 b

/-- Restrict a node decoration to a cursor residual. -/
def restrict {program : FreeM P α} (cursor : Cursor program)
    (d : Decoration Γ program) : Decoration Γ cursor.residual :=
  Displayed.restrict childProjection cursor d

@[simp]
theorem restrict_root (program : FreeM P α) (d : Decoration Γ program) :
    restrict (Cursor.root program) d = d :=
  rfl

@[simp]
theorem restrict_down {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer))
    (d : Decoration Γ (FreeM.liftBind a next)) :
    restrict (Cursor.down answer tail) d = restrict tail (d.2 answer) :=
  rfl

theorem restrict_comp {program : FreeM P α} (first : Cursor program)
    (second : Cursor first.residual) (d : Decoration Γ program) :
    restrict (first.comp second) d = restrict second (restrict first d) :=
  Displayed.restrict_comp childProjection first second d

theorem restrict_map {Δ : P.A → Type w₃} (f : ∀ a, Γ a → Δ a) :
    {program : FreeM P α} → (cursor : Cursor program) →
    (d : Decoration Γ program) →
    restrict cursor (Decoration.map f program d) =
      Decoration.map f cursor.residual (restrict cursor d)
  | _, ⟨_, .root _⟩, _ => rfl
  | _, ⟨_, .down answer tail⟩, d =>
      restrict_map f ⟨_, tail⟩ (d.2 answer)

namespace Over

variable {A : (a : P.A) → Γ a → Type w₃}

/-- Dependent node decorations expose the over-decoration at every child. -/
def childProjection :
    OverShape.ChildProjection
      (Decoration.childProjection (P := P) (α := α) (Γ := Γ))
      (Decoration.overShape (P := P) (α := α) Γ A) where
  child := fun _ _ _ _ r b => r.2 b

/-- Restrict a dependent decoration to a cursor residual. -/
def restrict {program : FreeM P α} (cursor : Cursor program)
    (d : Decoration Γ program) (r : Decoration.Over Γ A program d) :
    Decoration.Over Γ A cursor.residual (Decoration.restrict cursor d) :=
  Displayed.Over.restrict Decoration.childProjection childProjection cursor d r

@[simp]
theorem restrict_root (program : FreeM P α) (d : Decoration Γ program)
    (r : Decoration.Over Γ A program d) :
    restrict (Cursor.root program) d r = r :=
  rfl

@[simp]
theorem restrict_down {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer))
    (d : Decoration Γ (FreeM.liftBind a next))
    (r : Decoration.Over Γ A (FreeM.liftBind a next) d) :
    restrict (Cursor.down answer tail) d r =
      restrict tail (d.2 answer) (r.2 answer) :=
  rfl

theorem restrict_comp {program : FreeM P α} (first : Cursor program)
    (second : Cursor first.residual) (d : Decoration Γ program)
    (r : Decoration.Over Γ A program d) :
    HEq
      (restrict (first.comp second) d r)
      (restrict second (Decoration.restrict first d) (restrict first d r)) :=
  Displayed.Over.restrict_comp Decoration.childProjection childProjection
    first second d r

theorem restrict_map {B : (a : P.A) → Γ a → Type w₄}
    (f : ∀ a γ, A a γ → B a γ) :
    {program : FreeM P α} → (cursor : Cursor program) →
    (d : Decoration Γ program) → (r : Decoration.Over Γ A program d) →
    restrict cursor d (map f program d r) =
      map f cursor.residual (Decoration.restrict cursor d) (restrict cursor d r)
  | _, ⟨_, .root _⟩, _, _ => rfl
  | _, ⟨_, .down answer tail⟩, d, r =>
      restrict_map f ⟨_, tail⟩ (d.2 answer) (r.2 answer)

theorem restrict_mapBase
    {Δ : P.A → Type w₄}
    {B : (a : P.A) → Δ a → Type w₅}
    (f : ∀ a, Γ a → Δ a)
    (g : ∀ a γ, A a γ → B a (f a γ)) :
    {program : FreeM P α} → (cursor : Cursor program) →
    (d : Decoration Γ program) → (r : Decoration.Over Γ A program d) →
    HEq
      (restrict cursor (Decoration.map f program d) (mapBase f g program d r))
      (mapBase f g cursor.residual (Decoration.restrict cursor d)
        (restrict cursor d r))
  | _, ⟨_, .root _⟩, _, _ => HEq.rfl
  | _, ⟨_, .down answer tail⟩, d, r =>
      restrict_mapBase f g ⟨_, tail⟩ (d.2 answer) (r.2 answer)

end Over

theorem restrict_ofOver
    {A : (a : P.A) → Γ a → Type w₃}
    {program : FreeM P α} (cursor : Cursor program)
    (d : Decoration Γ program) (r : Decoration.Over Γ A program d) :
    Decoration.restrict cursor (ofOver program d r) =
      ofOver cursor.residual (Decoration.restrict cursor d)
        (Decoration.Over.restrict cursor d r) := by
  rcases cursor with ⟨residual, spine⟩
  induction spine with
  | root => rfl
  | down answer tail ih =>
      exact ih (d.2 answer) (r.2 answer)

theorem toOver_restrict
    {A : (a : P.A) → Γ a → Type w₃}
    {program : FreeM P α} (cursor : Cursor program)
    (d : Decoration (Context.extend Γ A) program) :
    toOver cursor.residual (Decoration.restrict cursor d) =
      ⟨Decoration.restrict cursor (toOver program d).1,
        Decoration.Over.restrict cursor (toOver program d).1 (toOver program d).2⟩ := by
  rw [← ofOver_toOver program d, restrict_ofOver, toOver_ofOver]
  have h := toOver_ofOver program (toOver program d).1 (toOver program d).2
  rw [h]

end Decoration

end Displayed
end FreeM
end PFunctor
