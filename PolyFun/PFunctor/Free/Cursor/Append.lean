/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Displayed.Append
public import PolyFun.PFunctor.Free.Displayed.Cursor

/-!
# Cursors through dependent append

This file classifies a cursor through `FreeM.append program suffix` into two
disjoint cases. A left cursor remains inside `program` and has an internal
residual. A right cursor has completed a canonical path through `program` and
continues inside the selected `suffix` tree.

The classification is intrinsic and cast-free. `Cursor.liftAppend` transports
a cursor through dependent append, while `Cursor.joinRight` follows a complete
prefix path before continuing with a suffix cursor.
-/

@[expose] public section

universe uA uB v w w₂ w₃

namespace PFunctor
namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v} {β : Type w}

/-- Evidence that a free program is an internal node rather than a leaf. -/
inductive IsNode : FreeM P α → Prop
  | liftBind (a : P.A) (next : P.B a → FreeM P α) :
      IsNode (FreeM.liftBind a next)

namespace Cursor

/-- A cursor has an internal residual exactly when it is not terminal. -/
theorem not_isTerminal_iff_isNode {program : FreeM P α} (cursor : Cursor program) :
    ¬ cursor.IsTerminal ↔ IsNode cursor.residual := by
  rcases cursor with ⟨residual, spine⟩
  cases residual with
  | pure output =>
      constructor
      · intro notTerminal
        exact (notTerminal ⟨output, rfl⟩).elim
      · intro isNode
        cases isNode
  | liftBind a next =>
      constructor
      · intro _
        exact IsNode.liftBind a next
      · intro _ terminal
        rcases terminal with ⟨output, residualEq⟩
        cases residualEq

namespace Spine

/-- Transport a cursor spine through dependent `FreeM.append`. -/
def liftAppend : {program residual : FreeM P α} →
    (spine : Spine program residual) →
    (suffix : Path program → FreeM P β) →
    Spine (FreeM.append program suffix)
      (FreeM.append residual (fun path => suffix (spine.plug path)))
  | _, _, .root program, suffix => .root (FreeM.append program suffix)
  | _, _, .down answer tail, suffix =>
      .down answer (liftAppend tail (fun path => suffix ⟨answer, path⟩))

@[simp]
theorem liftAppend_root (program : FreeM P α)
    (suffix : Path program → FreeM P β) :
    (Spine.root program).liftAppend suffix =
      Spine.root (FreeM.append program suffix) :=
  rfl

@[simp]
theorem liftAppend_down {a : P.A} {next : P.B a → FreeM P α}
    {residual : FreeM P α} (answer : P.B a)
    (tail : Spine (next answer) residual)
    (suffix : Path (FreeM.liftBind a next) → FreeM P β) :
    (Spine.down answer tail).liftAppend suffix =
      Spine.down answer
        (tail.liftAppend (fun path => suffix ⟨answer, path⟩)) :=
  rfl

@[simp]
theorem length_liftAppend {program residual : FreeM P α}
    (spine : Spine program residual)
    (suffix : Path program → FreeM P β) :
    (spine.liftAppend suffix).length = spine.length := by
  induction spine with
  | root => rfl
  | down answer tail ih =>
      exact congrArg (· + 1) (ih (fun path => suffix ⟨answer, path⟩))

@[simp]
theorem trace_liftAppend {program residual : FreeM P α}
    (spine : Spine program residual)
    (suffix : Path program → FreeM P β) :
    (spine.liftAppend suffix).trace = spine.trace := by
  induction spine with
  | root => rfl
  | down answer tail ih =>
      exact congrArg (List.cons ⟨_, answer⟩)
        (ih (fun path => suffix ⟨answer, path⟩))

/-- Follow a complete prefix path before a cursor spine in its selected suffix. -/
def joinRight : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → {residual : FreeM P β} →
    Spine (suffix path) residual → Spine (FreeM.append program suffix) residual
  | .pure _, _, ⟨⟩, _, spine => spine
  | .liftBind _ next, suffix, ⟨answer, path⟩, _, spine =>
      .down answer
        (joinRight (next answer) (fun tail => suffix ⟨answer, tail⟩) path spine)

theorem joinRight_comp : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → {middle residual : FreeM P β} →
    (first : Spine (suffix path) middle) → (second : Spine middle residual) →
    joinRight program suffix path (first.comp second) =
      (joinRight program suffix path first).comp second
  | .pure _, _, ⟨⟩, _, _, _, _ => rfl
  | .liftBind _ next, suffix, ⟨answer, path⟩, _, _, first, second => by
      exact congrArg (Spine.down answer)
        (joinRight_comp (next answer) (fun tail => suffix ⟨answer, tail⟩)
          path first second)

@[simp]
theorem trace_joinRight : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → {residual : FreeM P β} →
    (spine : Spine (suffix path) residual) →
    (spine.joinRight program suffix path).trace =
      List.append (Path.trace program path) spine.trace
  | .pure _, _, ⟨⟩, _, _ => rfl
  | .liftBind _ next, suffix, ⟨answer, path⟩, _, spine => by
      exact congrArg (List.cons ⟨_, answer⟩)
        (trace_joinRight (next answer) (fun tail => suffix ⟨answer, tail⟩)
          path spine)

theorem plug_joinRight : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → {residual : FreeM P β} →
    (spine : Spine (suffix path) residual) → (tail : Path residual) →
    (spine.joinRight program suffix path).plug tail =
      Path.append program suffix path (spine.plug tail)
  | .pure _, _, ⟨⟩, _, _, _ => rfl
  | .liftBind _ next, suffix, ⟨answer, path⟩, _, spine, tail => by
      exact congrArg
        (fun rest => (⟨answer, rest⟩ : Path (FreeM.append (.liftBind _ next) suffix)))
        (plug_joinRight (next answer) (fun rest => suffix ⟨answer, rest⟩)
          path spine tail)

end Spine

/-- Transport a cursor through dependent `FreeM.append`. -/
def liftAppend {program : FreeM P α} (cursor : Cursor program)
    (suffix : Path program → FreeM P β) :
    Cursor (FreeM.append program suffix) :=
  ⟨FreeM.append cursor.residual (fun path => suffix (cursor.plug path)),
    cursor.spine.liftAppend suffix⟩

@[simp]
theorem residual_liftAppend {program : FreeM P α} (cursor : Cursor program)
    (suffix : Path program → FreeM P β) :
    (cursor.liftAppend suffix).residual =
      FreeM.append cursor.residual (fun path => suffix (cursor.plug path)) :=
  rfl

@[simp]
theorem liftAppend_root (program : FreeM P α)
    (suffix : Path program → FreeM P β) :
    (Cursor.root program).liftAppend suffix =
      Cursor.root (FreeM.append program suffix) :=
  rfl

@[simp]
theorem liftAppend_down {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer))
    (suffix : Path (FreeM.liftBind a next) → FreeM P β) :
    (Cursor.down answer tail).liftAppend suffix =
      Cursor.down answer
        (tail.liftAppend (fun path => suffix ⟨answer, path⟩)) :=
  rfl

@[simp]
theorem length_liftAppend {program : FreeM P α} (cursor : Cursor program)
    (suffix : Path program → FreeM P β) :
    (cursor.liftAppend suffix).length = cursor.length :=
  Spine.length_liftAppend cursor.spine suffix

@[simp]
theorem trace_liftAppend {program : FreeM P α} (cursor : Cursor program)
    (suffix : Path program → FreeM P β) :
    (cursor.liftAppend suffix).trace = cursor.trace :=
  Spine.trace_liftAppend cursor.spine suffix

theorem liftAppend_comp {program : FreeM P α} (first : Cursor program)
    (second : Cursor first.residual)
    (suffix : Path program → FreeM P β) :
    (first.comp second).liftAppend suffix =
      (first.liftAppend suffix).comp
        (second.liftAppend (fun path => suffix (first.plug path))) := by
  rcases first with ⟨middle, spine⟩
  induction spine with
  | root => rfl
  | @down a next residual answer tail ih =>
      change
        Cursor.down
            (next := fun b => FreeM.append (next b)
              (fun path => suffix ⟨b, path⟩)) answer
            (((⟨residual, tail⟩ : Cursor (next answer)).comp second).liftAppend
              (fun path => suffix ⟨answer, path⟩)) =
          Cursor.down
            (next := fun b => FreeM.append (next b)
              (fun path => suffix ⟨b, path⟩)) answer
            (((⟨residual, tail⟩ : Cursor (next answer)).liftAppend
                (fun path => suffix ⟨answer, path⟩)).comp
              (second.liftAppend
                (fun path => suffix ⟨answer,
                  (⟨residual, tail⟩ : Cursor (next answer)).plug path⟩)))
      exact congrArg
        (fun cursor => Cursor.down
          (next := fun b => FreeM.append (next b)
            (fun path => suffix ⟨b, path⟩)) answer cursor)
        (ih (fun path => suffix ⟨answer, path⟩) second)

/-- Follow a complete prefix path and continue with a cursor in its selected suffix. -/
def joinRight : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → Cursor (suffix path) →
    Cursor (FreeM.append program suffix)
  | program, suffix, path, cursor =>
      ⟨cursor.residual, cursor.spine.joinRight program suffix path⟩

@[simp]
theorem joinRight_pure (output : α)
    (suffix : Path (pure output : FreeM P α) → FreeM P β)
    (cursor : Cursor (suffix ⟨⟩)) :
    joinRight (pure output) suffix ⟨⟩ cursor = cursor :=
  rfl

theorem joinRight_liftBind {a : P.A} (next : P.B a → FreeM P α)
    (suffix : Path (FreeM.liftBind a next) → FreeM P β)
    (answer : P.B a) (path : Path (next answer))
    (cursor : Cursor (suffix ⟨answer, path⟩)) :
    joinRight (FreeM.liftBind a next) suffix ⟨answer, path⟩ cursor =
      Cursor.down answer
        (joinRight (next answer) (fun tail => suffix ⟨answer, tail⟩) path cursor) :=
  rfl

@[simp]
theorem residual_joinRight : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → (cursor : Cursor (suffix path)) →
    (joinRight program suffix path cursor).residual = cursor.residual
  | _, _, _, _ => rfl

theorem joinRight_comp : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → (first : Cursor (suffix path)) →
    (second : Cursor first.residual) →
    joinRight program suffix path (first.comp second) =
      (joinRight program suffix path first).comp second
  | program, suffix, path, ⟨_middle, firstSpine⟩, ⟨residual, secondSpine⟩ =>
      congrArg
        (fun spine =>
          (⟨residual, spine⟩ : Cursor (FreeM.append program suffix)))
        (Spine.joinRight_comp program suffix path firstSpine secondSpine)

@[simp]
theorem trace_joinRight : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → (cursor : Cursor (suffix path)) →
    (joinRight program suffix path cursor).trace =
      List.append (Path.trace program path) cursor.trace
  | program, suffix, path, cursor =>
      Spine.trace_joinRight program suffix path cursor.spine

@[simp]
theorem plug_joinRight (program : FreeM P α)
    (suffix : Path program → FreeM P β)
    (path : Path program) (cursor : Cursor (suffix path))
    (tail : Path cursor.residual) :
    (joinRight program suffix path cursor).plug tail =
      Path.append program suffix path (cursor.plug tail) :=
  Spine.plug_joinRight program suffix path cursor.spine tail

/-- Classification of a cursor through dependent append. -/
inductive AppendView (program : FreeM P α)
    (suffix : Path program → FreeM P β) : Type (max uA uB v w)
  | /-- The cursor remains within the prefix and stops at an internal residual. -/
    left (cursor : Cursor program) (isNode : IsNode cursor.residual)
  | /-- The cursor completed a prefix path and continues in the selected suffix. -/
    right (path : Path program) (cursor : Cursor (suffix path))

namespace AppendView

/-- Reconstruct the cursor represented by an append classification. -/
def join {program : FreeM P α} {suffix : Path program → FreeM P β} :
    AppendView program suffix → Cursor (FreeM.append program suffix)
  | .left cursor _ => cursor.liftAppend suffix
  | .right path cursor => joinRight program suffix path cursor

@[simp]
theorem join_left {program : FreeM P α} {suffix : Path program → FreeM P β}
    (cursor : Cursor program) (isNode : IsNode cursor.residual) :
    join (.left cursor isNode : AppendView program suffix) =
      cursor.liftAppend suffix :=
  rfl

@[simp]
theorem join_right {program : FreeM P α} {suffix : Path program → FreeM P β}
    (path : Path program) (cursor : Cursor (suffix path)) :
    join (.right path cursor : AppendView program suffix) =
      joinRight program suffix path cursor :=
  rfl

/-- Prepend one prefix edge to an append classification. -/
def prepend {a : P.A} {next : P.B a → FreeM P α}
    {suffix : Path (FreeM.liftBind a next) → FreeM P β}
    (answer : P.B a) :
    AppendView (next answer) (fun path => suffix ⟨answer, path⟩) →
      AppendView (FreeM.liftBind a next) suffix
  | .left cursor isNode => .left (Cursor.down answer cursor) isNode
  | .right path cursor => .right ⟨answer, path⟩ cursor

@[simp]
theorem join_prepend {a : P.A} {next : P.B a → FreeM P α}
    {suffix : Path (FreeM.liftBind a next) → FreeM P β}
    (answer : P.B a) :
    (view : AppendView (next answer) (fun path => suffix ⟨answer, path⟩)) →
    (prepend answer view).join =
      Cursor.down
        (next := fun b => FreeM.append (next b)
          (fun path => suffix ⟨b, path⟩)) answer view.join
  | .left _ _ => rfl
  | .right _ _ => rfl

end AppendView

/-- Classify a cursor through dependent append into the prefix or suffix case. -/
def split : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    Cursor (FreeM.append program suffix) → AppendView program suffix
  | .pure _, _, cursor => .right ⟨⟩ cursor
  | .liftBind a next, suffix, ⟨_, .root _⟩ =>
      .left (Cursor.root (FreeM.liftBind a next)) (.liftBind a next)
  | .liftBind _ next, suffix, ⟨_, .down answer tail⟩ =>
      AppendView.prepend answer
        (split (next answer) (fun path => suffix ⟨answer, path⟩) ⟨_, tail⟩)

theorem split_down {a : P.A} (next : P.B a → FreeM P α)
    (suffix : Path (FreeM.liftBind a next) → FreeM P β)
    (answer : P.B a)
    (tail : Cursor (FreeM.append (next answer)
      (fun path => suffix ⟨answer, path⟩))) :
    split (FreeM.liftBind a next) suffix (Cursor.down answer tail) =
      AppendView.prepend answer
        (split (next answer) (fun path => suffix ⟨answer, path⟩) tail) :=
  rfl

@[simp]
theorem split_pure (output : α)
    (suffix : Path (pure output : FreeM P α) → FreeM P β)
    (cursor : Cursor (suffix ⟨⟩)) :
    split (pure output) suffix cursor = .right ⟨⟩ cursor :=
  rfl

theorem split_root_liftBind {a : P.A} (next : P.B a → FreeM P α)
    (suffix : Path (FreeM.liftBind a next) → FreeM P β) :
    split (FreeM.liftBind a next) suffix
      (Cursor.root (FreeM.append (FreeM.liftBind a next) suffix)) =
      .left (Cursor.root (FreeM.liftBind a next)) (.liftBind a next) :=
  rfl

theorem join_split : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (cursor : Cursor (FreeM.append program suffix)) →
    (split program suffix cursor).join = cursor
  | .pure _, _, _ => rfl
  | .liftBind _ _, _, ⟨_, .root _⟩ => rfl
  | .liftBind _ next, suffix, ⟨residual, .down answer tail⟩ => by
      change
        (AppendView.prepend answer
          (split (next answer) (fun path => suffix ⟨answer, path⟩)
            (⟨residual, tail⟩ : Cursor _))).join =
          Cursor.down
            (next := fun b => FreeM.append (next b)
              (fun path => suffix ⟨b, path⟩)) answer
            (⟨residual, tail⟩ : Cursor _)
      rw [AppendView.join_prepend]
      exact congrArg
        (fun tailCursor => Cursor.down
          (next := fun b => FreeM.append (next b)
            (fun path => suffix ⟨b, path⟩)) answer tailCursor)
        (join_split (next answer) (fun path => suffix ⟨answer, path⟩) ⟨_, tail⟩)

theorem split_liftAppend_of_isNode {program : FreeM P α}
    (suffix : Path program → FreeM P β) (cursor : Cursor program)
    (isNode : IsNode cursor.residual) :
    split program suffix (cursor.liftAppend suffix) = .left cursor isNode := by
  rcases cursor with ⟨residual, spine⟩
  induction spine with
  | root =>
      cases isNode
      rfl
  | @down a next residual answer tail ih =>
      change
        split (FreeM.liftBind a next) suffix
            (Cursor.down
              (next := fun b => FreeM.append (next b)
                (fun path => suffix ⟨b, path⟩)) answer
              ((⟨residual, tail⟩ : Cursor (next answer)).liftAppend
                (fun path => suffix ⟨answer, path⟩))) =
          .left (Cursor.down (next := next) answer ⟨residual, tail⟩) isNode
      rw [split_down]
      rw [ih (fun path => suffix ⟨answer, path⟩) isNode]
      rfl

theorem split_joinRight : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → (cursor : Cursor (suffix path)) →
    split program suffix (joinRight program suffix path cursor) =
      .right path cursor
  | .pure _, _, ⟨⟩, _ => rfl
  | .liftBind _ next, suffix, ⟨answer, path⟩, cursor => by
      rw [joinRight_liftBind, split_down]
      rw [split_joinRight (next answer) (fun tail => suffix ⟨answer, tail⟩)]
      rfl

@[simp]
theorem split_join {program : FreeM P α}
    {suffix : Path program → FreeM P β}
    (view : AppendView program suffix) :
    split program suffix view.join = view := by
  cases view with
  | left cursor isNode => exact split_liftAppend_of_isNode suffix cursor isNode
  | right path cursor => exact split_joinRight program suffix path cursor

theorem joinRight_ofPath : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → (suffixPath : Path (suffix path)) →
    joinRight program suffix path (Cursor.ofPath (suffix path) suffixPath) =
      Cursor.ofPath (FreeM.append program suffix)
        (Path.append program suffix path suffixPath)
  | .pure _, _, ⟨⟩, _ => rfl
  | .liftBind _ next, suffix, ⟨answer, path⟩, suffixPath => by
      exact congrArg
        (fun cursor => Cursor.down
          (next := fun b => FreeM.append (next b)
            (fun tail => suffix ⟨b, tail⟩)) answer cursor)
        (joinRight_ofPath (next answer)
          (fun tail => suffix ⟨answer, tail⟩) path suffixPath)

theorem split_ofPath_append {program : FreeM P α}
    (suffix : Path program → FreeM P β)
    (path : Path program) (suffixPath : Path (suffix path)) :
    split program suffix
      (Cursor.ofPath (FreeM.append program suffix)
        (Path.append program suffix path suffixPath)) =
      .right path (Cursor.ofPath (suffix path) suffixPath) := by
  rw [← joinRight_ofPath]
  exact split_joinRight program suffix path _

end Cursor

/-! ## Decoration compatibility -/

namespace Displayed
namespace Decoration

variable {Γ : P.A → Type w₂}

theorem restrict_liftAppend : {program : FreeM P α} →
    (suffix : Path program → FreeM P β) →
    (cursor : Cursor program) →
    (d₁ : Displayed.Decoration Γ program) →
    (d₂ : (path : Path program) → Displayed.Decoration Γ (suffix path)) →
    Decoration.restrict (cursor.liftAppend suffix)
      (Decoration.append d₁ d₂) =
      Decoration.append (Decoration.restrict cursor d₁)
        (fun path => d₂ (cursor.plug path))
  | _, _, ⟨_, .root _⟩, _, _ => rfl
  | _, suffix, ⟨_, .down answer tail⟩, d₁, d₂ =>
      restrict_liftAppend (fun path => suffix ⟨answer, path⟩) ⟨_, tail⟩
        (d₁.2 answer) (fun path => d₂ ⟨answer, path⟩)

theorem restrict_joinRight : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → (cursor : Cursor (suffix path)) →
    (d₁ : Displayed.Decoration Γ program) →
    (d₂ : (prefixPath : Path program) → Displayed.Decoration Γ (suffix prefixPath)) →
    Decoration.restrict (Cursor.joinRight program suffix path cursor)
      (Decoration.append d₁ d₂) =
      Decoration.restrict cursor (d₂ path)
  | .pure _, _, ⟨⟩, _, _, _ => rfl
  | .liftBind _ next, suffix, ⟨answer, path⟩, cursor, d₁, d₂ =>
      restrict_joinRight (next answer) (fun tail => suffix ⟨answer, tail⟩)
        path cursor (d₁.2 answer) (fun tail => d₂ ⟨answer, tail⟩)

namespace Over

variable {A : (a : P.A) → Γ a → Type w₃}

theorem restrict_liftAppend : {program : FreeM P α} →
    (suffix : Path program → FreeM P β) →
    (cursor : Cursor program) →
    (d₁ : Displayed.Decoration Γ program) →
    (d₂ : (path : Path program) → Displayed.Decoration Γ (suffix path)) →
    (r₁ : Displayed.Decoration.Over Γ A program d₁) →
    (r₂ : (path : Path program) → Displayed.Decoration.Over Γ A (suffix path) (d₂ path)) →
    HEq
      (Decoration.Over.restrict (cursor.liftAppend suffix)
        (Decoration.append d₁ d₂)
        (Decoration.Over.append r₁ r₂))
      (Decoration.Over.append
        (Decoration.Over.restrict cursor d₁ r₁)
        (fun path => r₂ (cursor.plug path)))
  | _, _, ⟨_, .root _⟩, _, _, _, _ => HEq.rfl
  | _, suffix, ⟨_, .down answer tail⟩, d₁, d₂, r₁, r₂ =>
      restrict_liftAppend (fun path => suffix ⟨answer, path⟩) ⟨_, tail⟩
        (d₁.2 answer) (fun path => d₂ ⟨answer, path⟩)
        (r₁.2 answer) (fun path => r₂ ⟨answer, path⟩)

theorem restrict_joinRight : (program : FreeM P α) →
    (suffix : Path program → FreeM P β) →
    (path : Path program) → (cursor : Cursor (suffix path)) →
    (d₁ : Displayed.Decoration Γ program) →
    (d₂ : (prefixPath : Path program) → Displayed.Decoration Γ (suffix prefixPath)) →
    (r₁ : Displayed.Decoration.Over Γ A program d₁) →
    (r₂ : (prefixPath : Path program) →
      Displayed.Decoration.Over Γ A (suffix prefixPath) (d₂ prefixPath)) →
    HEq
      (Decoration.Over.restrict (Cursor.joinRight program suffix path cursor)
        (Decoration.append d₁ d₂)
        (Decoration.Over.append r₁ r₂))
      (Decoration.Over.restrict cursor (d₂ path) (r₂ path))
  | .pure _, _, ⟨⟩, _, _, _, _, _ => HEq.rfl
  | .liftBind _ next, suffix, ⟨answer, path⟩, cursor, d₁, d₂, r₁, r₂ =>
      restrict_joinRight (next answer) (fun tail => suffix ⟨answer, tail⟩)
        path cursor (d₁.2 answer) (fun tail => d₂ ⟨answer, tail⟩)
        (r₁.2 answer) (fun tail => r₂ ⟨answer, tail⟩)

end Over

end Decoration
end Displayed
end FreeM
end PFunctor
