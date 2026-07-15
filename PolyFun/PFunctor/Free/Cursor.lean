/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Path
public import PolyFun.PFunctor.Trace

/-!
# Cursors into free polynomial programs

A `FreeM.Cursor program` is a finite typed path prefix through `program`. Unlike
a `FreeM.Path`, a cursor may stop at the root or at any internal subtree. Its
`residual` is the subtree selected by the prefix.

Cursors compose by continuing from the selected residual. Terminal cursors are
exactly complete root-to-leaf paths, while `Cursor.Edge` records one immediate
descent. These are structural objects: they do not execute the program or
attach protocol-specific meaning to the visited prefix.
-/

@[expose] public section

universe uA uB v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

namespace Cursor

/-- The typed spine of a cursor, indexed by its source program and selected
residual. Keeping the residual as an index makes composition preserve it
definitionally. -/
inductive Spine : (program residual : FreeM P α) → Type (max uA uB v)
  | root (program : FreeM P α) : Spine program program
  | down {a : P.A} {next : P.B a → FreeM P α} {residual : FreeM P α}
      (answer : P.B a) (tail : Spine (next answer) residual) :
      Spine (FreeM.liftBind a next) residual

namespace Spine

variable {program middle residual suffix : FreeM P α}

/-- Compose typed cursor spines. -/
def comp : {program middle residual : FreeM P α} →
    Spine program middle → Spine middle residual → Spine program residual
  | _, _, _, .root _, suffix => suffix
  | _, _, _, .down answer tail, suffix => .down answer (tail.comp suffix)

@[simp]
theorem root_comp (suffix : Spine program residual) :
    (Spine.root program).comp suffix = suffix :=
  rfl

@[simp]
theorem comp_root (spine : Spine program residual) :
    spine.comp (Spine.root residual) = spine := by
  induction spine with
  | root => rfl
  | down answer tail ih =>
      change Spine.down answer (tail.comp (Spine.root _)) = Spine.down answer tail
      rw [ih]

@[simp]
theorem comp_assoc (first : Spine program middle)
    (second : Spine middle residual) (third : Spine residual suffix) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  induction first with
  | root => rfl
  | down answer tail ih =>
      change Spine.down answer ((tail.comp second).comp third) =
        Spine.down answer (tail.comp (second.comp third))
      rw [ih]

/-- Number of edges in a cursor spine. -/
def length : {program residual : FreeM P α} → Spine program residual → Nat
  | _, _, .root _ => 0
  | _, _, .down _ tail => tail.length + 1

@[simp]
theorem length_root (program : FreeM P α) :
    (Spine.root program).length = 0 :=
  rfl

@[simp]
theorem length_down {a : P.A} {next : P.B a → FreeM P α}
    {residual : FreeM P α} (answer : P.B a)
    (tail : Spine (next answer) residual) :
    (Spine.down answer tail).length = tail.length + 1 :=
  rfl

@[simp]
theorem length_comp (first : Spine program middle)
    (second : Spine middle residual) :
    (first.comp second).length = first.length + second.length := by
  induction first with
  | root => simp only [comp, length, Nat.zero_add]
  | down answer tail ih =>
      change (tail.comp second).length + 1 = tail.length + 1 + second.length
      rw [ih]
      omega

/-- Erased events visited by a cursor spine. -/
def trace : {program residual : FreeM P α} →
    Spine program residual → PFunctor.TraceList P
  | _, _, .root _ => []
  | _, _, .down (a := a) answer tail => (⟨a, answer⟩ : P.Idx) :: tail.trace

@[simp]
theorem trace_root (program : FreeM P α) :
    (Spine.root program).trace = [] :=
  rfl

@[simp]
theorem trace_down {a : P.A} {next : P.B a → FreeM P α}
    {residual : FreeM P α} (answer : P.B a)
    (tail : Spine (next answer) residual) :
    (Spine.down answer tail).trace = (⟨a, answer⟩ : P.Idx) :: tail.trace :=
  rfl

@[simp]
theorem trace_comp (first : Spine program middle)
    (second : Spine middle residual) :
    (first.comp second).trace = List.append first.trace second.trace := by
  induction first with
  | root => rfl
  | down answer tail ih =>
      change (⟨_, answer⟩ : P.Idx) :: (tail.comp second).trace =
        List.append ((⟨_, answer⟩ : P.Idx) :: tail.trace) second.trace
      rw [ih]
      rfl

theorem length_eq_trace_length (spine : Spine program residual) :
    spine.length = FreeMonoid.length spine.trace := by
  induction spine with
  | root => rfl
  | down answer tail ih =>
      change tail.length + 1 = FreeMonoid.length (_ :: tail.trace)
      change tail.length + 1 = FreeMonoid.length tail.trace + 1
      rw [ih]

/-- Plug a complete path through the residual back through a cursor spine. -/
def plug : {program residual : FreeM P α} →
    Spine program residual → Path residual → Path program
  | _, _, .root _, path => path
  | _, _, .down answer tail, path => ⟨answer, tail.plug path⟩

@[simp]
theorem plug_root (program : FreeM P α) (path : Path program) :
    (Spine.root program).plug path = path :=
  rfl

@[simp]
theorem plug_down {a : P.A} {next : P.B a → FreeM P α}
    {residual : FreeM P α} (answer : P.B a)
    (tail : Spine (next answer) residual) (path : Path residual) :
    (Spine.down answer tail).plug path = ⟨answer, tail.plug path⟩ :=
  rfl

@[simp]
theorem plug_comp (first : Spine program middle)
    (second : Spine middle residual) (path : Path residual) :
    (first.comp second).plug path = first.plug (second.plug path) := by
  induction first with
  | root => rfl
  | down answer tail ih =>
      rw [comp, plug_down, plug_down, ih]

@[simp]
theorem output_plug (spine : Spine program residual) (path : Path residual) :
    output program (spine.plug path) = output residual path := by
  induction spine with
  | root => rfl
  | down answer tail ih =>
      exact ih path

end Spine

end Cursor

/-- A finite typed path prefix selecting a residual subtree of a free
polynomial program. -/
structure Cursor (program : FreeM P α) where
  /-- The subtree selected by the cursor. -/
  residual : FreeM P α
  /-- Typed evidence that the residual occurs below `program`. -/
  spine : Cursor.Spine program residual

namespace Cursor

variable {program middle residual suffix : FreeM P α}

/-- The cursor that stops at the root. -/
def root (program : FreeM P α) : Cursor program :=
  ⟨program, Spine.root program⟩

/-- Prepend one typed descent to a cursor. -/
def down {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer)) :
    Cursor (FreeM.liftBind a next) :=
  ⟨tail.residual, Spine.down answer tail.spine⟩

@[simp]
theorem residual_root (program : FreeM P α) :
    (root program).residual = program :=
  rfl

@[simp]
theorem residual_down {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer)) :
    (down answer tail).residual = tail.residual :=
  rfl

/-- Continue a cursor with another cursor rooted at its selected residual. -/
def comp (cursor : Cursor program) (continuation : Cursor cursor.residual) :
    Cursor program :=
  ⟨continuation.residual, cursor.spine.comp continuation.spine⟩

@[simp]
theorem residual_comp (cursor : Cursor program)
    (continuation : Cursor cursor.residual) :
    (cursor.comp continuation).residual = continuation.residual :=
  rfl

@[simp]
theorem root_comp (continuation : Cursor program) :
    (root program).comp continuation = continuation :=
  rfl

@[simp]
theorem down_comp {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer))
    (continuation : Cursor tail.residual) :
    (down answer tail).comp continuation = down answer (tail.comp continuation) :=
  rfl

@[simp]
theorem comp_root (cursor : Cursor program) :
    cursor.comp (root cursor.residual) = cursor := by
  cases cursor with
  | mk residual spine =>
      simp only [comp, root, Spine.comp_root]

@[simp]
theorem comp_assoc (first : Cursor program) (second : Cursor first.residual)
    (third : Cursor second.residual) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  cases first with
  | mk firstResidual firstSpine =>
      cases second with
      | mk secondResidual secondSpine =>
          cases third with
          | mk thirdResidual thirdSpine =>
              simp only [comp, Spine.comp_assoc]

/-- Number of edges in a cursor. -/
def length (cursor : Cursor program) : Nat :=
  cursor.spine.length

@[simp]
theorem length_root (program : FreeM P α) : (root program).length = 0 :=
  rfl

@[simp]
theorem length_down {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer)) :
    (down answer tail).length = tail.length + 1 :=
  rfl

@[simp]
theorem length_comp (first : Cursor program) (second : Cursor first.residual) :
    (first.comp second).length = first.length + second.length :=
  Spine.length_comp first.spine second.spine

/-- Erased events visited before the selected residual. -/
def trace (cursor : Cursor program) : PFunctor.TraceList P :=
  cursor.spine.trace

@[simp]
theorem trace_root (program : FreeM P α) : (root program).trace = [] :=
  rfl

@[simp]
theorem trace_down {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer)) :
    (down answer tail).trace = ⟨a, answer⟩ :: tail.trace :=
  rfl

@[simp]
theorem trace_comp (first : Cursor program) (second : Cursor first.residual) :
    (first.comp second).trace = List.append first.trace second.trace :=
  Spine.trace_comp first.spine second.spine

theorem length_eq_trace_length (cursor : Cursor program) :
    cursor.length = FreeMonoid.length cursor.trace :=
  Spine.length_eq_trace_length cursor.spine

/-- Plug a complete residual path back into the source program. -/
def plug (cursor : Cursor program) : Path cursor.residual → Path program :=
  cursor.spine.plug

@[simp]
theorem plug_root (program : FreeM P α) (path : Path program) :
    (root program).plug path = path :=
  rfl

@[simp]
theorem plug_down {a : P.A} {next : P.B a → FreeM P α}
    (answer : P.B a) (tail : Cursor (next answer))
    (path : Path tail.residual) :
    (down answer tail).plug path = ⟨answer, tail.plug path⟩ :=
  rfl

@[simp]
theorem plug_comp (first : Cursor program) (second : Cursor first.residual)
    (path : Path second.residual) :
    (first.comp second).plug path = first.plug (second.plug path) :=
  Spine.plug_comp first.spine second.spine path

@[simp]
theorem output_plug (cursor : Cursor program) (path : Path cursor.residual) :
    output program (cursor.plug path) = output cursor.residual path :=
  Spine.output_plug cursor.spine path

/-! ## Immediate edges and extension witnesses -/

namespace Edge

/-- Evidence for one immediate descent and its selected child. -/
inductive Witness : (program residual : FreeM P α) → Type (max uA uB v)
  | down {a : P.A} {next : P.B a → FreeM P α} (answer : P.B a) :
      Witness (FreeM.liftBind a next) (next answer)

end Edge

/-- A one-edge cursor with its residual exposed definitionally. -/
structure Edge (program : FreeM P α) where
  /-- Child selected by the edge. -/
  residual : FreeM P α
  /-- Typed evidence for the immediate descent. -/
  witness : Edge.Witness program residual

namespace Edge

/-- Select one immediate child of an internal node. -/
def down {a : P.A} {next : P.B a → FreeM P α} (answer : P.B a) :
    Edge (FreeM.liftBind a next) :=
  ⟨next answer, Witness.down answer⟩

/-- Regard an immediate edge as a cursor. -/
def toCursor : {program : FreeM P α} → (edge : Edge program) → Cursor program
  | _, ⟨_, .down (next := next) answer⟩ =>
      Cursor.down answer (Cursor.root (next answer))

@[simp]
theorem residual_toCursor (edge : Edge program) :
    edge.toCursor.residual = edge.residual := by
  cases edge with
  | mk residual witness => cases witness; rfl

@[simp]
theorem length_toCursor (edge : Edge program) :
    edge.toCursor.length = 1 := by
  cases edge with
  | mk residual witness => cases witness; rfl

end Edge

/-- Witness that `later` continues `earlier` from its selected residual. -/
structure Extends (earlier later : Cursor program) : Type (max uA uB v) where
  /-- Continuation from the earlier cursor's residual. -/
  continuation : Cursor earlier.residual
  /-- Composing the continuation gives the later cursor. -/
  comp_eq : earlier.comp continuation = later

/-- Witness that `later` is exactly one edge beyond `earlier`. -/
structure ExtendsByOne (earlier later : Cursor program) : Type (max uA uB v) where
  /-- Immediate edge below the earlier cursor. -/
  edge : Edge earlier.residual
  /-- Composing the edge gives the later cursor. -/
  comp_eq : earlier.comp edge.toCursor = later

/-! ## Terminal cursors and complete paths -/

/-- A cursor is terminal when its residual is a leaf. -/
def IsTerminal (cursor : Cursor program) : Prop :=
  ∃ output : α, cursor.residual = FreeM.pure output

/-- The terminal cursor selected by a complete path. -/
def ofPath : (program : FreeM P α) → Path program → Cursor program
  | .pure output, _ => root (FreeM.pure output)
  | .liftBind _ next, ⟨answer, tail⟩ => down answer (ofPath (next answer) tail)

@[simp]
theorem residual_ofPath : (program : FreeM P α) → (path : Path program) →
    (ofPath program path).residual = FreeM.pure (output program path)
  | .pure _, _ => rfl
  | .liftBind _ next, ⟨answer, tail⟩ => residual_ofPath (next answer) tail

@[simp]
theorem ofPath_plug (cursor : Cursor program) (path : Path cursor.residual) :
    ofPath program (cursor.plug path) = cursor.comp (ofPath cursor.residual path) := by
  cases cursor with
  | mk residual spine =>
      induction spine with
      | root => rfl
      | down answer tail ih =>
          change down answer (ofPath _ (tail.plug path)) =
            down answer ((⟨_, tail⟩ : Cursor _).comp (ofPath _ path))
          simpa [plug, comp] using congrArg (down answer) (ih path)

/-- A terminal cursor together with its selected leaf payload. -/
structure Terminal (program : FreeM P α) where
  /-- Complete cursor ending at a leaf. -/
  cursor : Cursor program
  /-- Payload stored at the selected leaf. -/
  output : α
  /-- The selected residual is exactly that leaf. -/
  residual_eq : cursor.residual = FreeM.pure output

namespace Terminal

@[ext]
theorem ext {left right : Terminal program}
    (cursor_eq : left.cursor = right.cursor)
    (output_eq : left.output = right.output) : left = right := by
  cases left with
  | mk leftCursor leftOutput leftResidual =>
      cases right with
      | mk rightCursor rightOutput rightResidual =>
          cases cursor_eq
          cases output_eq
          have residual_eq : leftResidual = rightResidual := Subsingleton.elim _ _
          cases residual_eq
          rfl

/-- A terminal cursor satisfies `Cursor.IsTerminal`. -/
theorem isTerminal (terminal : Terminal program) : terminal.cursor.IsTerminal :=
  ⟨terminal.output, terminal.residual_eq⟩

/-- The unique path through the selected leaf residual. -/
def residualPath (terminal : Terminal program) : Path terminal.cursor.residual :=
  terminal.residual_eq.symm ▸
    (⟨⟩ : Path (FreeM.pure (P := P) terminal.output))

@[simp]
theorem ofPath_residualPath (terminal : Terminal program) :
    ofPath terminal.cursor.residual terminal.residualPath = root terminal.cursor.residual := by
  cases terminal with
  | mk cursor leaf residual_eq =>
      cases cursor with
      | mk residual spine =>
          dsimp at residual_eq ⊢
          subst residual
          rfl

end Terminal

/-- Convert a complete path to the corresponding terminal cursor. -/
def terminalOfPath : (program : FreeM P α) → Path program → Terminal program
  | .pure output, _ =>
      ⟨root (FreeM.pure output), output, rfl⟩
  | .liftBind _ next, ⟨answer, tail⟩ =>
      let terminal := terminalOfPath (next answer) tail
      ⟨down answer terminal.cursor, terminal.output, terminal.residual_eq⟩

/-- Convert a terminal cursor to its complete path. -/
def pathOfTerminal (terminal : Terminal program) : Path program :=
  terminal.cursor.plug terminal.residualPath

@[simp]
theorem terminalOfPath_cursor : (program : FreeM P α) → (path : Path program) →
    (terminalOfPath program path).cursor = ofPath program path
  | .pure _, _ => rfl
  | .liftBind _ next, ⟨answer, tail⟩ => by
      change down answer (terminalOfPath (next answer) tail).cursor =
        down answer (ofPath (next answer) tail)
      rw [terminalOfPath_cursor]

@[simp]
theorem terminalOfPath_output : (program : FreeM P α) → (path : Path program) →
    (terminalOfPath program path).output = output program path
  | .pure _, _ => rfl
  | .liftBind _ next, ⟨answer, tail⟩ => terminalOfPath_output (next answer) tail

@[simp]
theorem pathOfTerminal_terminalOfPath :
    (program : FreeM P α) → (path : Path program) →
      pathOfTerminal (terminalOfPath program path) = path
  | .pure _, _ => rfl
  | .liftBind a next, ⟨answer, tail⟩ => by
      change (⟨answer, pathOfTerminal (terminalOfPath (next answer) tail)⟩ :
        Path (FreeM.liftBind a next)) = ⟨answer, tail⟩
      rw [pathOfTerminal_terminalOfPath]

@[simp]
theorem terminalOfPath_pathOfTerminal :
    (terminal : Terminal program) →
      terminalOfPath program (pathOfTerminal terminal) = terminal := by
  intro terminal
  have cursor_eq :
      (terminalOfPath program (pathOfTerminal terminal)).cursor = terminal.cursor := by
    rw [terminalOfPath_cursor]
    change ofPath program (terminal.cursor.plug terminal.residualPath) = terminal.cursor
    rw [ofPath_plug, Terminal.ofPath_residualPath, comp_root]
  have output_eq :
      (terminalOfPath program (pathOfTerminal terminal)).output = terminal.output := by
    rw [terminalOfPath_output]
    change output program (terminal.cursor.plug terminal.residualPath) = terminal.output
    rw [output_plug]
    cases terminal with
    | mk cursor leaf residual_eq =>
        cases cursor with
        | mk residual spine =>
            dsimp at residual_eq ⊢
            subst residual
            rfl
  exact Terminal.ext cursor_eq output_eq

/-- Terminal cursors are equivalent to complete paths. -/
def terminalEquivPath (program : FreeM P α) : Terminal program ≃ Path program where
  toFun := pathOfTerminal
  invFun := terminalOfPath program
  left_inv := terminalOfPath_pathOfTerminal
  right_inv := pathOfTerminal_terminalOfPath program

theorem terminal_output_eq_path_output (terminal : Terminal program) :
    terminal.output = output program (pathOfTerminal terminal) := by
  change terminal.output = output program (terminal.cursor.plug terminal.residualPath)
  rw [output_plug]
  cases terminal with
  | mk cursor leaf residual_eq =>
      cases cursor with
      | mk residual spine =>
          dsimp at residual_eq ⊢
          subst residual
          rfl

end Cursor

end PFunctor.FreeM
