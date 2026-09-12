/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Path
public import PolyFun.PFunctor.Trace

/-!
# Executing paths through free polynomial programs

This file equips a free polynomial program with its canonical path-producing
execution and erases completed paths to polynomial traces. The constructions
are structural and independent of any interpretation of the polynomial.
-/

@[expose] public section

universe uA uB v w

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

/- Lean compares path indices over `liftBind` at implicit transparency. -/
attribute [local implicit_reducible] FreeM.bind FreeMonoid

/-- Execute a free program while returning the typed path selected by the
answers received during that execution. -/
def withPath : (program : FreeM P α) → FreeM P (Path program)
  | .pure _ => pure ⟨⟩
  | .liftBind a next =>
      FreeM.liftBind a fun answer =>
        FreeM.map (fun path : Path (next answer) =>
          (⟨answer, path⟩ : Path (FreeM.liftBind a next))) (withPath (next answer))

@[simp] theorem withPath_pure (x : α) :
    withPath (pure x : FreeM P α) = pure ⟨⟩ := rfl

@[simp] theorem withPath_liftBind (a : P.A) (next : P.B a → FreeM P α) :
    withPath (FreeM.liftBind a next) =
      FreeM.liftBind a fun answer =>
        FreeM.map (fun path : Path (next answer) =>
          (⟨answer, path⟩ : Path (FreeM.liftBind a next))) (withPath (next answer)) := rfl

/-- Forget the dependent path returned by `withPath`, retaining the selected
leaf payload. This recovers the original program exactly. -/
@[simp] theorem map_output_withPath : (program : FreeM P α) →
    FreeM.map (output program) (withPath program) = program
  | .pure _ => rfl
  | .liftBind a next => by
      simp only [withPath, FreeM.map]
      apply congrArg (FreeM.liftBind a)
      funext answer
      rw [← FreeM.comp_map]
      exact map_output_withPath (next answer)

/-- Binding after path execution exposes the root answer and tail path
without leaving a dependent `map` in the term. -/
theorem withPath_liftBind_bind {γ : Type w} (a : P.A)
    (next : P.B a → FreeM P α)
    (k : Path (FreeM.liftBind a next) → FreeM P γ) :
    FreeM.bind (withPath (FreeM.liftBind a next)) k =
      FreeM.liftBind a fun answer =>
        FreeM.bind (withPath (next answer)) fun suffix =>
          k (⟨answer, suffix⟩ : Path (FreeM.liftBind a next)) := by
  change FreeM.liftBind a (fun answer =>
      FreeM.bind
        (FreeM.map (fun path : Path (next answer) =>
          (⟨answer, path⟩ : Path (FreeM.liftBind a next)))
          (withPath (next answer))) k) = _
  apply congrArg (FreeM.liftBind a)
  funext answer
  rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
  rfl

namespace Path

/-- Erase a typed path to the universal list of polynomial events. -/
def trace : (program : FreeM P α) → Path program → PFunctor.TraceList P
  | .pure _, _ => []
  | .liftBind a next, ⟨answer, tail⟩ =>
      ⟨a, answer⟩ :: trace (next answer) tail

@[simp] theorem trace_pure (x : α) (path : Path (pure x : FreeM P α)) :
    trace (pure x) path = [] := rfl

/- The path constructor's hidden direction type specializes when the polynomial is concrete.
Index the query constructor and leave dependent path matching to the unifier. -/

@[simp] theorem trace_liftBind (a : P.A) (next : P.B a → FreeM P α)
    (answer : P.B a) (tail : Path (next answer)) :
    trace (FreeM.liftBind a next) (no_index ⟨answer, tail⟩) =
      ⟨a, answer⟩ :: trace (next answer) tail := rfl

/-- The visited input positions of a typed execution path, preserving their order and repeats. -/
def positions (program : FreeM P α) (path : Path program) : List P.A :=
  TraceList.positions (trace program path)

@[simp]
theorem positions_pure (x : α) (path : Path (pure x : FreeM P α)) :
    positions (pure x) path = [] := rfl

@[simp]
theorem positions_liftBind (a : P.A) (next : P.B a → FreeM P α)
    (answer : P.B a) (tail : Path (next answer)) :
    positions (FreeM.liftBind a next) (no_index ⟨answer, tail⟩) =
      a :: positions (next answer) tail := rfl

/-- Agreement at the visited positions preserves deterministic execution, using the public
position projection instead of exposing the event carrier's representation. -/
theorem ofHandler_eq_of_agree_positions (choose choose' : (a : P.A) → P.B a)
    (program : FreeM P α)
    (h : ∀ a ∈ positions program (ofHandler choose program), choose' a = choose a) :
    ofHandler choose' program = ofHandler choose program := by
  induction program with
  | pure _ => rfl
  | lift_bind a next ih =>
      change ∀ a' ∈ a :: positions (next (choose a)) (ofHandler choose (next (choose a))),
        choose' a' = choose a' at h
      have ha := h a (List.mem_cons_self ..)
      change (⟨choose' a, ofHandler choose' (next (choose' a))⟩ : Path (FreeM.liftBind a next)) =
        ⟨choose a, ofHandler choose (next (choose a))⟩
      rw [ha]
      exact congrArg (fun path => (⟨choose a, path⟩ : Path (FreeM.liftBind a next)))
        (ih (choose a) fun a' ha' => h a' (List.mem_cons_of_mem a ha'))

/-- Number of operation-answer steps in a completed typed path. -/
def length : (program : FreeM P α) → Path program → Nat
  | .pure _, _ => 0
  | .liftBind _ next, ⟨answer, tail⟩ => length (next answer) tail + 1

@[simp] theorem length_pure (x : α) (path : Path (pure x : FreeM P α)) :
    length (pure x) path = 0 := rfl

@[simp] theorem length_liftBind (a : P.A) (next : P.B a → FreeM P α)
    (answer : P.B a) (tail : Path (next answer)) :
    length (FreeM.liftBind a next) (no_index ⟨answer, tail⟩) =
      length (next answer) tail + 1 := rfl

/-- Relabelling the leaves of a free program does not change the length of a
path pulled back to the source program. -/
@[simp] theorem length_pullMap {β : Type w} (f : α → β) :
    (program : FreeM P α) → (path : Path (FreeM.map f program)) →
      length program (Path.pullMap f program path) =
        length (FreeM.map f program) path
  | .pure _, _ => rfl
  | .liftBind _ next, ⟨answer, tail⟩ => by
      change length (next answer) (Path.pullMap f (next answer) tail) + 1 =
        length (FreeM.map f (next answer)) tail + 1
      exact congrArg (fun n => n + 1) (length_pullMap f (next answer) tail)

/-- The typed path length agrees with the length of its erased event trace. -/
theorem length_eq_trace_length (program : FreeM P α) (path : Path program) :
    length program path = (trace program path).length := by
  induction program with
  | pure x => rfl
  | lift_bind a next ih =>
      rcases path with ⟨answer, tail⟩
      change length (next answer) tail + 1 =
        (trace (next answer) tail).length + 1
      exact congrArg (fun n => n + 1) (ih answer tail)

/-- Agreement on the operations visited by one deterministic execution preserves its entire
typed path. The alternative handler may differ arbitrarily on unvisited operations. -/
theorem ofHandler_eq_of_agree_trace (choose choose' : (a : P.A) → P.B a)
    (program : FreeM P α)
    (h : ∀ a ∈ (trace program (ofHandler choose program)).map Sigma.fst,
      choose' a = choose a) :
    ofHandler choose' program = ofHandler choose program := by
  apply ofHandler_eq_of_agree_positions
  intro a ha
  exact h a ha

end Path

/-- Reading the output of the path selected by a handler agrees with the ordinary monadic fold. -/
theorem output_ofHandler {α : Type uB} (choose : (a : P.A) → P.B a) (program : FreeM P α) :
    output program (Path.ofHandler choose program) =
      FreeM.liftM (m := Id) choose program := by
  induction program with
  | pure _ => rfl
  | lift_bind a next ih =>
      exact ih (choose a)

/-- Execute a free program while retaining only the number of steps in its
completed typed path. This is the nondependent length projection of
`withPath`. -/
def withPathLength (program : FreeM P α) : FreeM P Nat :=
  FreeM.map (Path.length program) (withPath program)

@[simp] theorem withPathLength_pure (x : α) :
    withPathLength (pure x : FreeM P α) = pure 0 := rfl

@[simp] theorem withPathLength_liftBind (a : P.A)
    (next : P.B a → FreeM P α) :
    withPathLength (FreeM.liftBind a next) =
      FreeM.liftBind a fun answer =>
        FreeM.map (fun length => length + 1) (withPathLength (next answer)) := by
  unfold withPathLength
  change FreeM.liftBind a (fun answer =>
      FreeM.map (Path.length (FreeM.liftBind a next))
        (FreeM.map (fun path : Path (next answer) =>
          (⟨answer, path⟩ : Path (FreeM.liftBind a next)))
          (withPath (next answer)))) =
    FreeM.liftBind a (fun answer =>
      FreeM.map (fun length => length + 1)
        (FreeM.map (Path.length (next answer)) (withPath (next answer))))
  apply congrArg (FreeM.liftBind a)
  funext answer
  rw [← FreeM.comp_map, ← FreeM.comp_map]
  apply congrArg (fun f => FreeM.map f (withPath (next answer)))
  funext tail
  rfl

end PFunctor.FreeM
