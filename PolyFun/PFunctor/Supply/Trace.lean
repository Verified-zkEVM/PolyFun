/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Supply
public import PolyFun.PFunctor.Free.Path.Execution
public import PolyFun.PFunctor.Trace

/-!
# What a run against a supply reads

`Supply.run` executes a program against a positional answer supply. `Supply.runPath` is that same
execution retaining the typed `FreeM.Path` it selected, so a run can be compared with the
path-indexed structures built on top of `Path` — cursors, occurrence contexts, fork views.
`run_eq_map_runPath` says the two agree: `run` is `runPath` followed by reading off the leaf.

The bridge those comparisons rest on is `getAt?_trace_runPath`: the answer a run took at the `n`-th
occurrence of a position is the supply's `n`-th answer there. Positional substitution on a supply is
therefore substitution at an occurrence of the executed trace, which is what makes `Supply.setAt` a
rewind primitive rather than an arbitrary edit. `getAt?_trace_runPath_setAt` states exactly that,
and `getAt?_trace_runPath_setAt_of_ne` states that every other answer the run takes is untouched —
the same shared-prefix property that `Cursor.ForkView` gets by construction from retaining its
occurrence context.

`apply_eq_drop_occurrences` is the accounting behind all of it: a run leaves behind exactly what it
did not read, so the supply that remains at a position is that position's list with as many answers
dropped as the trace has events there.
-/

@[expose] public section

universe uA uB v

namespace PFunctor

namespace Supply

/- Lean 4.33 compares assigned metavariable types at implicit transparency; the rewrites below move
between `TraceList` — reducibly `FreeMonoid (Idx _)` — and its `List` normal form.
`implicit_reducible` (unlike `reducible`) stays invisible to simp and instance search, and needs no
`allowUnsafeReducibility`. -/
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- `FreeM.Path.trace_liftBind` in the `liftBind` spelling the definitions below produce. -/
private theorem trace_liftBind' {a : P.A} (next : P.B a → FreeM P α) (answer : P.B a)
    (tail : FreeM.Path (next answer)) :
    FreeM.Path.trace (FreeM.liftBind a next) ⟨answer, tail⟩
      = (⟨a, answer⟩ : P.Idx) :: FreeM.Path.trace (next answer) tail := rfl

/-! ### Running for a path -/

variable [DecidableEq P.A]

/-- One event at the counted position. -/
private theorem occurrences_cons_self (a : P.A) (answer : P.B a) (tail : TraceList P) :
    TraceList.occurrences a ((⟨a, answer⟩ : P.Idx) :: tail)
      = TraceList.occurrences a tail + 1 := by
  simp [TraceList.occurrences]

/-- An event elsewhere is not counted. -/
private theorem occurrences_cons_of_ne {a b : P.A} (hb : b ≠ a) (answer : P.B a)
    (tail : TraceList P) :
    TraceList.occurrences b ((⟨a, answer⟩ : P.Idx) :: tail)
      = TraceList.occurrences b tail := by
  simp [TraceList.occurrences, Ne.symm hb]

/-- Run a program against a supply, retaining the typed path the answers selected. -/
def runPath : (program : FreeM P α) → Supply P → Option (FreeM.Path program × Supply P)
  | .pure _, s => some (⟨⟩, s)
  | .liftBind a next, s =>
      match s a with
      | [] => none
      | u :: us =>
          (runPath (next u) (Function.update s a us)).map fun r => (⟨u, r.1⟩, r.2)

@[simp] lemma runPath_pure (x : α) (s : Supply P) :
    runPath (pure x : FreeM P α) s = some (⟨⟩, s) := rfl

lemma runPath_liftBind_of_nil {a : P.A} (next : P.B a → FreeM P α) {s : Supply P} (hs : s a = []) :
    runPath (FreeM.liftBind a next) s = none := by
  rw [runPath]; rw [hs]

lemma runPath_liftBind_of_cons {a : P.A} (next : P.B a → FreeM P α) {s : Supply P} {u : P.B a}
    {us : List (P.B a)} (hs : s a = u :: us) :
    runPath (FreeM.liftBind a next) s
      = (runPath (next u) (s.update a us)).map fun r => (⟨u, r.1⟩, r.2) := by
  rw [runPath]; rw [hs]; rfl

/-- **`run` is `runPath` with the path forgotten.** Reading the leaf off the selected path recovers
exactly the value the plain run returns, so every statement about `runPath` is a statement about
`run`. -/
theorem run_eq_map_runPath : ∀ (program : FreeM P α) (s : Supply P),
    run program s = (runPath program s).map fun r => (FreeM.output program r.1, r.2)
  | .pure y, s => by
      rw [show run (FreeM.pure y : FreeM P α) s = some (y, s) from rfl,
        show runPath (FreeM.pure y : FreeM P α) s = some (⟨⟩, s) from rfl]
      rfl
  | .liftBind a next, s => by
      cases hs : s a with
      | nil => rw [run_liftBind_of_nil next hs, runPath_liftBind_of_nil next hs]; rfl
      | cons u us =>
          rw [run_liftBind_of_cons next hs, runPath_liftBind_of_cons next hs,
            run_eq_map_runPath (next u) (s.update a us), Option.map_map]
          rfl

/-! ### What the run consumed -/

/-- **A run leaves behind exactly what it did not read.** At every position, the remaining supply
is that position's list with one answer dropped per event the executed trace has there. -/
theorem apply_eq_drop_occurrences : ∀ (program : FreeM P α) {s s' : Supply P}
    {path : FreeM.Path program}, runPath program s = some (path, s') → ∀ b : P.A,
      s' b = (s b).drop (TraceList.occurrences b (FreeM.Path.trace program path))
  | .pure y, s, s', path, h, b => by
      rw [show runPath (FreeM.pure y : FreeM P α) s = some (⟨⟩, s) from rfl, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
  | .liftBind a next, s, s', path, h, b => by
      classical
      cases hs : s a with
      | nil => rw [runPath_liftBind_of_nil next hs] at h; simp at h
      | cons u us =>
          rw [runPath_liftBind_of_cons next hs, Option.map_eq_some_iff] at h
          obtain ⟨r, hrec, heq⟩ := h
          obtain ⟨tail, s''⟩ := r
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          have hih := apply_eq_drop_occurrences (next u) hrec b
          by_cases hb : b = a
          · subst hb
            rw [hih, update_apply_self, trace_liftBind', occurrences_cons_self, hs,
              List.drop_succ_cons]
          · rw [hih, update_apply_of_ne _ _ _ hb, trace_liftBind', occurrences_cons_of_ne hb]

/-- **The bridge to the trace.** The answer a run took at the `n`-th occurrence of a position is
the supply's `n`-th answer there. A supply therefore *positionally* determines the trace, which is
what lets the occurrence and cursor layers reason about it. -/
theorem getAt?_trace_runPath (program : FreeM P α) : ∀ (b : P.A) (n : Nat) (s s' : Supply P)
    (path : FreeM.Path program), runPath program s = some (path, s') →
      n < TraceList.occurrences b (FreeM.Path.trace program path) →
        TraceList.getAt? (FreeM.Path.trace program path) b n = (s b)[n]? := by
  classical
  induction program with
  | pure y =>
      intro b n s s' path h hn
      rw [runPath_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [TraceList.occurrences] at hn
  | lift_bind a next ih =>
      intro b n s s' path h hn
      -- The recursor presents the node as `(FreeM.lift a).bind next`; name it by its constructor.
      replace h : runPath (FreeM.liftBind a next) s = some (path, s') := h
      replace hn : n < TraceList.occurrences b
        (FreeM.Path.trace (FreeM.liftBind a next) path) := hn
      suffices hgoal : TraceList.getAt? (FreeM.Path.trace (FreeM.liftBind a next) path) b n
          = (s b)[n]? from hgoal
      cases hs : s a with
      | nil => rw [runPath_liftBind_of_nil next hs] at h; simp at h
      | cons u us =>
          rw [runPath_liftBind_of_cons next hs] at h
          obtain ⟨r, hrec, heq⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨tail, s''⟩ := r
          simp only at heq
          obtain ⟨rfl, rfl⟩ := heq
          rw [trace_liftBind'] at hn ⊢
          by_cases hb : b = a
          · subst hb
            cases n with
            | zero => rw [TraceList.getAt?_cons_self_zero, hs]; rfl
            | succ n =>
                rw [occurrences_cons_self] at hn
                have hih := ih u b n (s.update b us) s' tail hrec (by omega)
                rw [TraceList.getAt?_cons_self_succ, hih, update_apply_self, hs]
                rfl
          · rw [occurrences_cons_of_ne hb] at hn
            have hih := ih u b n (s.update a us) s' tail hrec hn
            rw [TraceList.getAt?_cons_of_ne (fun h : a = b => hb h.symm), hih,
              update_apply_of_ne _ _ _ hb]

/-- A run never reads more answers at a position than the supply offers there. -/
theorem occurrences_le_length {program : FreeM P α} {s s' : Supply P} {path : FreeM.Path program}
    (h : runPath program s = some (path, s')) (b : P.A) :
    TraceList.occurrences b (FreeM.Path.trace program path) ≤ (s b).length := by
  rcases Nat.eq_zero_or_pos (TraceList.occurrences b (FreeM.Path.trace program path)) with hz | hp
  · omega
  · have hlt : TraceList.occurrences b (FreeM.Path.trace program path) - 1 <
        TraceList.occurrences b (FreeM.Path.trace program path) := by omega
    have hsome := TraceList.getAt?_isSome_iff_lt_occurrences
      (events := FreeM.Path.trace program path) (target := b)
      (n := TraceList.occurrences b (FreeM.Path.trace program path) - 1) |>.mpr hlt
    rw [getAt?_trace_runPath program b _ s s' path h hlt] at hsome
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hlt', -⟩ := List.getElem?_eq_some_iff.mp hx
    omega

/-- The run's consumption, as a length. -/
theorem length_add_occurrences {program : FreeM P α} {s s' : Supply P} {path : FreeM.Path program}
    (h : runPath program s = some (path, s')) (b : P.A) :
    (s' b).length + TraceList.occurrences b (FreeM.Path.trace program path) = (s b).length := by
  have hle := occurrences_le_length h b
  rw [apply_eq_drop_occurrences program h b, List.length_drop]
  omega

/-! ### Substitution is substitution at an occurrence -/

variable {program : FreeM P α} {s s' : Supply P} {a : P.A} {n : Nat} {u : P.B a}

/-- **Substituting the supply substitutes the trace.** If the run reaches the `n`-th occurrence of
`a` at all, the answer it takes there is the substituted one. -/
theorem getAt?_trace_runPath_setAt (hn : n < (s a).length) {path : FreeM.Path program}
    (h : runPath program (s.setAt a n u) = some (path, s'))
    (hocc : n < TraceList.occurrences a (FreeM.Path.trace program path)) :
    TraceList.getAt? (FreeM.Path.trace program path) a n = some u := by
  rw [getAt?_trace_runPath program a n _ s' path h hocc, getElem?_setAt_self s a u hn]

/-- Every other answer at the substituted position is untouched. -/
theorem getAt?_trace_runPath_setAt_of_ne {m : Nat} (hm : m ≠ n) {path : FreeM.Path program}
    (h : runPath program (s.setAt a n u) = some (path, s'))
    (hocc : m < TraceList.occurrences a (FreeM.Path.trace program path)) :
    TraceList.getAt? (FreeM.Path.trace program path) a m = (s a)[m]? := by
  rw [getAt?_trace_runPath program a m _ s' path h hocc, setAt_apply_self,
    List.getElem?_set_ne (Ne.symm hm)]

/-- And so is every answer at every other position. -/
theorem getAt?_trace_runPath_setAt_of_pos_ne {b : P.A} (hb : b ≠ a) {m : Nat}
    {path : FreeM.Path program} (h : runPath program (s.setAt a n u) = some (path, s'))
    (hocc : m < TraceList.occurrences b (FreeM.Path.trace program path)) :
    TraceList.getAt? (FreeM.Path.trace program path) b m = (s b)[m]? := by
  rw [getAt?_trace_runPath program b m _ s' path h hocc, setAt_apply_of_ne _ _ _ _ hb]

end Supply

end PFunctor
