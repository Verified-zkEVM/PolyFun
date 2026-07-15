/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Cursor.Occurrence

/-!
# Reforking free polynomial programs at typed occurrences

This file locates a selected occurrence on an executed path and independently
completes the retained occurrence context a second time. Fixed and dynamically
selected reforking share the same path-independent `Occurrence` representation.
-/

@[expose] public section

open scoped PFunctor

universe uA uB v

namespace PFunctor.FreeM.Cursor

open PFunctor.TraceList

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-! ## Locating an occurrence on an existing path -/

/-- A concrete path decomposed into a path-independent occurrence context and
the answer/suffix completing that context. -/
structure Located (target : P.A) (program : FreeM P α)
    (path : Path program) (n : Nat) where
  /-- Path-independent context of the selected occurrence. -/
  occurrence : Occurrence target program n
  /-- Answer and suffix by which the original path completes the occurrence. -/
  completion : occurrence.Completion
  /-- The stored completion reconstructs the original path. -/
  path_eq : completion.path = path

namespace Located

/-- Regard an occurrence completion as the corresponding located occurrence
on its full path. -/
def ofCompletion {target : P.A} {program : FreeM P α} {n : Nat}
    {occ : Occurrence target program n} (completion : occ.Completion) :
    Located target program completion.path n where
  occurrence := occ
  completion := completion
  path_eq := rfl

/-- Locate the root occurrence of a path. -/
def here {target : P.A}
    (next : P.B target → FreeM P α) (answer : P.B target)
    (suffix : Path (next answer)) :
    Located target (FreeM.liftBind target next) ⟨answer, suffix⟩ 0 where
  occurrence := .here next
  completion := ⟨answer, suffix⟩
  path_eq := rfl

/-- Extend a located path by one earlier occurrence of the target. -/
def prependSame {target : P.A}
    {next : P.B target → FreeM P α} (answer : P.B target)
    {suffix : Path (next answer)} {n : Nat}
    (located : Located target (next answer) suffix n) :
    Located target (FreeM.liftBind target next) ⟨answer, suffix⟩ (n + 1) where
  occurrence := .stepSame answer located.occurrence
  completion := ⟨located.completion.answer, located.completion.suffix⟩
  path_eq := by
    change (⟨answer, located.completion.path⟩ :
      Path (FreeM.liftBind target next)) = ⟨answer, suffix⟩
    rw [located.path_eq]

/-- Extend a located path by one earlier non-target event. -/
def prependOther {target a : P.A}
    {next : P.B a → FreeM P α} (hne : a ≠ target) (answer : P.B a)
    {suffix : Path (next answer)} {n : Nat}
    (located : Located target (next answer) suffix n) :
    Located target (FreeM.liftBind a next) ⟨answer, suffix⟩ n where
  occurrence := .stepOther hne answer located.occurrence
  completion := ⟨located.completion.answer, located.completion.suffix⟩
  path_eq := by
    change (⟨answer, located.completion.path⟩ :
      Path (FreeM.liftBind a next)) = ⟨answer, suffix⟩
    rw [located.path_eq]

end Located

/-! ## Path-first and dynamically selected reforking -/

/-- Locate occurrence `n` on an existing path and return its typed context
decomposition. -/
def locateAt? [DecidableEq P.A] (target : P.A) :
    (program : FreeM P α) → (path : Path program) → (n : Nat) →
      Option (Located target program path n)
  | .pure _, _, _ => none
  | .liftBind a next, ⟨answer, suffix⟩, n =>
      if h : a = target then
        match n with
        | 0 => by
            subst target
            exact some (Located.here next answer suffix)
        | n + 1 => by
            subst target
            exact (locateAt? a (next answer) suffix n).map
              (Located.prependSame answer)
      else
        (locateAt? target (next answer) suffix n).map
          (Located.prependOther h answer)

@[simp] theorem locateAt?_pure [DecidableEq P.A] (target : P.A) (value : α)
    (path : Path (pure value : FreeM P α)) (n : Nat) :
    locateAt? target (pure value) path n = none := rfl

theorem locateAt?_liftBind_same_zero [DecidableEq P.A] (target : P.A)
    (next : P.B target → FreeM P α) (answer : P.B target)
    (suffix : Path (next answer)) :
    locateAt? target (FreeM.liftBind target next) ⟨answer, suffix⟩ 0 =
      some (Located.here next answer suffix) := by
  simp [locateAt?]

theorem locateAt?_liftBind_same_succ [DecidableEq P.A] (target : P.A)
    (next : P.B target → FreeM P α) (answer : P.B target)
    (suffix : Path (next answer)) (n : Nat) :
    locateAt? target (FreeM.liftBind target next) ⟨answer, suffix⟩ (n + 1) =
      (locateAt? target (next answer) suffix n).map
        (Located.prependSame answer) := by
  simp [locateAt?]

theorem locateAt?_liftBind_other [DecidableEq P.A] {target a : P.A}
    (hne : a ≠ target) (next : P.B a → FreeM P α) (answer : P.B a)
    (suffix : Path (next answer)) (n : Nat) :
    locateAt? target (FreeM.liftBind a next) ⟨answer, suffix⟩ n =
      (locateAt? target (next answer) suffix n).map
        (Located.prependOther hne answer) := by
  simp [locateAt?, hne]

/-- Locating the selected ordinal on a completed occurrence recovers that
occurrence and completion. -/
theorem locateAt?_completion_path [DecidableEq P.A]
    {target : P.A} {program : FreeM P α} {n : Nat}
    (occ : Occurrence target program n) (completion : occ.Completion) :
    locateAt? target program completion.path n =
      some (Located.ofCompletion completion) := by
  induction occ with
  | here next =>
      rcases completion with ⟨answer, suffix⟩
      change locateAt? target (FreeM.liftBind target next)
          ⟨answer, suffix⟩ 0 = _
      rw [locateAt?_liftBind_same_zero]
      rfl
  | stepSame prefixAnswer tail ih =>
      rcases completion with ⟨answer, suffix⟩
      change Path (tail.resume answer) at suffix
      simp only [Occurrence.Completion.path, Occurrence.plug_stepSame]
      rw [locateAt?_liftBind_same_succ]
      have htail := ih (⟨answer, suffix⟩ : tail.Completion)
      simp only [Occurrence.Completion.path] at htail
      rw [htail]
      rfl
  | stepOther hne prefixAnswer tail ih =>
      rcases completion with ⟨answer, suffix⟩
      change Path (tail.resume answer) at suffix
      simp only [Occurrence.Completion.path, Occurrence.plug_stepOther]
      rw [locateAt?_liftBind_other hne]
      have htail := ih (⟨answer, suffix⟩ : tail.Completion)
      simp only [Occurrence.Completion.path] at htail
      rw [htail]
      rfl

/-- A context can be located exactly when the path contains the requested
target occurrence. -/
theorem locateAt?_isSome_iff_lt_occurrences [DecidableEq P.A] (target : P.A)
    (program : FreeM P α) (path : Path program) (n : Nat) :
    (locateAt? target program path n).isSome ↔
      n < occurrences target (Path.trace program path) := by
  induction program generalizing n with
  | pure value => simp [occurrences]
  | lift_bind a next ih =>
      rcases path with ⟨answer, suffix⟩
      by_cases h : a = target
      · subst a
        cases n with
        | zero =>
            change (locateAt? target (FreeM.liftBind target next)
              (⟨answer, suffix⟩ : Path (FreeM.liftBind target next)) 0).isSome ↔
              0 < occurrences target
                (⟨target, answer⟩ :: Path.trace (next answer) suffix)
            rw [locateAt?_liftBind_same_zero]
            simp [occurrences]
        | succ n =>
            change (locateAt? target (FreeM.liftBind target next)
              (⟨answer, suffix⟩ : Path (FreeM.liftBind target next)) (n + 1)).isSome ↔
              n + 1 < occurrences target
                (⟨target, answer⟩ :: Path.trace (next answer) suffix)
            rw [locateAt?_liftBind_same_succ, Option.isSome_map]
            simpa [occurrences] using ih answer suffix n
      · change (locateAt? target (FreeM.liftBind a next)
            (⟨answer, suffix⟩ : Path (FreeM.liftBind a next)) n).isSome ↔
          n < occurrences target (⟨a, answer⟩ :: Path.trace (next answer) suffix)
        rw [locateAt?_liftBind_other h, Option.isSome_map]
        simpa [occurrences, h] using ih answer suffix n

namespace Located

/-- Independently complete the occurrence carried by a located first path. -/
def refork {target : P.A} {program : FreeM P α}
    {path : Path program} {n : Nat} (located : Located target program path n) :
    FreeM P (ForkView target program n) :=
  FreeM.liftBind target fun secondAnswer =>
    FreeM.map (fun secondSuffix => {
      occurrence := located.occurrence
      first := located.completion
      second := ⟨secondAnswer, secondSuffix⟩ })
      (withPath (located.occurrence.resume secondAnswer))

/-- A located refork is a generic completion of its occurrence, decorated
with the already observed first completion. -/
theorem refork_eq_map_complete {target : P.A}
    {program : FreeM P α} {path : Path program} {n : Nat}
    (located : Located target program path n) :
    located.refork =
      FreeM.map (fun second : located.occurrence.Completion => ({
        occurrence := located.occurrence
        first := located.completion
        second := second } : ForkView target program n))
        located.occurrence.complete := by
  unfold refork Occurrence.complete
  simp only [FreeM.map]
  apply congrArg (FreeM.bind (FreeM.lift target))
  funext secondAnswer
  rw [← FreeM.comp_map]
  rfl

/-- Reforking commutes with an earlier target occurrence. -/
theorem refork_prependSame {target : P.A}
    {next : P.B target → FreeM P α} (answer : P.B target)
    {suffix : Path (next answer)} {n : Nat}
    (located : Located target (next answer) suffix n) :
    (prependSame answer located).refork =
      FreeM.map (ForkView.prependSame answer) located.refork := by
  unfold refork prependSame ForkView.prependSame
  simp only [Occurrence.resume, FreeM.map]
  apply congrArg (FreeM.liftBind target)
  funext secondAnswer
  rw [← FreeM.comp_map]
  apply congrArg (fun f => FreeM.map f
    (withPath (located.occurrence.resume secondAnswer)))
  funext secondSuffix
  rfl

/-- Reforking commutes with an earlier non-target event. -/
theorem refork_prependOther {target a : P.A}
    {next : P.B a → FreeM P α} (hne : a ≠ target) (answer : P.B a)
    {suffix : Path (next answer)} {n : Nat}
    (located : Located target (next answer) suffix n) :
    (prependOther hne answer located).refork =
      FreeM.map (ForkView.prependOther hne answer) located.refork := by
  unfold refork prependOther ForkView.prependOther
  simp only [Occurrence.resume, FreeM.map]
  apply congrArg (FreeM.liftBind target)
  funext secondAnswer
  rw [← FreeM.comp_map]
  apply congrArg (fun f => FreeM.map f
    (withPath (located.occurrence.resume secondAnswer)))
  funext secondSuffix
  rfl

end Located

/-- Path-first presentation of `forkAt`: execute one complete path, recover
its occurrence context, and independently complete that context once more. -/
def reforkAt [DecidableEq P.A] (target : P.A) (program : FreeM P α) (n : Nat) :
    FreeM P (Option (ForkView target program n)) :=
  FreeM.bind (withPath program) fun (path : Path program) =>
    match locateAt? target program path n with
    | none => pure none
    | some located => FreeM.map some located.refork

/-- A dynamically selected refork together with the label that chose its
dependent occurrence index. -/
structure SelectedForkView (target : P.A) (program : FreeM P α)
    (κ : Type*) (index : κ → Nat) where
  /-- Selector label that determines the reforked occurrence. -/
  label : κ
  /-- Two completions of the occurrence selected by `label`. -/
  view : ForkView target program (index label)

namespace SelectedForkView

variable {κ : Type*} {index : κ → Nat} {target : P.A}
  {program : FreeM P α}

/-- Output of the first completion in a selected fork. -/
def firstOutput (selected : SelectedForkView target program κ index) : α :=
  output program selected.view.firstPath

/-- Output of the independently sampled second completion. -/
def secondOutput (selected : SelectedForkView target program κ index) : α :=
  output program selected.view.secondPath

/-- Observable output pair of a selected fork. -/
def outputs (selected : SelectedForkView target program κ index) : α × α :=
  (selected.firstOutput, selected.secondOutput)

end SelectedForkView

/-- Dynamically select an occurrence from the first output and refork its
typed context.  The observer hides the path-dependent occurrence index from
the result type, making this the canonical reduction-wiring interface. -/
def reforkBy [DecidableEq P.A] {κ β : Type*}
    (target : P.A) (program : FreeM P α)
    (select : α → Option κ) (index : κ → Nat)
    (observe : (k : κ) → ForkView target program (index k) → β) :
    FreeM P (Option β) :=
  FreeM.bind (withPath program) fun path =>
    match select (output program path) with
    | none => pure none
    | some k =>
        match locateAt? target program path (index k) with
        | none => pure none
        | some located => FreeM.map (some ∘ observe k) located.refork

/-- Dynamically select an occurrence and retain its typed fork view together
with the selecting label. -/
def reforkSelected [DecidableEq P.A] {κ : Type*}
    (target : P.A) (program : FreeM P α)
    (select : α → Option κ) (index : κ → Nat) :
    FreeM P (Option (SelectedForkView target program κ index)) :=
  reforkBy target program select index fun label view => ⟨label, view⟩

/-- Dynamically select and refork an occurrence, discarding observations
that do not satisfy a pure optional classifier. -/
def filterMapReforkBy [DecidableEq P.A] {κ β : Type*}
    (target : P.A) (program : FreeM P α)
    (select : α → Option κ) (index : κ → Nat)
    (observe : (k : κ) → ForkView target program (index k) → Option β) :
    FreeM P (Option β) :=
  FreeM.map Option.join (reforkBy target program select index observe)

/-- Refork one fixed occurrence and discard views rejected by a pure optional
classifier. -/
def filterMapReforkAt [DecidableEq P.A] {β : Type*}
    (target : P.A) (program : FreeM P α) (n : Nat)
    (observe : ForkView target program n → Option β) :
    FreeM P (Option β) :=
  FreeM.map (fun view? => view?.bind observe) (reforkAt target program n)

/-- Mapping an observation after dynamic refork selection fuses into the
path-dependent observer. -/
theorem map_reforkBy [DecidableEq P.A] {κ β γ : Type*}
    (target : P.A) (program : FreeM P α)
    (select : α → Option κ) (index : κ → Nat)
    (observe : (k : κ) → ForkView target program (index k) → β)
    (f : Option β → γ) :
    FreeM.map f (reforkBy target program select index observe) =
      FreeM.bind (withPath program) fun path =>
        match select (output program path) with
        | none => pure (f none)
        | some k =>
            match locateAt? target program path (index k) with
            | none => pure (f none)
            | some located =>
                FreeM.map (f ∘ some ∘ observe k) located.refork := by
  unfold reforkBy
  rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
  apply congrArg (FreeM.bind (withPath program))
  funext path
  rcases hselect : select (output program path) with _ | k
  · rfl
  · rcases hlocate : locateAt? target program path (index k) with _ | located
    · simp only [hlocate]
      rfl
    · simp only [hlocate]
      rw [FreeM.bind_pure_comp, ← FreeM.comp_map]

/-- Eliminate a dynamically selected optional refork into its first path and
one independently sampled completion. -/
theorem filterMapReforkBy_eq_bind_complete [DecidableEq P.A]
    {κ β : Type*} (target : P.A) (program : FreeM P α)
    (select : α → Option κ) (index : κ → Nat)
    (observe : (k : κ) → ForkView target program (index k) → Option β) :
    filterMapReforkBy target program select index observe =
      FreeM.bind (withPath program) fun path =>
        match select (output program path) with
        | none => pure none
        | some k =>
            match locateAt? target program path (index k) with
            | none => pure none
            | some located =>
                FreeM.map (fun second => observe k {
                  occurrence := located.occurrence
                  first := located.completion
                  second := second }) located.occurrence.complete := by
  unfold filterMapReforkBy
  rw [map_reforkBy]
  apply congrArg (FreeM.bind (withPath program))
  funext path
  rcases hselect : select (output program path) with _ | k
  · rfl
  · rcases hlocate : locateAt? target program path (index k) with _ | located
    · simp [hlocate]
    · simp only [hlocate]
      rw [Located.refork_eq_map_complete, ← FreeM.comp_map]
      rfl

/-- Mapping an observation over a path-first refork can be pushed into each
located continuation. This is the canonical elimination rule for consumers
that inspect a `ForkView` without otherwise changing the reforking program. -/
theorem map_reforkAt [DecidableEq P.A] {β : Type*} (target : P.A)
    (program : FreeM P α) (n : Nat)
    (observe : Option (ForkView target program n) → β) :
    FreeM.map observe (reforkAt target program n) =
      FreeM.bind (withPath program) fun path =>
        match locateAt? target program path n with
        | none => pure (observe none)
        | some located => FreeM.map (observe ∘ some) located.refork := by
  unfold reforkAt
  rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
  apply congrArg (FreeM.bind (withPath program))
  funext path
  rcases locateAt? target program path n with _ | located
  · rfl
  · rw [FreeM.bind_pure_comp, ← FreeM.comp_map]

/-- Eliminate a fixed optional refork into its first path and one
independently sampled completion. -/
theorem filterMapReforkAt_eq_bind_complete [DecidableEq P.A]
    {β : Type*} (target : P.A) (program : FreeM P α) (n : Nat)
    (observe : ForkView target program n → Option β) :
    filterMapReforkAt target program n observe =
      FreeM.bind (withPath program) fun path =>
        match locateAt? target program path n with
        | none => pure none
        | some located =>
            FreeM.map (fun second => observe {
              occurrence := located.occurrence
              first := located.completion
              second := second }) located.occurrence.complete := by
  unfold filterMapReforkAt reforkAt
  rw [← bind_map_right]
  apply congrArg (FreeM.bind (withPath program))
  funext path
  rcases hlocate : locateAt? target program path n with _ | located
  · rfl
  · rw [← FreeM.comp_map, Located.refork_eq_map_complete, ← FreeM.comp_map]
    rfl

@[simp] theorem reforkAt_pure [DecidableEq P.A] (target : P.A)
    (value : α) (n : Nat) :
    reforkAt target (pure value : FreeM P α) n = pure none := rfl

theorem reforkAt_liftBind_same_zero [DecidableEq P.A] (target : P.A)
    (next : P.B target → FreeM P α) :
    reforkAt target (FreeM.liftBind target next) 0 =
      Split.completeFork (.found (.here next)) := by
  unfold reforkAt
  rw [withPath_liftBind_bind]
  apply congrArg (FreeM.liftBind target)
  funext firstAnswer
  apply congrArg (FreeM.bind (withPath (next firstAnswer)))
  funext firstSuffix
  rw [locateAt?_liftBind_same_zero]
  simp only [Located.refork, Occurrence.resume, FreeM.map]
  apply congrArg (FreeM.liftBind target)
  funext secondAnswer
  rw [← FreeM.comp_map]
  rfl

theorem reforkAt_liftBind_same_succ [DecidableEq P.A] (target : P.A)
    (next : P.B target → FreeM P α) (n : Nat) :
    reforkAt target (FreeM.liftBind target next) (n + 1) =
      FreeM.liftBind target fun answer =>
        FreeM.map (Option.map (ForkView.prependSame answer))
          (reforkAt target (next answer) n) := by
  unfold reforkAt
  rw [withPath_liftBind_bind]
  apply congrArg (FreeM.liftBind target)
  funext answer
  rw [← bind_map_right]
  apply congrArg (FreeM.bind (withPath (next answer)))
  funext suffix
  rw [locateAt?_liftBind_same_succ]
  rcases hlocated : locateAt? target (next answer) suffix n with _ | located
  · rfl
  · simp only [Option.map_some]
    rw [Located.refork_prependSame, ← FreeM.comp_map, ← FreeM.comp_map]
    rfl

theorem reforkAt_liftBind_other [DecidableEq P.A] {target a : P.A}
    (hne : a ≠ target) (next : P.B a → FreeM P α) (n : Nat) :
    reforkAt target (FreeM.liftBind a next) n =
      FreeM.liftBind a fun answer =>
        FreeM.map (Option.map (ForkView.prependOther hne answer))
          (reforkAt target (next answer) n) := by
  unfold reforkAt
  rw [withPath_liftBind_bind]
  apply congrArg (FreeM.liftBind a)
  funext answer
  rw [← bind_map_right]
  apply congrArg (FreeM.bind (withPath (next answer)))
  funext suffix
  rw [locateAt?_liftBind_other hne]
  rcases hlocated : locateAt? target (next answer) suffix n with _ | located
  · rfl
  · simp only [Option.map_some]
    rw [Located.refork_prependOther, ← FreeM.comp_map, ← FreeM.comp_map]
    rfl

/-- Splitting before execution and locating the same occurrence after one
execution define the same resampling program. -/
theorem forkAt_eq_reforkAt [DecidableEq P.A] (target : P.A) :
    (program : FreeM P α) → (n : Nat) →
      forkAt target program n = reforkAt target program n := by
  intro program
  induction program with
  | pure value =>
      intro n
      rw [forkAt_pure, reforkAt_pure]
  | lift_bind a next ih =>
      intro n
      by_cases h : a = target
      · subst a
        cases n with
        | zero =>
            change forkAt target (FreeM.liftBind target next) 0 =
              reforkAt target (FreeM.liftBind target next) 0
            rw [forkAt_liftBind_same_zero, reforkAt_liftBind_same_zero]
        | succ n =>
            change forkAt target (FreeM.liftBind target next) (n + 1) =
              reforkAt target (FreeM.liftBind target next) (n + 1)
            rw [forkAt_liftBind_same_succ, reforkAt_liftBind_same_succ]
            apply congrArg (FreeM.liftBind target)
            funext answer
            rw [ih answer n]
      · change forkAt target (FreeM.liftBind a next) n =
          reforkAt target (FreeM.liftBind a next) n
        rw [forkAt_liftBind_other h, reforkAt_liftBind_other h]
        apply congrArg (FreeM.liftBind a)
        funext answer
        rw [ih answer n]

end PFunctor.FreeM.Cursor
