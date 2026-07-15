/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Focus

/-!
# Typed contexts and occurrence splitting for free polynomial programs

This file provides finite occurrence contexts for `PFunctor.FreeM`.
An `Occurrence` stops immediately before a selected polynomial position and
retains the typed prefix needed to complete that position along any answer.
The executable `splitAt` operation exposes this context without interpreting
the polynomial.
-/

@[expose] public section

open scoped PFunctor

universe uA uB v

namespace PFunctor.FreeM.Path

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-! ## Occurrence contexts and completions -/

/-- Mapping after a universe-polymorphic free-monad bind can be moved into
each continuation. -/
theorem bind_map_right {δ : Type*} {β : Type*} {γ : Type*}
    (mx : FreeM P δ) (g : δ → FreeM P β) (f : β → γ) :
    FreeM.bind mx (fun x => FreeM.map f (g x)) =
      FreeM.map f (FreeM.bind mx g) := by
  simpa only [FreeM.bind_pure_comp] using
    (FreeM.bind_assoc mx g (pure ∘ f)).symm

/-- Binding after path execution exposes the root answer and tail path
without leaving a dependent `map` in the term. -/
theorem withPath_liftBind_bind {γ : Type*} (a : P.A)
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

/-- A typed prefix ending immediately before occurrence `n` of `target`. -/
inductive Occurrence (target : P.A) : (program : FreeM P α) → Nat → Type (max uA uB v)
  | here (resume : P.B target → FreeM P α) :
      Occurrence target (FreeM.liftBind target resume) 0
  | stepSame {next : P.B target → FreeM P α} {n : Nat}
      (answer : P.B target) (tail : Occurrence target (next answer) n) :
      Occurrence target (FreeM.liftBind target next) (n + 1)
  | stepOther {a : P.A} {next : P.B a → FreeM P α} {n : Nat}
      (hne : a ≠ target) (answer : P.B a) (tail : Occurrence target (next answer) n) :
      Occurrence target (FreeM.liftBind a next) n

namespace Occurrence

variable {target : P.A} {program : FreeM P α} {n : Nat}

/-- Continuation family exposed at the focused occurrence. -/
def resume : {program : FreeM P α} → {n : Nat} →
    Occurrence target program n → P.B target → FreeM P α
  | _, _, .here next => next
  | _, _, .stepSame _ tail => tail.resume
  | _, _, .stepOther _ _ tail => tail.resume

/-- Erased events strictly before the focused occurrence. -/
def before : {program : FreeM P α} → {n : Nat} →
    Occurrence target program n → PFunctor.TraceList P
  | _, _, .here _ => []
  | _, _, .stepSame answer tail => ⟨target, answer⟩ :: tail.before
  | _, _, .stepOther _ answer tail => ⟨_, answer⟩ :: tail.before

/-- Plug an answer and residual suffix through an occurrence context. -/
def plug : {program : FreeM P α} → {n : Nat} →
    (occ : Occurrence target program n) → (answer : P.B target) →
      Path (occ.resume answer) → Path program
  | _, _, .here _, answer, suffix => ⟨answer, suffix⟩
  | _, _, .stepSame prefixAnswer tail, answer, suffix =>
      ⟨prefixAnswer, tail.plug answer suffix⟩
  | _, _, .stepOther _ prefixAnswer tail, answer, suffix =>
      ⟨prefixAnswer, tail.plug answer suffix⟩

@[simp] theorem before_count [DecidableEq P.A]
    (occ : Occurrence target program n) :
    occurrences target occ.before = n := by
  induction occ with
  | here => rfl
  | stepSame answer tail ih =>
      rw [before, occurrences, List.countP_cons_of_pos (by simp)]
      change occurrences target tail.before + 1 = _
      rw [ih]
  | stepOther hne answer tail ih =>
      rw [before, occurrences, List.countP_cons_of_neg (by simp [hne])]
      exact ih

@[simp] theorem trace_plug (occ : Occurrence target program n)
    (answer : P.B target) (suffix : Path (occ.resume answer)) :
    trace program (occ.plug answer suffix) = List.append occ.before
      (⟨target, answer⟩ :: trace (occ.resume answer) suffix) := by
  induction occ with
  | here => rfl
  | stepSame prefixAnswer tail ih =>
      change _ :: trace _ (tail.plug answer suffix) =
        _ :: List.append tail.before (⟨target, answer⟩ :: trace (tail.resume answer) suffix)
      rw [ih]
  | stepOther hne prefixAnswer tail ih =>
      change _ :: trace _ (tail.plug answer suffix) =
        _ :: List.append tail.before (⟨target, answer⟩ :: trace (tail.resume answer) suffix)
      rw [ih]

@[simp] theorem output_plug (occ : Occurrence target program n)
    (answer : P.B target) (suffix : Path (occ.resume answer)) :
    output program (occ.plug answer suffix) = output (occ.resume answer) suffix := by
  induction occ with
  | here => rfl
  | stepSame _ tail ih =>
      change output _ (tail.plug answer suffix) = output (tail.resume answer) suffix
      exact ih suffix
  | stepOther _ _ tail ih =>
      change output _ (tail.plug answer suffix) = output (tail.resume answer) suffix
      exact ih suffix

/-- An answer at the focused event and a path through the resulting residual. -/
structure Completion (occ : Occurrence target program n) where
  /-- Answer supplied at the focused occurrence. -/
  answer : P.B target
  /-- Path through the residual program selected by `answer`. -/
  suffix : Path (occ.resume answer)

/-- Full program path represented by an occurrence completion. -/
def Completion.path {occ : Occurrence target program n} (completion : Completion occ) :
    Path program := occ.plug completion.answer completion.suffix

/-- Execute the focused query and its residual, retaining the typed completion. -/
def complete (occ : Occurrence target program n) : FreeM P (Completion occ) :=
  FreeM.liftBind target fun answer =>
    FreeM.map (fun suffix => Completion.mk answer suffix) (withPath (occ.resume answer))

/-- Execute an occurrence completion and plug it back into the original program. -/
def completePath (occ : Occurrence target program n) : FreeM P (Path program) :=
  FreeM.map Completion.path occ.complete

end Occurrence

/-- Two independent completions of one occurrence context. Retaining the
context makes the shared prefix intrinsic rather than a property reconstructed
from the two full paths. -/
structure ForkView (target : P.A) (program : FreeM P α) (n : Nat) where
  /-- Shared typed prefix ending at the selected occurrence. -/
  occurrence : Occurrence target program n
  /-- First independent completion of the occurrence. -/
  first : occurrence.Completion
  /-- Second independent completion of the same occurrence. -/
  second : occurrence.Completion

namespace ForkView

variable {target : P.A} {program : FreeM P α} {n : Nat}

/-- Full path selected by the first completion. -/
def firstPath (view : ForkView target program n) : Path program :=
  view.first.path

/-- Full path selected by the second completion. -/
def secondPath (view : ForkView target program n) : Path program :=
  view.second.path

/-- Answer at the focused occurrence in the first completion. -/
def firstAnswer (view : ForkView target program n) : P.B target :=
  view.first.answer

/-- Answer at the focused occurrence in the second completion. -/
def secondAnswer (view : ForkView target program n) : P.B target :=
  view.second.answer

/-- Extend both completions by one earlier occurrence of the target. -/
def prependSame {next : P.B target → FreeM P α} (answer : P.B target) {n : Nat}
    (view : ForkView target (next answer) n) :
    ForkView target (FreeM.liftBind target next) (n + 1) where
  occurrence := .stepSame answer view.occurrence
  first := ⟨view.first.answer, view.first.suffix⟩
  second := ⟨view.second.answer, view.second.suffix⟩

/-- Extend both completions by one earlier non-target event. -/
def prependOther {a : P.A} {next : P.B a → FreeM P α} (_hne : a ≠ target)
    (answer : P.B a) {n : Nat} (view : ForkView target (next answer) n) :
    ForkView target (FreeM.liftBind a next) n where
  occurrence := .stepOther _hne answer view.occurrence
  first := ⟨view.first.answer, view.first.suffix⟩
  second := ⟨view.second.answer, view.second.suffix⟩

end ForkView

/-! ## Splitting execution at an occurrence -/

/-- Result of stopping an execution immediately before a selected occurrence. -/
inductive Split (target : P.A) (program : FreeM P α) (n : Nat) : Type (max uA uB v)
  | missing (path : Path program)
  | found (occurrence : Occurrence target program n)

namespace Split

variable [DecidableEq P.A] {target : P.A} {program : FreeM P α} {n : Nat}

/-- Structural invariant of a split result. A missing occurrence can only be
returned after executing a path containing at most `n` target events. -/
def Valid (result : Split target program n) : Prop :=
  match result with
  | .missing path => occurrences target (trace program path) ≤ n
  | .found _ => True

/-- Resume a split result to a complete path. -/
def complete : Split target program n → FreeM P (Path program)
  | .missing path => pure path
  | .found occurrence => occurrence.completePath

/-- Independently complete a found occurrence twice. A certified missing
split has no occurrence to fork and therefore returns `none`. -/
def completeFork : Split target program n →
    FreeM P (Option (ForkView target program n))
  | .missing _ => pure none
  | .found occurrence =>
      FreeM.liftBind target fun firstAnswer =>
        FreeM.bind (withPath (occurrence.resume firstAnswer)) fun firstSuffix =>
          FreeM.liftBind target fun secondAnswer =>
            FreeM.map (fun secondSuffix => some {
              occurrence := occurrence
              first := ⟨firstAnswer, firstSuffix⟩
              second := ⟨secondAnswer, secondSuffix⟩ })
              (withPath (occurrence.resume secondAnswer))

omit [DecidableEq P.A] in
/-- On a found occurrence, `completeFork` is two independent executions of
the occurrence completion program. -/
theorem completeFork_found (occurrence : Occurrence target program n) :
    completeFork (.found occurrence) =
      FreeM.bind occurrence.complete fun first : occurrence.Completion =>
        FreeM.map (fun second : occurrence.Completion => some {
          occurrence := occurrence
          first := first
          second := second }) occurrence.complete := by
  unfold completeFork Occurrence.complete
  simp only [FreeM.bind, FreeM.map]
  apply congrArg (FreeM.liftBind target)
  funext firstAnswer
  conv_rhs => rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
  apply congrArg (FreeM.bind (withPath (occurrence.resume firstAnswer)))
  funext firstSuffix
  apply congrArg (FreeM.liftBind target)
  funext secondAnswer
  rw [← FreeM.comp_map]
  rfl

omit [DecidableEq P.A] in
/-- Observing a found fork is the corresponding observation of its two
independent occurrence completions. -/
theorem map_completeFork_found (occurrence : Occurrence target program n)
    {β : Type*} (observe : ForkView target program n → β) :
    FreeM.map (Option.map observe) (completeFork (.found occurrence)) =
      FreeM.bind occurrence.complete fun first : occurrence.Completion =>
        FreeM.map (fun second : occurrence.Completion => some (observe {
          occurrence := occurrence
          first := first
          second := second })) occurrence.complete := by
  rw [completeFork_found]
  rw [← bind_map_right]
  apply congrArg (FreeM.bind occurrence.complete)
  funext first
  rw [← FreeM.comp_map]
  rfl

/-- Extend a split result by one earlier occurrence of the target. -/
def prependSame {next : P.B target → FreeM P α} (answer : P.B target) {n : Nat} :
    Split target (next answer) n → Split target (FreeM.liftBind target next) (n + 1)
  | .missing path => .missing ⟨answer, path⟩
  | .found occurrence => .found (.stepSame answer occurrence)

/-- Extend a split result by one earlier non-target event. -/
def prependOther {a : P.A} {next : P.B a → FreeM P α} (hne : a ≠ target)
    (answer : P.B a) {n : Nat} :
    Split target (next answer) n → Split target (FreeM.liftBind a next) n
  | .missing path => .missing ⟨answer, path⟩
  | .found occurrence => .found (.stepOther hne answer occurrence)

theorem valid_prependSame {next : P.B target → FreeM P α}
    (answer : P.B target) {n : Nat} (result : Split target (next answer) n)
    (hresult : result.Valid) : (prependSame answer result).Valid := by
  cases result with
  | missing path =>
      change occurrences target
        (⟨target, answer⟩ :: trace (next answer) path) ≤ n + 1
      simpa [occurrences] using Nat.succ_le_succ hresult
  | found occurrence => trivial

theorem valid_prependOther {a : P.A} {next : P.B a → FreeM P α}
    (hne : a ≠ target) (answer : P.B a) {n : Nat}
    (result : Split target (next answer) n) (hresult : result.Valid) :
    (prependOther hne answer result).Valid := by
  cases result with
  | missing path =>
      change occurrences target (trace (next answer) path) ≤ n at hresult
      change occurrences target (⟨a, answer⟩ :: trace (next answer) path) ≤ n
      simpa [occurrences, hne] using hresult
  | found occurrence => trivial

omit [DecidableEq P.A] in
theorem completeFork_prependSame
    {next : P.B target → FreeM P α} (answer : P.B target) {n : Nat}
    (result : Split target (next answer) n) :
    completeFork (prependSame answer result) =
      FreeM.map (Option.map (ForkView.prependSame answer)) (completeFork result) := by
  cases result with
  | missing => rfl
  | found occurrence =>
      simp only [prependSame, completeFork]
      simp only [Occurrence.resume, FreeM.map]
      apply congrArg (FreeM.liftBind target)
      funext firstAnswer
      rw [← bind_map_right]
      apply congrArg (FreeM.bind (withPath (occurrence.resume firstAnswer)))
      funext firstSuffix
      apply congrArg (FreeM.liftBind target)
      funext secondAnswer
      rw [← FreeM.comp_map]
      apply congrArg (fun f => FreeM.map f (withPath (occurrence.resume secondAnswer)))
      funext secondSuffix
      rfl

omit [DecidableEq P.A] in
theorem completeFork_prependOther
    {a : P.A} {next : P.B a → FreeM P α} (hne : a ≠ target)
    (answer : P.B a) {n : Nat} (result : Split target (next answer) n) :
    completeFork (prependOther hne answer result) =
      FreeM.map (Option.map (ForkView.prependOther hne answer)) (completeFork result) := by
  cases result with
  | missing => rfl
  | found occurrence =>
      simp only [prependOther, completeFork]
      simp only [Occurrence.resume, FreeM.map]
      apply congrArg (FreeM.liftBind target)
      funext firstAnswer
      rw [← bind_map_right]
      apply congrArg (FreeM.bind (withPath (occurrence.resume firstAnswer)))
      funext firstSuffix
      apply congrArg (FreeM.liftBind target)
      funext secondAnswer
      rw [← FreeM.comp_map]
      apply congrArg (fun f => FreeM.map f (withPath (occurrence.resume secondAnswer)))
      funext secondSuffix
      rfl

omit [DecidableEq P.A] in
theorem complete_prependSame {next : P.B target → FreeM P α} (answer : P.B target)
    {n : Nat} (result : Split target (next answer) n) :
    complete (prependSame answer result) =
      FreeM.map (fun path => (⟨answer, path⟩ : Path (FreeM.liftBind target next)))
        (complete result) := by
  cases result with
  | missing => rfl
  | found occurrence =>
      unfold complete Occurrence.completePath Occurrence.complete
      simp only [FreeM.map]
      apply congrArg (FreeM.liftBind target)
      funext focusedAnswer
      simp only [Occurrence.resume]
      rw [← FreeM.comp_map]
      conv_rhs => rw [← FreeM.comp_map, ← FreeM.comp_map]
      apply congrArg (fun f => FreeM.map f (withPath (occurrence.resume focusedAnswer)))
      funext suffix
      rfl

omit [DecidableEq P.A] in
theorem complete_prependOther {a : P.A} {next : P.B a → FreeM P α}
    (hne : a ≠ target) (answer : P.B a) {n : Nat}
    (result : Split target (next answer) n) :
    complete (prependOther hne answer result) =
      FreeM.map (fun path => (⟨answer, path⟩ : Path (FreeM.liftBind a next)))
        (complete result) := by
  cases result with
  | missing => rfl
  | found occurrence =>
      unfold complete Occurrence.completePath Occurrence.complete
      simp only [FreeM.map]
      apply congrArg (FreeM.liftBind target)
      funext focusedAnswer
      simp only [Occurrence.resume]
      rw [← FreeM.comp_map]
      conv_rhs => rw [← FreeM.comp_map, ← FreeM.comp_map]
      apply congrArg (fun f => FreeM.map f (withPath (occurrence.resume focusedAnswer)))
      funext suffix
      rfl

end Split

/-! ## Executable splitting and prefix-first reforking -/

/-- Execute a program only until immediately before occurrence `n` of `target`. -/
def splitAt [DecidableEq P.A] (target : P.A) :
    (program : FreeM P α) → (n : Nat) → FreeM P (Split target program n)
  | .pure value, _ => pure (.missing ⟨⟩)
  | .liftBind a next, n =>
      if h : a = target then
        match n with
        | 0 => by
            subst target
            exact pure (.found (.here next))
        | n + 1 => by
            subst target
            exact FreeM.liftBind a fun answer =>
              FreeM.map (Split.prependSame answer)
                (splitAt a (next answer) n)
      else
        FreeM.liftBind a fun answer =>
          FreeM.map (Split.prependOther h answer)
            (splitAt target (next answer) n)

/-- Certified execution of `splitAt`. The certificate is carried only by this
proof-facing computation, leaving `Split` itself as the minimal operational
result type. -/
def splitAtValid [DecidableEq P.A] (target : P.A) :
    (program : FreeM P α) → (n : Nat) →
      FreeM P {result : Split target program n // result.Valid}
  | .pure value, n => pure ⟨.missing ⟨⟩, Nat.zero_le n⟩
  | .liftBind a next, n =>
      if h : a = target then
        match n with
        | 0 => by
            subst target
            exact pure ⟨.found (.here next), trivial⟩
        | n + 1 => by
            subst target
            exact FreeM.liftBind a fun answer =>
              FreeM.map (fun result =>
                ⟨Split.prependSame answer result.1,
                  Split.valid_prependSame answer result.1 result.2⟩)
                (splitAtValid a (next answer) n)
      else
        FreeM.liftBind a fun answer =>
          FreeM.map (fun result =>
            ⟨Split.prependOther h answer result.1,
              Split.valid_prependOther h answer result.1 result.2⟩)
            (splitAtValid target (next answer) n)

@[simp] theorem splitAtValid_pure [DecidableEq P.A] (target : P.A)
    (value : α) (n : Nat) :
    splitAtValid target (pure value : FreeM P α) n =
      pure ⟨.missing ⟨⟩, Nat.zero_le n⟩ := rfl

theorem splitAtValid_liftBind_same_zero [DecidableEq P.A] (target : P.A)
    (next : P.B target → FreeM P α) :
    splitAtValid target (FreeM.liftBind target next) 0 =
      pure ⟨.found (.here next), trivial⟩ := by
  simp [splitAtValid]

theorem splitAtValid_liftBind_same_succ [DecidableEq P.A] (target : P.A)
    (next : P.B target → FreeM P α) (n : Nat) :
    splitAtValid target (FreeM.liftBind target next) (n + 1) =
      FreeM.liftBind target fun answer =>
        FreeM.map (fun result =>
          ⟨Split.prependSame answer result.1,
            Split.valid_prependSame answer result.1 result.2⟩)
          (splitAtValid target (next answer) n) := by
  simp [splitAtValid]

theorem splitAtValid_liftBind_other [DecidableEq P.A] {target a : P.A}
    (hne : a ≠ target) (next : P.B a → FreeM P α) (n : Nat) :
    splitAtValid target (FreeM.liftBind a next) n =
      FreeM.liftBind a fun answer =>
        FreeM.map (fun result =>
          ⟨Split.prependOther hne answer result.1,
            Split.valid_prependOther hne answer result.1 result.2⟩)
          (splitAtValid target (next answer) n) := by
  rw (occs := .pos [1]) [splitAtValid.eq_def]
  simp only [dif_neg hne]

@[simp] theorem splitAt_pure [DecidableEq P.A] (target : P.A) (value : α) (n : Nat) :
    splitAt target (pure value : FreeM P α) n = pure (.missing ⟨⟩) := rfl

/-- Splitting at an occurrence and completing the result recovers the original
path-producing execution exactly. -/
theorem splitAt_bind_complete [DecidableEq P.A] (target : P.A) :
    (program : FreeM P α) → (n : Nat) →
      FreeM.bind (splitAt target program n) Split.complete = withPath program := by
  intro program
  induction program with
  | pure value =>
      intro n
      rfl
  | lift_bind a next ih =>
      intro n
      change FreeM.bind (splitAt target (FreeM.liftBind a next) n) Split.complete =
        withPath (FreeM.liftBind a next)
      by_cases h : a = target
      · subst target
        cases n with
        | zero =>
            simp only [splitAt, withPath]
            apply congrArg (FreeM.liftBind a)
            funext answer
            rw [← FreeM.comp_map]
            rfl
        | succ n =>
            simp only [splitAt, withPath]
            apply congrArg (FreeM.liftBind a)
            funext answer
            rw [show FreeM.bind (FreeM.map (Split.prependSame answer)
                (splitAt a (next answer) n)) Split.complete =
              FreeM.bind (splitAt a (next answer) n)
                (fun result => Split.complete (Split.prependSame answer result)) by
              rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
              rfl]
            simp_rw [Split.complete_prependSame]
            let addPrefix : Path (next answer) → Path (FreeM.liftBind a next) :=
              fun path => ⟨answer, path⟩
            change FreeM.bind (splitAt a (next answer) n)
                (fun result => FreeM.map addPrefix (Split.complete result)) =
              FreeM.map addPrefix (withPath (next answer))
            rw [bind_map_right, ih answer n]
      · simp only [splitAt, dif_neg h, withPath]
        apply congrArg (FreeM.liftBind a)
        funext answer
        rw [show FreeM.bind (FreeM.map (Split.prependOther h answer)
              (splitAt target (next answer) n)) Split.complete =
            FreeM.bind (splitAt target (next answer) n)
              (fun result => Split.complete (Split.prependOther h answer result)) by
            rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
            rfl]
        simp_rw [Split.complete_prependOther]
        let addPrefix : Path (next answer) → Path (FreeM.liftBind a next) :=
          fun path => ⟨answer, path⟩
        change FreeM.bind (splitAt target (next answer) n)
            (fun result => FreeM.map addPrefix (Split.complete result)) =
          FreeM.map addPrefix (withPath (next answer))
        rw [bind_map_right, ih answer n]

/-- Erasing validity certificates from `splitAtValid` recovers `splitAt`. -/
theorem map_val_splitAtValid [DecidableEq P.A] (target : P.A) :
    (program : FreeM P α) → (n : Nat) →
      FreeM.map Subtype.val (splitAtValid target program n) =
        splitAt target program n := by
  intro program
  induction program with
  | pure value =>
      intro n
      rfl
  | lift_bind a next ih =>
      intro n
      change FreeM.map Subtype.val
          (splitAtValid target (FreeM.liftBind a next) n) =
        splitAt target (FreeM.liftBind a next) n
      by_cases h : a = target
      · subst target
        cases n with
        | zero =>
            rw [splitAtValid_liftBind_same_zero]
            simp [splitAt]
        | succ n =>
            rw [splitAtValid_liftBind_same_succ]
            simp only [splitAt, FreeM.map]
            apply congrArg (FreeM.liftBind a)
            funext answer
            rw [← FreeM.comp_map]
            change FreeM.map (Split.prependSame answer ∘ Subtype.val)
                (splitAtValid a (next answer) n) =
              FreeM.map (Split.prependSame answer) (splitAt a (next answer) n)
            rw [FreeM.comp_map, ih answer n]
      · rw [splitAtValid_liftBind_other h]
        simp only [splitAt, dif_neg h, FreeM.map]
        apply congrArg (FreeM.liftBind a)
        funext answer
        rw [← FreeM.comp_map]
        change FreeM.map (Split.prependOther h answer ∘ Subtype.val)
            (splitAtValid target (next answer) n) =
          FreeM.map (Split.prependOther h answer)
            (splitAt target (next answer) n)
        rw [FreeM.comp_map, ih answer n]

/-- Completing a certified split recovers the original path-producing
execution. This is the certified analogue of `splitAt_bind_complete`. -/
theorem splitAtValid_bind_complete [DecidableEq P.A] (target : P.A)
    (program : FreeM P α) (n : Nat) :
    FreeM.bind (splitAtValid target program n)
        (fun result => Split.complete result.1) = withPath program := by
  rw [← splitAt_bind_complete target program n,
    ← map_val_splitAtValid target program n]
  rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
  rfl

/-- Execute to occurrence `n`, retain its typed prefix, and independently
complete the occurrence twice. -/
def forkAt [DecidableEq P.A] (target : P.A) (program : FreeM P α) (n : Nat) :
    FreeM P (Option (ForkView target program n)) :=
  FreeM.bind (splitAt target program n) Split.completeFork

/-- Certified splitting followed by two focused completions is exactly the
ordinary `forkAt` computation after forgetting the validity certificate. -/
theorem splitAtValid_bind_completeFork [DecidableEq P.A] (target : P.A)
    (program : FreeM P α) (n : Nat) :
    FreeM.bind (splitAtValid target program n)
        (fun result => Split.completeFork result.1) = forkAt target program n := by
  unfold forkAt
  rw [← map_val_splitAtValid target program n]
  rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
  rfl

@[simp] theorem forkAt_pure [DecidableEq P.A] (target : P.A) (value : α) (n : Nat) :
    forkAt target (pure value : FreeM P α) n = pure none := rfl

theorem forkAt_liftBind_same_zero [DecidableEq P.A] (target : P.A)
    (next : P.B target → FreeM P α) :
    forkAt target (FreeM.liftBind target next) 0 =
      Split.completeFork (.found (.here next)) := by
  simp [forkAt, splitAt]

theorem forkAt_liftBind_same_succ [DecidableEq P.A] (target : P.A)
    (next : P.B target → FreeM P α) (n : Nat) :
    forkAt target (FreeM.liftBind target next) (n + 1) =
      FreeM.liftBind target fun answer =>
        FreeM.map (Option.map (ForkView.prependSame answer))
          (forkAt target (next answer) n) := by
  unfold forkAt
  simp only [splitAt]
  apply congrArg (FreeM.liftBind target)
  funext answer
  rw [show FreeM.bind (FreeM.map (Split.prependSame answer)
        (splitAt target (next answer) n)) Split.completeFork =
      FreeM.bind (splitAt target (next answer) n)
        (fun result => Split.completeFork (Split.prependSame answer result)) by
      rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
      rfl]
  simp_rw [Split.completeFork_prependSame]
  rw [bind_map_right]

theorem forkAt_liftBind_other [DecidableEq P.A] {target a : P.A}
    (hne : a ≠ target) (next : P.B a → FreeM P α) (n : Nat) :
    forkAt target (FreeM.liftBind a next) n =
      FreeM.liftBind a fun answer =>
        FreeM.map (Option.map (ForkView.prependOther hne answer))
          (forkAt target (next answer) n) := by
  unfold forkAt
  simp only [splitAt, dif_neg hne]
  apply congrArg (FreeM.liftBind a)
  funext answer
  rw [show FreeM.bind (FreeM.map (Split.prependOther hne answer)
        (splitAt target (next answer) n)) Split.completeFork =
      FreeM.bind (splitAt target (next answer) n)
        (fun result => Split.completeFork (Split.prependOther hne answer result)) by
      rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
      rfl]
  simp_rw [Split.completeFork_prependOther]
  rw [bind_map_right]


end PFunctor.FreeM.Path
