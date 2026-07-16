/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Sim.CrossSignature

/-!
# Cross-signature relational ITree examples

These compile-time examples exercise the event/reply-dependent
`CrossSignatureWeakBisim` API, its same-signature specialization, monadic
congruence, lens graph theorem, and separation of all event and return
universes.
-/

@[expose] public section

universe uEA uEB uFA uFB uα uβ

namespace ITree.CrossSignatureExamples

variable {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
  {α : Type uα} {β : Type uβ}

/-- Event signatures, replies, and return values may all inhabit independent
universes. -/
def separated (eventRel : ITree.EventSignatureRel E F) (resultRel : α → β → Prop)
    (left : ITree E α) (right : ITree F β) : Prop :=
  ITree.CrossSignatureWeakBisim eventRel resultRel left right

/-- The identity event-signature relation recovers the established relational weak
bisimulation semantics exactly. -/
example (resultRel : α → β → Prop) (left : ITree E α) (right : ITree E β) :
    ITree.CrossSignatureWeakBisim (ITree.EventSignatureRel.eq E) resultRel left right ↔
      ITree.WeakBisimRel resultRel left right :=
  ITree.CrossSignatureWeakBisim.eq_iff_weakBisimRel

example (tree : ITree E α) :
    ITree.CrossSignatureWeakBisim (ITree.EventSignatureRel.eq E) Eq tree tree :=
  ITree.CrossSignatureWeakBisim.refl tree

/-! ## A concrete relation between distinct protocols -/

inductive ReadEvent where
  | read

inductive SampleEvent where
  | sample

@[reducible] def ReadSpec : PFunctor :=
  ⟨ReadEvent, fun | .read => Bool⟩

@[reducible] def SampleSpec : PFunctor :=
  ⟨SampleEvent, fun | .sample => Fin 2⟩

/-- `false` corresponds to zero and `true` to one. -/
def readSampleRel : ITree.EventSignatureRel ReadSpec SampleSpec where
  event
    | .read, .sample => True
  reply
    | .read, .sample, _, flag, sample =>
        sample.val = if flag then 1 else 0

def boolFinRel (flag : Bool) (sample : Fin 2) : Prop :=
  sample.val = if flag then 1 else 0

def readTree : ITree ReadSpec Bool :=
  ITree.query .read ITree.pure

def sampleTree : ITree SampleSpec (Fin 2) :=
  ITree.query .sample ITree.pure

/-- The relation is observable at both the query and returned value. -/
theorem readTree_sampleTree :
    ITree.CrossSignatureWeakBisim readSampleRel boolFinRel readTree sampleTree := by
  unfold readTree sampleTree
  apply ITree.CrossSignatureWeakBisim.query (eventRel := readSampleRel)
    ReadEvent.read SampleEvent.sample trivial ITree.pure ITree.pure
  intro flag sample h
  exact ITree.CrossSignatureWeakBisim.pure h

example : ITree.CrossSignatureWeakBisim readSampleRel
    (readSampleRel.reply ReadEvent.read SampleEvent.sample trivial)
    (ITree.lift ReadEvent.read) (ITree.lift SampleEvent.sample) :=
  ITree.CrossSignatureWeakBisim.lift (eventRel := readSampleRel)
    ReadEvent.read SampleEvent.sample trivial

def leftCont (flag : Bool) : ITree ReadSpec String :=
  ITree.pure (if flag then "one" else "zero")

def rightCont (sample : Fin 2) : ITree SampleSpec Bool :=
  ITree.pure (sample.val = 1)

def stringBoolRel (label : String) (isOne : Bool) : Prop :=
  (label = "one" ∧ isOne = true) ∨ (label = "zero" ∧ isOne = false)

/-- Cross-signature relations compose with the monadic program structure. -/
example : ITree.CrossSignatureWeakBisim readSampleRel stringBoolRel
    (ITree.bind readTree leftCont) (ITree.bind sampleTree rightCont) := by
  apply readTree_sampleTree.bind
  intro flag sample h
  unfold boolFinRel at h
  unfold leftCont rightCont
  cases flag <;> apply ITree.CrossSignatureWeakBisim.pure <;> simp_all [stringBoolRel]

/-! ## Lens graphs -/

def readToSample : PFunctor.Lens ReadSpec SampleSpec where
  toFunA
    | .read => .sample
  toFunB
    | .read, sample => sample.val = 1

example (tree : ITree ReadSpec Nat) :
    ITree.CrossSignatureWeakBisim (ITree.EventSignatureRel.ofLens readToSample) Eq tree
      (ITree.mapSpec readToSample tree) :=
  ITree.CrossSignatureWeakBisim.mapSpec readToSample tree

end ITree.CrossSignatureExamples
