/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Closure
public import PolyFun.Realizability.Quantitative

/-!
# Compositional quantitative realizability

This file refines the structural closure operations of `StepClass` with executable
`QuantitativeStepClass.Realizer` data. The four mixins mirror the qualitative product, sum,
optional-value, and distributivity interfaces without attaching an asymptotic interpretation to
them. In particular, a structural realizer has the exact backend cost supplied by `Q.cost`, but no
theorem here calls that cost polynomial or bounds it by the costs of its inputs.

The resulting realization constructors cover the operations whose qualitative counterparts live
in `PolyFun.Realizability.Closure`:

* immediate return from an explicitly supplied result realizer;
* input precomposition and result postcomposition;
* sequential composition of two returning machines.

Sequential composition constructs executable code for every map of the sum-state machine. It does
not produce an `IsQuantitativelyRealizableWithin` theorem: doing so requires backend-specific size
and cost bounds for the structural codes below. This separation keeps generic machine assembly
honest while leaving polynomial closure to an adequacy-backed complexity layer.
-/

@[expose] public section

universe u v w

namespace PFunctor

namespace QuantitativeStepClass

variable {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C)

/-! ## Transport of executable evidence -/

namespace Realizer

variable {Q} {A B : Type u} {a : C.Str A} {b : C.Str B} {f g : A → B}

/-- Transport executable evidence across extensional equality of its semantic function. -/
def castFunction (code : Q.Realizer a b f) (h : f = g) : Q.Realizer a b g :=
  h ▸ code

/-- Transporting a realizer's semantic index does not alter its backend cost. -/
@[simp]
theorem cost_castFunction (code : Q.Realizer a b f) (h : f = g) (input : A) :
    Q.cost (code.castFunction h) input = Q.cost code input := by
  cases h
  rfl

end Realizer

/-! ## Executable structural mixins -/

/-- Executable counterparts of the product operations of a qualitative step class.

The product representation remains the pinned representation chosen by `C.HasProd`; this class
only supplies backend code implementing its projections and pairing operation. -/
class HasProd [P : C.HasProd] where
  /-- Executable first projection. -/
  fst : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.Realizer (P.prod a b) a Prod.fst
  /-- Executable second projection. -/
  snd : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.Realizer (P.prod a b) b Prod.snd
  /-- Executable pairing of two functions with a common input. -/
  pair : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : A → D}, Q.Realizer a b f → Q.Realizer a d g →
      Q.Realizer a (P.prod b d) fun input ↦ (f input, g input)

namespace HasProd

variable [Q.HasCategory] [P : C.HasProd] (QP : Q.HasProd)

/-- Execute two functions independently on the components of a product. -/
def map {A B A' B' : Type u} {a : C.Str A} {b : C.Str B} {a' : C.Str A'}
    {b' : C.Str B'} {f : A → A'} {g : B → B'}
    (left : Q.Realizer a a' f) (right : Q.Realizer b b' g) :
    Q.Realizer (P.prod a b) (P.prod a' b') (Prod.map f g) :=
  (QP.pair (Q.compose (QP.fst a b) left) (Q.compose (QP.snd a b) right)).castFunction
    (by
      funext input
      cases input
      rfl)

/-- Execute a function on the first component while retaining the second. -/
def pairRight {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} (code : Q.Realizer a b f) :
    Q.Realizer (P.prod a d) (P.prod b d) fun input ↦ (f input.1, input.2) :=
  (QP.pair (Q.compose (QP.fst a d) code) (QP.snd a d)).castFunction
    (by
      funext input
      cases input
      rfl)

/-- Execute a function on the second component while retaining the first. -/
def pairLeft {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} (code : Q.Realizer a b f) :
    Q.Realizer (P.prod d a) (P.prod d b) fun input ↦ (input.1, f input.2) :=
  (QP.pair (QP.fst d a) (Q.compose (QP.snd d a) code)).castFunction
    (by
      funext input
      cases input
      rfl)

/-- Duplicate a represented input. -/
def diag {A : Type u} (a : C.Str A) :
    Q.Realizer a (P.prod a a) fun input ↦ (input, input) :=
  QP.pair (Q.identity a) (Q.identity a)

/-- Retain an input alongside an executable readout of it. -/
def withInput {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) :
    Q.Realizer a (P.prod b a) fun input ↦ (f input, input) :=
  QP.pair code (Q.identity a)

/-- Swap the components of a represented product. -/
def swap {A B : Type u} (a : C.Str A) (b : C.Str B) :
    Q.Realizer (P.prod a b) (P.prod b a) Prod.swap :=
  (QP.pair (QP.snd a b) (QP.fst a b)).castFunction
    (by
      funext input
      cases input
      rfl)

end HasProd

/-- Executable counterparts of the sum operations of a qualitative step class. -/
class HasSum [S : C.HasSum] where
  /-- Executable left injection. -/
  inl : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.Realizer a (S.sum a b) Sum.inl
  /-- Executable right injection. -/
  inr : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.Realizer b (S.sum a b) Sum.inr
  /-- Executable case analysis over a represented sum. -/
  elim : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → D} {g : B → D}, Q.Realizer a d f → Q.Realizer b d g →
      Q.Realizer (S.sum a b) d (Sum.elim f g)

namespace HasSum

variable [Q.HasCategory] [S : C.HasSum] (QS : Q.HasSum)

/-- Execute functions independently on the two summands. -/
def map {A B A' B' : Type u} {a : C.Str A} {b : C.Str B} {a' : C.Str A'}
    {b' : C.Str B'} {f : A → A'} {g : B → B'}
    (left : Q.Realizer a a' f) (right : Q.Realizer b b' g) :
    Q.Realizer (S.sum a b) (S.sum a' b') (Sum.map f g) :=
  (QS.elim (Q.compose left (QS.inl a' b')) (Q.compose right (QS.inr a' b'))).castFunction
    (by
      funext input
      cases input <;> rfl)

end HasSum

/-- Executable counterparts of optional-value operations of a qualitative step class. -/
class HasOption [P : C.HasProd] [O : C.HasOption] where
  /-- Execute a represented function under `Option.map`. -/
  map : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B},
    Q.Realizer a b f → Q.Realizer (O.option a) (O.option b) (Option.map f)
  /-- Executable constant absent value. -/
  none : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.Realizer a (O.option b) fun _ ↦ none
  /-- Execute contextual bind of a represented optional value. -/
  bindContext : ∀ {A B E : Type u} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    {k : A × E → Option B}, Q.Realizer (P.prod a e) (O.option b) k →
      Q.Realizer (P.prod (O.option a) e) (O.option b) fun input ↦
        input.1.bind fun value ↦ k (value, input.2)

/-- Executable distributivity of product over sum.

Unlike qualitative `StepClass.IsDistributive`, this is data rather than a proposition: it retains
the backend program that moves the sum tag out of its paired context. -/
class IsDistributive [P : C.HasProd] [S : C.HasSum] where
  /-- Execute the inverse distributivity map used by contextual case analysis. -/
  distribute : ∀ {A B E : Type u} (a : C.Str A) (b : C.Str B) (e : C.Str E),
    Q.Realizer (P.prod (S.sum a b) e) (S.sum (P.prod a e) (P.prod b e)) fun input ↦
      Sum.elim (fun left ↦ Sum.inl (left, input.2))
        (fun right ↦ Sum.inr (right, input.2)) input.1

namespace IsDistributive

variable [Q.HasCategory] [P : C.HasProd] [S : C.HasSum] [QS : Q.HasSum]
  (QD : Q.IsDistributive)

/-- Execute case analysis while retaining a common context. -/
def elimContext {A B E D : Type u} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    {d : C.Str D} {f : A × E → D} {g : B × E → D}
    (left : Q.Realizer (P.prod a e) d f) (right : Q.Realizer (P.prod b e) d g) :
    Q.Realizer (P.prod (S.sum a b) e) d fun input ↦
      Sum.elim (fun value ↦ f (value, input.2))
        (fun value ↦ g (value, input.2)) input.1 :=
  (Q.compose (QD.distribute a b e) (QS.elim left right)).castFunction
    (by
      funext input
      obtain ⟨side, context⟩ := input
      cases side <;> rfl)

end IsDistributive

end QuantitativeStepClass

namespace DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}} [P : C.HasProd]
  [S : C.HasSum] [O : C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {A B : Type u}
  {bd : Boundary C p A B}

/-! ## Executable interface transport -/

/-- Executable evidence for the two maps used to transport a machine along a lens.

The position map changes exposed queries. `onPull` handles the harder direction: it partially
pulls a tagged answer back through the lens while observing the whole return-or-query head. -/
structure _root_.PFunctor.Lens.QuantitativelyAdmissible
    {q : PFunctor.{u, u}} [DecidableEq q.A] (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C p A B) (posRep : C.Str q.A) (idxRep : C.Str q.Idx)
    (lens : Lens p q) where
  /-- Executable evidence for the lens's position map. -/
  onPos : Q.Realizer bd.pos posRep lens.toFunA
  /-- Executable evidence for the lens's partial tagged-answer pullback. -/
  onPull : Q.Realizer (P.prod bd.head idxRep) (O.option bd.idx) (lens.pullHeadIdx B)

omit [DecidableEq p.A] in
/-- Forget executable lens code, retaining qualitative admissibility. -/
theorem _root_.PFunctor.Lens.QuantitativelyAdmissible.toIsAdmissible
    {q : PFunctor.{u, u}} [DecidableEq q.A] {posRep : C.Str q.A}
    {idxRep : C.Str q.Idx} {lens : Lens p q}
    (h : lens.QuantitativelyAdmissible Q bd posRep idxRep) :
    lens.IsAdmissible C bd posRep idxRep where
  onPos := Q.admissible h.onPos
  onPull := Q.admissible h.onPull

namespace QuantitativeRealization

/-! ## Immediately returning machines -/

section OfFn

variable [QS : Q.HasSum] [QO : Q.HasOption]

/-- Quantitative realization of an immediately returning function from explicit backend code. -/
@[implicit_reducible]
def ofFn {f : A → B} (code : Q.Realizer bd.input bd.out f) :
    QuantitativeRealization Q bd where
  machine := DynComputation.ofFn (p := p) f
  state := bd.out
  initCode := code
  headCode := QS.inl bd.out bd.pos
  updateCode := (QO.none (bd.stateIdx bd.out) bd.out).castFunction (by
    funext step
    exact (update?_of_view_return (DynComputation.ofFn (p := p) f)
      (view_ofFn f step.1) step.2).symm)

end OfFn

/-! ## Input precomposition -/

/-- Precompose the input of a quantitative realization with explicit backend code.

The new initialization code is genuine sequential composition. Its exact cost therefore follows
from `QuantitativeStepClass.cost_comp`; the head and update code are shared unchanged. -/
@[implicit_reducible]
def precomp [Q.HasCategory] {D : Type u} {inputRep : C.Str D} {f : D → A}
    (R : QuantitativeRealization Q bd) (code : Q.Realizer inputRep bd.input f) :
    QuantitativeRealization Q (bd.withInput inputRep) where
  machine := R.machine.setInit (R.machine.init ∘ f)
  state := R.state
  initCode := by
    change Q.Realizer inputRep R.state (R.machine.init ∘ f)
    exact Q.compose code R.initCode
  headCode := R.headCode
  updateCode := R.updateCode

/-- Initialization cost of quantitative input precomposition is bounded by its components and
the backend's explicit connection overhead. -/
theorem cost_initCode_precomp_le [Q.HasCategory]
    {D : Type u} {inputRep : C.Str D} {f : D → A}
    (R : QuantitativeRealization Q bd) (code : Q.Realizer inputRep bd.input f)
    (input : D) :
    Q.cost (R.precomp code).initCode input ≤
      Q.cost code input + Q.cost R.initCode (f input) +
        Q.composeOverhead code R.initCode input :=
  by
    change Q.cost (Q.compose code R.initCode) input ≤ _
    exact Q.cost_comp_le code R.initCode input

/-- Exact initialization cost when the backend carries an exact-category refinement. -/
theorem cost_initCode_precomp [Q.HasCategory] [Q.HasExactCategory]
    {D : Type u} {inputRep : C.Str D} {f : D → A}
    (R : QuantitativeRealization Q bd) (code : Q.Realizer inputRep bd.input f)
    (input : D) :
    Q.cost (R.precomp code).initCode input =
      Q.cost code input + Q.cost R.initCode (f input) +
        Q.composeOverhead code R.initCode input := by
  change Q.cost (Q.compose code R.initCode) input = _
  exact Q.cost_comp code R.initCode input

/-- Input precomposition leaves one-step readout work unchanged. -/
@[simp] theorem cost_headCode_precomp [Q.HasCategory]
    {D : Type u} {inputRep : C.Str D} {f : D → A}
    (R : QuantitativeRealization Q bd) (code : Q.Realizer inputRep bd.input f)
    (state : R.machine.State) :
    Q.cost (R.precomp code).headCode state = Q.cost R.headCode state :=
  rfl

/-- Input precomposition leaves enabled-transition work unchanged. -/
@[simp] theorem cost_updateCode_precomp [Q.HasCategory]
    {D : Type u} {inputRep : C.Str D} {f : D → A}
    (R : QuantitativeRealization Q bd) (code : Q.Realizer inputRep bd.input f)
    (step : R.machine.State × p.Idx) :
    Q.cost (R.precomp code).updateCode step = Q.cost R.updateCode step :=
  rfl

/-- Input precomposition leaves hidden-state encodings unchanged. -/
@[simp] theorem size_state_precomp [Q.HasCategory]
    {D : Type u} {inputRep : C.Str D} {f : D → A}
    (R : QuantitativeRealization Q bd) (code : Q.Realizer inputRep bd.input f)
    (state : R.machine.State) :
    Q.size (R.precomp code).state state = Q.size R.state state :=
  rfl

/-- Input precomposition leaves encoded one-step readout sizes unchanged. -/
@[simp] theorem size_head_precomp [Q.HasCategory]
    {D : Type u} {inputRep : C.Str D} {f : D → A}
    (R : QuantitativeRealization Q bd) (code : Q.Realizer inputRep bd.input f)
    (state : R.machine.State) :
    Q.size bd.head ((R.precomp code).machine.head state) =
      Q.size bd.head (R.machine.head state) :=
  rfl

/-! ## Result postcomposition -/

section MapResult

variable [Q.HasCategory] [QS : Q.HasSum]

/-- Postcompose returned values of a quantitative realization with explicit backend code. -/
@[implicit_reducible]
def mapResult {D : Type u} {outRep : C.Str D} {f : B → D}
    (R : QuantitativeRealization Q bd) (code : Q.Realizer bd.out outRep f) :
    QuantitativeRealization Q (bd.withOut outRep) where
  machine := R.machine.mapResult f
  state := R.state
  initCode := R.initCode
  headCode := by
    let resultCode := QuantitativeStepClass.HasSum.map Q QS code (Q.identity bd.pos)
    exact (Q.compose R.headCode resultCode).castFunction (by
      funext state
      exact (head_mapResult R.machine f state).symm)
  updateCode := R.updateCode.castFunction (by
    funext step
    exact (update?_mapResult R.machine f step).symm)

end MapResult

/-! ## Sequential composition -/

section SeqComp

variable [Q.HasCategory] [QS : Q.HasSum] [QO : Q.HasOption] [QP : Q.HasProd]
  [QD : Q.IsDistributive] {D : Type u} {outRep : C.Str D}

/-- Sequentially compose two quantitative realizations.

All three maps of the sum-state machine carry executable evidence. No resource bound is inferred:
the exact cost of each assembled map remains available through `Q.cost` and `Q.cost_compose`, while
bounding the primitive structural codes is an explicit backend obligation. -/
@[implicit_reducible]
def seqComp (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) :
    QuantitativeRealization Q (bd.withOut outRep) where
  machine := R₁.machine.seqComp R₂.machine
  state := S.sum R₁.state R₂.state
  initCode := (Q.compose R₁.initCode (QS.inl R₁.state R₂.state)).castFunction (by
    funext input
    rfl)
  headCode :=
    let handoff := Q.compose R₂.initCode R₂.headCode
    let left := Q.compose R₁.headCode
      (QS.elim handoff (QS.inr outRep bd.pos))
    (QS.elim left R₂.headCode).castFunction (by
      funext state
      cases state with
      | inl state₁ => exact (head_seqComp_inl R₁.machine R₂.machine state₁).symm
      | inr state₂ => exact (head_seqComp_inr R₁.machine R₂.machine state₂).symm)
  updateCode :=
    let sumState := S.sum R₁.state R₂.state
    let right : Q.Realizer (P.prod R₂.state bd.idx) (O.option sumState)
        (fun input ↦ Option.map Sum.inr (R₂.machine.update? input)) :=
      Q.compose R₂.updateCode (QO.map (QS.inr R₁.state R₂.state))
    let query : Q.Realizer (P.prod bd.pos (P.prod R₁.state bd.idx))
        (O.option sumState)
        (fun input ↦ Option.map Sum.inl (R₁.machine.update? input.2)) :=
      Q.compose (QP.snd bd.pos (P.prod R₁.state bd.idx))
        (Q.compose R₁.updateCode (QO.map (QS.inl R₁.state R₂.state)))
    let handoffInput : Q.Realizer (P.prod bd.out (P.prod R₁.state bd.idx))
        (P.prod R₂.state bd.idx)
        (fun input ↦ (R₂.machine.init input.1, input.2.2)) :=
      QP.pair
        (Q.compose (QP.fst bd.out (P.prod R₁.state bd.idx)) R₂.initCode)
        (Q.compose (QP.snd bd.out (P.prod R₁.state bd.idx))
          (QP.snd R₁.state bd.idx))
    let handoff := Q.compose handoffInput right
    let left : Q.Realizer (P.prod R₁.state bd.idx) (O.option sumState)
        (fun input ↦ Sum.elim
          (fun value ↦ Option.map Sum.inr
            (R₂.machine.update? (R₂.machine.init value, input.2)))
          (fun _ : p.A ↦ Option.map Sum.inl (R₁.machine.update? input))
          (R₁.machine.head input.1)) :=
      Q.compose
        (QuantitativeStepClass.HasProd.withInput Q QP
          (Q.compose (QP.fst R₁.state bd.idx) R₁.headCode))
        (QuantitativeStepClass.IsDistributive.elimContext Q QD handoff query)
    (QuantitativeStepClass.IsDistributive.elimContext Q QD left right).castFunction (by
      funext input
      obtain ⟨state, index⟩ := input
      cases state with
      | inl state₁ =>
          exact (update?_seqComp_inl R₁.machine R₂.machine state₁ index).symm
      | inr state₂ =>
          exact (update?_seqComp_inr R₁.machine R₂.machine state₂ index).symm)

end SeqComp

/-! ## Interface transport -/

section Wrap

variable [Q.HasCategory] [QS : Q.HasSum] [QO : Q.HasOption] [QP : Q.HasProd]
  {q : PFunctor.{u, u}} [DecidableEq q.A]

/-- Transport a quantitative realization along a lens carrying executable position and answer
pullback code.

The construction relabels the readout, partially pulls each tagged answer back to the source
interface, and only then executes the source transition. No resource bound is inferred. -/
@[implicit_reducible]
def wrap (R : QuantitativeRealization Q bd) (posRep : C.Str q.A) (idxRep : C.Str q.Idx)
    {lens : Lens p q} (hlens : lens.QuantitativelyAdmissible Q bd posRep idxRep) :
    QuantitativeRealization Q (bd.withInterface posRep idxRep) where
  machine := R.machine.wrap lens
  state := R.state
  initCode := R.initCode
  headCode := by
    let relabel := QuantitativeStepClass.HasSum.map Q QS (Q.identity bd.out) hlens.onPos
    exact (Q.compose R.headCode relabel).castFunction (by
      funext state
      exact (head_wrap R.machine lens state).symm)
  updateCode := by
    let pull : Q.Realizer (P.prod R.state idxRep) (O.option bd.idx) fun input ↦
        lens.pullHeadIdx B (R.machine.head input.1, input.2) :=
      Q.compose
        (QuantitativeStepClass.HasProd.pairRight Q QP R.headCode)
        hlens.onPull
    let sourceStep : Q.Realizer (P.prod bd.idx (P.prod R.state idxRep))
        (O.option R.state) fun input ↦ R.machine.update? (input.2.1, input.1) :=
      Q.compose
        (QP.pair
          (Q.compose (QP.snd bd.idx (P.prod R.state idxRep))
            (QP.fst R.state idxRep))
          (QP.fst bd.idx (P.prod R.state idxRep)))
        R.updateCode
    let pulledUpdate := Q.compose
      (QuantitativeStepClass.HasProd.withInput Q QP pull)
      (QO.bindContext sourceStep)
    exact pulledUpdate.castFunction (by
      funext input
      obtain ⟨state, position, direction⟩ := input
      exact (update?_wrap R.machine lens state position direction).symm)

end Wrap

end QuantitativeRealization

/-! ## Program-level closure -/

/-- An immediately returning program is quantitatively realizable from executable result code. -/
theorem isQuantitativelyRealizableBy_ofFn {f : A → B}
    [Q.HasSum] [Q.HasOption]
    (code : Q.Realizer bd.input bd.out f) :
    IsQuantitativelyRealizableBy Q bd fun input ↦ FreeM.pure (f input) := by
  refine ⟨QuantitativeRealization.ofFn code, ?_⟩
  change (DynComputation.ofFn (p := p) f).Implements _
  intro input
  rw [denote_ofFn]
  simp

namespace IsQuantitativelyRealizableBy

variable {program : A → FreeM p B}

/-- Quantitative realizability is closed under executable input precomposition. -/
theorem precomp [Q.HasCategory] {D : Type u} {inputRep : C.Str D} {f : D → A}
    (h : IsQuantitativelyRealizableBy Q bd program)
    (code : Q.Realizer inputRep bd.input f) :
    IsQuantitativelyRealizableBy Q (bd.withInput inputRep) (program ∘ f) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R.precomp code, ?_⟩
  change (R.machine.setInit (R.machine.init ∘ f)).Implements (program ∘ f)
  rw [← R.machine.contramapInput_eq_setInit f]
  exact hR.contramapInput f

/-- Quantitative realizability is closed under executable result postcomposition. -/
theorem mapResult {D : Type u} {outRep : C.Str D} {f : B → D}
    [Q.HasCategory] [Q.HasSum]
    (h : IsQuantitativelyRealizableBy Q bd program)
    (code : Q.Realizer bd.out outRep f) :
    IsQuantitativelyRealizableBy Q (bd.withOut outRep)
      fun input ↦ FreeM.map f (program input) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R.mapResult code, ?_⟩
  change (R.machine.mapResult f).Implements fun input ↦ FreeM.map f (program input)
  exact hR.mapResult f

section SeqComp

variable [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive]
  {D : Type u} {outRep : C.Str D}
  {next : B → FreeM p D}

/-- Quantitative realizability is closed under sequential composition of executable machines.

This is intentionally an unbounded theorem. A backend may derive a bounded or polynomial closure
theorem only after proving resource inequalities for its structural realizers. -/
theorem seqComp (first : IsQuantitativelyRealizableBy Q bd program)
    (second : IsQuantitativelyRealizableBy Q (bd.mid outRep) next) :
    IsQuantitativelyRealizableBy Q (bd.withOut outRep)
      fun input ↦ FreeM.bind (program input) next := by
  obtain ⟨R₁, hR₁⟩ := first
  obtain ⟨R₂, hR₂⟩ := second
  refine ⟨R₁.seqComp R₂, ?_⟩
  change (R₁.machine.seqComp R₂.machine).Implements _
  exact hR₁.seqComp hR₂

end SeqComp

section Wrap

variable [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption]
  {q : PFunctor.{u, u}} [DecidableEq q.A]

/-- Quantitative realizability is closed under executable interface transport. -/
theorem wrap (h : IsQuantitativelyRealizableBy Q bd program)
    (posRep : C.Str q.A) (idxRep : C.Str q.Idx) {lens : Lens p q}
    (hlens : lens.QuantitativelyAdmissible Q bd posRep idxRep) :
    IsQuantitativelyRealizableBy Q (bd.withInterface posRep idxRep)
      fun input ↦ (program input).mapLens lens := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R.wrap posRep idxRep hlens, ?_⟩
  change (R.machine.wrap lens).Implements _
  exact hR.wrap lens

end Wrap

end IsQuantitativelyRealizableBy

end DynSystem.DynComputation

end PFunctor
