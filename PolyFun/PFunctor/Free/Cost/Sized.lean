/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import PolyFun.PFunctor.Free.Cost.Measured
public import PolyFun.PFunctor.Free.Restrict
public import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Size-indexed cost contracts for measured programs

A fixed budget, `MeasuredProgram.CostAtMost B`, says nothing about growth. A program whose
completed paths have bounded cost meets some constant budget, and an exhaustive search over a
capped set of inputs is such a program. A size-indexed contract therefore fixes two things
independently of the program:

- A size measure on inputs, `size : Input → ℕ`.
- A budget envelope, `envelope : ℕ → ω`, a function of the size.

`CostWithin size envelope` says that every completed path of the program run on an input costs at
most the envelope at the size of that input. The cost of a path is the sum of the prices of the
declared operations it calls. A cost contract therefore bounds the total price of these calls and
nothing else. Growth of the envelope is a separate statement about a function `ℕ → ℕ`.
`PolyCost size` asks for a natural-number polynomial envelope, and `FamilyPolyCost` asks for one
polynomial for a whole parameter-indexed family. Neither bounds machine time.
`PolyFun.PFunctor.Free.Cost.Sized.Growth` relates them to `Cslib.PolynomiallyBounded` and gives
refutations of them from super-polynomial lower bounds. `OutputWithin` bounds the size of results in
the same way. The contracts compose along `MeasuredProgram.comp` when the inner results have an
output-size envelope and the outer envelope is monotone (`CostWithin.comp`, `OutputWithin.comp`,
`PolyCost.comp`, `FamilyPolyCost.comp`). A larger size measure keeps a contract whose envelope is
monotone (`CostWithin.mono_size`). Polynomial envelopes are monotone.

**Inputs, not views.** `CostAtMost` quantifies over every view. `CostWithin` quantifies over
inputs, and runs each input's own view, as `Realizes` does. The size is a function of the input,
and views that no input reaches are not constrained.

**All answers, or the allowed ones.** As in `CostAtMost`, the completed paths of `CostWithin` and
`OutputWithin` range over every answer of every call, not only over the answers of `answer`. A
program that returns an answer it receives has no output-size envelope when the answers are
unbounded in the result-size measure, for example a natural number measured by its value, whatever
`answer` returns.
`CostWithinUnder allows` and `OutputWithinUnder allows` range over the paths of the program
restricted to the answers `allows` admits (`FreeM.restrict`). Under `Answered`, which admits only
the answers of `answer`, the one remaining path is the path of the run, so the restricted contracts
bound the run (`costWithinUnder_answered_iff`, `outputWithinUnder_answered_iff`). A restriction
that admits fewer answers gives a weaker contract (`CostWithinUnder.mono_allows`): one that admits
no answer to a call leaves no completed path through that call. The restriction that admits
every answer gives the unrestricted contract (`costWithinUnder_true_iff`), so the unrestricted
contracts imply the restricted ones (`CostWithinUnder.of_costWithin`). The restricted contracts
compose along the composite restriction `CompAllows` (`CostWithinUnder.comp`), of which `Answered`
is an instance (`answered_comp`).

The polynomial classes come in both forms. Over every answer, an inner program that returns a
natural-number answer it receives, measured by its value, has no output-size envelope.
`PolyCost.comp` then does not apply, even when the run of the composite is cheap. `PolyCostUnder`,
`PolyOutputUnder`, `FamilyPolyCostUnder` and `FamilyPolyOutputUnder` ask for a polynomial envelope
over allowed answers, and compose along `CompAllows` (`PolyCostUnder.comp`,
`FamilyPolyCostUnder.comp`).

**Capped parameters.** A uniform budget is a constant envelope (`CostAtMost.costWithin`), hence a
constant polynomial (`PolyCost.of_costAtMost`). A program within a uniform budget meets every
envelope that is at least that budget at the size of each input (`CostAtMost.costWithin_of_le`).
Over finitely many parameters, every family whose members have fixed budgets has polynomial cost
(`FamilyPolyCost.of_finite`). Over capped parameters, the contract states the envelope as a named
function, such as `fun n => n ^ 2`.

**What stays uncharged.** The contracts inherit the accounting boundary of `MeasuredProgram`. The
view, the answering function and the code between calls are uncharged. A program can do an
exhaustive search in its view and meet the envelope `0` (`costWithin_ofFun`). The size measure is
not checked either. With a size such as `2 ^ (encoding length)`, an exhaustive search that makes one
call for each of `2 ^ (encoding length)` candidates meets a linear envelope. The existential
statement `∃ M, M.Realizes f ∧ M.PolyCost size` therefore holds for every function `f` and every
size measure `size`, and is no evidence of efficiency. A witness is the program whose view is `f`
and that returns its view. When the input type of `f` lies in the universe of its result type,
`ofFun f` is another witness. The prices are part of the program. A program that prices every
operation at `0`, for example `M.mapCost fun _ => 0`, keeps its run and meets the zero envelope. A
contract is informative only with stated prices, such as a unit price for each call. A contract on a
named program, with stated prices, a stated size measure and a stated envelope, bounds the total
price of the declared operations of that program. It does not bound the work of the uncharged parts,
and it does not check the size measure.

**Cost types.** `CostWithin` is stated for any ordered cost type, as `CostAtMost` is. The polynomial
contracts use `ℕ` with its usual addition and order. `ℕ` is canonically ordered, so no refund call
can pad a budget. A per-kind count in `K → ℕ` is read one kind at a time (`costWithin_pi_iff`,
through `mapCost`). Over a finite set of kinds, the sum of the per-kind envelopes bounds the sum of
the counts (`costWithin_finsetSum`).
-/

@[expose] public section

universe u w w' uI uI' uP uK

namespace PFunctor.FreeM.MeasuredProgram

variable {Input : Type uI} {Mid Result : Type u} {ω : Type w}

/-! ## Size-indexed contracts -/

/-- Every completed path of the program run on an input, over every answer of every call, costs at
most the envelope at the size of that input.

The contract bounds only the charges of the program's declared operations. The view, the answering
function and the code between calls are not charged. -/
def CostWithin [Add ω] [Zero ω] [LE ω] (M : MeasuredProgram Input Result ω) (size : Input → ℕ)
    (envelope : ℕ → ω) : Prop :=
  ∀ i (p : Path (M.program (M.view i))), Path.charge M.cost (M.program (M.view i)) p ≤
    envelope (size i)

/-- Every completed path of the program run on an input, over every answer of every call, returns
a result whose size is at most the envelope at the size of that input. -/
def OutputWithin (M : MeasuredProgram Input Result ω) (size : Input → ℕ)
    (resultSize : Result → ℕ) (envelope : ℕ → ℕ) : Prop :=
  ∀ i (p : Path (M.program (M.view i))), resultSize (output (M.program (M.view i)) p) ≤
    envelope (size i)

variable {M : MeasuredProgram Input Result ω} {size : Input → ℕ}

/-- A uniform budget is a constant envelope. -/
theorem CostAtMost.costWithin [Add ω] [Zero ω] [LE ω] {B : ω} (h : M.CostAtMost B)
    (size : Input → ℕ) : M.CostWithin size fun _ => B :=
  fun i => h (M.view i)

/-- A program within a uniform budget meets every envelope that is at least that budget at the
size of each input. -/
theorem CostAtMost.costWithin_of_le [Add ω] [Zero ω] [Preorder ω] {B : ω} (h : M.CostAtMost B)
    {envelope : ℕ → ω} (hB : ∀ i, B ≤ envelope (size i)) : M.CostWithin size envelope :=
  fun i p => (h _ p).trans (hB i)

theorem CostWithin.mono [Add ω] [Zero ω] [Preorder ω] {envelope envelope' : ℕ → ω}
    (h : M.CostWithin size envelope) (he : ∀ n, envelope n ≤ envelope' n) :
    M.CostWithin size envelope' :=
  fun i p => (h i p).trans (he _)

/-- A monotone envelope holds for every larger size measure. -/
theorem CostWithin.mono_size [Add ω] [Zero ω] [Preorder ω] {envelope : ℕ → ω}
    {size' : Input → ℕ} (h : M.CostWithin size envelope) (he : Monotone envelope)
    (hs : ∀ i, size i ≤ size' i) : M.CostWithin size' envelope :=
  fun i p => (h i p).trans (he (hs i))

theorem CostWithin.contramap [Add ω] [Zero ω] [LE ω] {Input' : Type uI'} {envelope : ℕ → ω}
    (h : M.CostWithin size envelope) (g : Input' → Input) :
    (M.contramap g).CostWithin (size ∘ g) envelope :=
  fun i => h (g i)

/-- A program with no operations meets the zero envelope, whatever it computes in its view. -/
theorem costWithin_ofFun [Add ω] [Zero ω] [Preorder ω] {Input : Type u} (f : Input → Result)
    (size : Input → ℕ) : (ofFun f (ω := ω)).CostWithin size fun _ => 0 :=
  (costAtMost_ofFun f).costWithin size

theorem OutputWithin.mono {resultSize : Result → ℕ} {envelope envelope' : ℕ → ℕ}
    (h : M.OutputWithin size resultSize envelope) (he : ∀ n, envelope n ≤ envelope' n) :
    M.OutputWithin size resultSize envelope' :=
  fun i p => (h i p).trans (he _)

theorem OutputWithin.mono_size {resultSize : Result → ℕ} {envelope : ℕ → ℕ} {size' : Input → ℕ}
    (h : M.OutputWithin size resultSize envelope) (he : Monotone envelope)
    (hs : ∀ i, size i ≤ size' i) : M.OutputWithin size' resultSize envelope :=
  fun i p => (h i p).trans (he (hs i))

theorem OutputWithin.contramap {Input' : Type uI'} {resultSize : Result → ℕ} {envelope : ℕ → ℕ}
    (h : M.OutputWithin size resultSize envelope) (g : Input' → Input) :
    (M.contramap g).OutputWithin (size ∘ g) resultSize envelope :=
  fun i => h (g i)

/-- A program with no operations returns `f` of its input. -/
theorem outputWithin_ofFun {Input : Type u} {f : Input → Result} {size : Input → ℕ}
    {resultSize : Result → ℕ} {envelope : ℕ → ℕ} (h : ∀ i, resultSize (f i) ≤ envelope (size i)) :
    (ofFun f (ω := ω)).OutputWithin size resultSize envelope :=
  fun i _ => h i

/-- **Sized composition.** The composite stays within the inner envelope plus the outer envelope
at the inner output-size envelope. -/
theorem CostWithin.comp [AddMonoid ω] [Preorder ω] [AddLeftMono ω] [AddRightMono ω]
    {outer : MeasuredProgram Mid Result ω} {inner : MeasuredProgram Input Mid ω}
    {midSize : Mid → ℕ} {outerEnvelope innerEnvelope : ℕ → ω} {growth : ℕ → ℕ}
    (ho : outer.CostWithin midSize outerEnvelope) (hoe : Monotone outerEnvelope)
    (hi : inner.CostWithin size innerEnvelope) (hg : inner.OutputWithin size midSize growth) :
    (outer.comp inner).CostWithin size fun n => innerEnvelope n + outerEnvelope (growth n) :=
  fun i => Path.charge_bind_mapLens_le_of_output _ _ _ _ (fun _ => rfl) (fun _ _ => rfl) (hi i)
    fun p q => (ho _ q).trans (hoe (hg i p))

/-- Output-size envelopes compose. -/
theorem OutputWithin.comp {outer : MeasuredProgram Mid Result ω}
    {inner : MeasuredProgram Input Mid ω} {midSize : Mid → ℕ} {resultSize : Result → ℕ}
    {outerGrowth innerGrowth : ℕ → ℕ} (ho : outer.OutputWithin midSize resultSize outerGrowth)
    (hoe : Monotone outerGrowth) (hi : inner.OutputWithin size midSize innerGrowth) :
    (outer.comp inner).OutputWithin size resultSize (outerGrowth ∘ innerGrowth) := fun i q => by
  obtain ⟨p, r, hq⟩ := Path.exists_output_bind_mapLens (inner.program (inner.view i))
    (innerLens outer inner _) (fun m => outer.program (outer.view m))
    (fun m => outerLens outer inner _ (outer.view m)) q
  exact (congrArg resultSize hq).trans_le ((ho _ r).trans (hoe (hi i p)))

/-! ## Contracts over allowed answers -/

/-- Every completed path of the program run on an input, restricted to the answers `allows` admits
at that input's view, costs at most the envelope at the size of that input.

The contract bounds only the charges of the program's declared operations. The view, the answering
function and the code between calls are not charged.

No completed path passes a call none of whose answers `allows` admits. An `allows` that admits no
answer therefore leaves no completed path through a call, so the contract constrains only the paths
that make no call. Under an `allows` that admits the answers of `answer`, the contract bounds the
run (`CostWithinUnder.answered`). -/
def CostWithinUnder [Add ω] [Zero ω] [LE ω] (M : MeasuredProgram Input Result ω)
    (allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop) (size : Input → ℕ)
    (envelope : ℕ → ω) : Prop :=
  ∀ i (p : Path ((M.program (M.view i)).restrict (allows (M.view i)))),
    Path.charge M.cost _ p ≤ envelope (size i)

/-- Every completed path of the program run on an input, restricted to the answers `allows` admits
at that input's view, returns a result whose size is at most the envelope at the size of that
input.

No completed path passes a call none of whose answers `allows` admits. An `allows` that admits no
answer therefore leaves no completed path through a call, so the contract constrains only the paths
that make no call. Under an `allows` that admits the answers of `answer`, the contract bounds the
result of the run (`OutputWithinUnder.answered`). -/
def OutputWithinUnder (M : MeasuredProgram Input Result ω)
    (allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop) (size : Input → ℕ)
    (resultSize : Result → ℕ) (envelope : ℕ → ℕ) : Prop :=
  ∀ i (p : Path ((M.program (M.view i)).restrict (allows (M.view i)))),
    resultSize (output _ p) ≤ envelope (size i)

/-- The answers the program's answering function gives. -/
def Answered (M : MeasuredProgram Input Result ω) (v : M.View) (o : M.Op) (b : M.spec v o) :
    Prop :=
  b = M.answer v o

variable {allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop}

/-- Admitting fewer answers keeps the cost contract. -/
theorem CostWithinUnder.mono_allows [Add ω] [Zero ω] [LE ω] {envelope : ℕ → ω}
    {allows' : (v : M.View) → (o : M.Op) → M.spec v o → Prop}
    (h : M.CostWithinUnder allows size envelope) (hle : ∀ v o b, allows' v o b → allows v o b) :
    M.CostWithinUnder allows' size envelope := by
  intro i
  rw [← FreeM.mapLens_restrictInclusion (hle (M.view i))]
  exact fun q => (Path.charge_pullMapLens _ (d := M.cost) _ q).trans_le (h i _)

/-- Admitting fewer answers keeps the output contract. -/
theorem OutputWithinUnder.mono_allows {resultSize : Result → ℕ} {envelope : ℕ → ℕ}
    {allows' : (v : M.View) → (o : M.Op) → M.spec v o → Prop}
    (h : M.OutputWithinUnder allows size resultSize envelope)
    (hle : ∀ v o b, allows' v o b → allows v o b) :
    M.OutputWithinUnder allows' size resultSize envelope := by
  intro i
  rw [← FreeM.mapLens_restrictInclusion (hle (M.view i))]
  exact fun q => (congrArg resultSize (Path.output_pullMapLens _ _ q).symm).trans_le (h i _)

/-- Over every answer, the restricted cost contract is the cost contract. -/
theorem costWithinUnder_true_iff [Add ω] [Zero ω] [LE ω] {envelope : ℕ → ω} :
    M.CostWithinUnder (fun _ _ _ => True) size envelope ↔ M.CostWithin size envelope := by
  refine ⟨fun h i => ?_, fun h i q => ?_⟩
  · rw [← FreeM.mapLens_unrestrict (allows := fun _ _ => True) (fun _ _ => trivial)
      (M.program (M.view i))]
    exact fun p => (Path.charge_pullMapLens _ (d := M.cost) _ p).trans_le (h i _)
  · exact (Path.charge_pullMapLens (Lens.restrict ⟨M.Op, M.spec (M.view i)⟩ _) (d := M.cost)
      (M.program (M.view i)) q).trans_le (h i _)

/-- Over every answer, the restricted output contract is the output contract. -/
theorem outputWithinUnder_true_iff {resultSize : Result → ℕ} {envelope : ℕ → ℕ} :
    M.OutputWithinUnder (fun _ _ _ => True) size resultSize envelope ↔
      M.OutputWithin size resultSize envelope := by
  refine ⟨fun h i => ?_, fun h i q => ?_⟩
  · rw [← FreeM.mapLens_unrestrict (allows := fun _ _ => True) (fun _ _ => trivial)
      (M.program (M.view i))]
    exact fun p => (congrArg resultSize (Path.output_pullMapLens _ _ p).symm).trans_le (h i _)
  · exact (congrArg resultSize (Path.output_pullMapLens
      (Lens.restrict ⟨M.Op, M.spec (M.view i)⟩ _) (M.program (M.view i)) q).symm).trans_le (h i _)

theorem CostWithinUnder.of_costWithin [Add ω] [Zero ω] [LE ω] {envelope : ℕ → ω}
    (h : M.CostWithin size envelope) (allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop) :
    M.CostWithinUnder allows size envelope :=
  (costWithinUnder_true_iff.2 h).mono_allows fun _ _ _ _ => trivial

theorem OutputWithinUnder.of_outputWithin {resultSize : Result → ℕ} {envelope : ℕ → ℕ}
    (h : M.OutputWithin size resultSize envelope)
    (allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop) :
    M.OutputWithinUnder allows size resultSize envelope :=
  (outputWithinUnder_true_iff.2 h).mono_allows fun _ _ _ _ => trivial

theorem CostWithinUnder.mono [Add ω] [Zero ω] [Preorder ω] {envelope envelope' : ℕ → ω}
    (h : M.CostWithinUnder allows size envelope) (he : ∀ n, envelope n ≤ envelope' n) :
    M.CostWithinUnder allows size envelope' :=
  fun i p => (h i p).trans (he _)

theorem OutputWithinUnder.mono {resultSize : Result → ℕ} {envelope envelope' : ℕ → ℕ}
    (h : M.OutputWithinUnder allows size resultSize envelope)
    (he : ∀ n, envelope n ≤ envelope' n) : M.OutputWithinUnder allows size resultSize envelope' :=
  fun i p => (h i p).trans (he _)

theorem CostWithinUnder.mono_size [Add ω] [Zero ω] [Preorder ω] {envelope : ℕ → ω}
    {size' : Input → ℕ} (h : M.CostWithinUnder allows size envelope) (he : Monotone envelope)
    (hs : ∀ i, size i ≤ size' i) : M.CostWithinUnder allows size' envelope :=
  fun i p => (h i p).trans (he (hs i))

theorem OutputWithinUnder.mono_size {resultSize : Result → ℕ} {envelope : ℕ → ℕ}
    {size' : Input → ℕ} (h : M.OutputWithinUnder allows size resultSize envelope)
    (he : Monotone envelope) (hs : ∀ i, size i ≤ size' i) :
    M.OutputWithinUnder allows size' resultSize envelope :=
  fun i p => (h i p).trans (he (hs i))

theorem CostWithinUnder.contramap [Add ω] [Zero ω] [LE ω] {Input' : Type uI'}
    {envelope : ℕ → ω} (h : M.CostWithinUnder allows size envelope) (g : Input' → Input) :
    (M.contramap g).CostWithinUnder allows (size ∘ g) envelope :=
  fun i => h (g i)

theorem OutputWithinUnder.contramap {Input' : Type uI'} {resultSize : Result → ℕ}
    {envelope : ℕ → ℕ} (h : M.OutputWithinUnder allows size resultSize envelope)
    (g : Input' → Input) :
    (M.contramap g).OutputWithinUnder allows (size ∘ g) resultSize envelope :=
  fun i => h (g i)

/-- The only completed path of the program restricted to the answers of `answer` is the path of
the run. -/
theorem pullMapLens_restrict_answered (M : MeasuredProgram Input Result ω) (v : M.View)
    (q : Path ((M.program v).restrict (M.Answered v))) :
    Path.pullMapLens (Lens.restrict ⟨M.Op, M.spec v⟩ (M.Answered v)) (M.program v) q =
      Path.ofHandler (M.answer v) (M.program v) := by
  have : ∀ a, Subsingleton ((PFunctor.restrict ⟨M.Op, M.spec v⟩ (M.Answered v)).B a) :=
    fun _ => ⟨fun ⟨_, h₁⟩ ⟨_, h₂⟩ => Subtype.ext (h₁.trans h₂.symm)⟩
  rw [Subsingleton.elim q (Path.ofHandler (P := PFunctor.restrict ⟨M.Op, M.spec v⟩ (M.Answered v))
    (fun a => ⟨M.answer v a, rfl⟩) _)]
  generalize M.program v = x
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    exact congrArg (fun p => (⟨M.answer v a, p⟩ : Path (FreeM.liftBind a r))) (ih _)

/-- Over the answers of `answer`, the cost contract bounds the charge of the path of the run. -/
theorem costWithinUnder_answered_iff [Add ω] [Zero ω] [LE ω] {envelope : ℕ → ω} :
    M.CostWithinUnder M.Answered size envelope ↔ ∀ i,
      Path.charge M.cost _ (Path.ofHandler (M.answer (M.view i)) (M.program (M.view i))) ≤
        envelope (size i) := by
  have key : ∀ i (q : Path ((M.program (M.view i)).restrict (M.Answered (M.view i)))),
      Path.charge M.cost _ q =
        Path.charge M.cost _ (Path.ofHandler (M.answer (M.view i)) (M.program (M.view i))) :=
    fun i q => (Path.charge_pullMapLens (Lens.restrict ⟨M.Op, M.spec (M.view i)⟩ _)
      (d := M.cost) _ q).trans (congrArg _ (pullMapLens_restrict_answered M _ q))
  refine ⟨fun h i => ?_, fun h i q => (key i q).trans_le (h i)⟩
  exact (key i (Path.ofHandler (P := PFunctor.restrict ⟨M.Op, M.spec (M.view i)⟩
    (M.Answered (M.view i))) (fun a => ⟨M.answer (M.view i) a, rfl⟩) _)).symm.trans_le (h i _)

/-- Over the answers of `answer`, the output contract bounds the result of the run. -/
theorem outputWithinUnder_answered_iff {resultSize : Result → ℕ} {envelope : ℕ → ℕ} :
    M.OutputWithinUnder M.Answered size resultSize envelope ↔
      ∀ i, resultSize (M.run i) ≤ envelope (size i) := by
  have key : ∀ i (q : Path ((M.program (M.view i)).restrict (M.Answered (M.view i)))),
      output _ q = M.run i := fun i q => by
    rw [run_eq_output, ← pullMapLens_restrict_answered M _ q]
    exact (Path.output_pullMapLens (Lens.restrict ⟨M.Op, M.spec (M.view i)⟩ _) _ q).symm
  refine ⟨fun h i => ?_, fun h i q => (congrArg resultSize (key i q)).trans_le (h i)⟩
  exact (congrArg resultSize (key i (Path.ofHandler (P := PFunctor.restrict
    ⟨M.Op, M.spec (M.view i)⟩ (M.Answered (M.view i))) (fun a => ⟨M.answer (M.view i) a, rfl⟩)
    _))).symm.trans_le (h i _)

/-- An `allows` that admits the answers of `answer` gives the cost contract over them. -/
theorem CostWithinUnder.answered [Add ω] [Zero ω] [LE ω] {envelope : ℕ → ω}
    (h : M.CostWithinUnder allows size envelope) (ha : ∀ v o, allows v o (M.answer v o)) :
    M.CostWithinUnder M.Answered size envelope :=
  h.mono_allows fun v o _ hb => hb ▸ ha v o

/-- An `allows` that admits the answers of `answer` gives the output contract over them. -/
theorem OutputWithinUnder.answered {resultSize : Result → ℕ} {envelope : ℕ → ℕ}
    (h : M.OutputWithinUnder allows size resultSize envelope)
    (ha : ∀ v o, allows v o (M.answer v o)) :
    M.OutputWithinUnder M.Answered size resultSize envelope :=
  h.mono_allows fun v o _ hb => hb ▸ ha v o

/-- The restriction of the composite interface that admits, at each operation, the answers its own
restriction admits at the view it is tagged with. -/
def CompAllows (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (innerAllows : (v : inner.View) → (o : inner.Op) → inner.spec v o → Prop)
    (outerAllows : (v : outer.View) → (o : outer.Op) → outer.spec v o → Prop) (v : inner.View) :
    (o : (outer.comp inner).Op) → CompSpec outer inner v o → Prop
  | .inl ⟨v, o⟩ => innerAllows v o
  | .inr ⟨v', o⟩ => outerAllows v' o

/-- The answers of the composite are the answers of the parts. -/
theorem answered_comp (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω) :
    (outer.comp inner).Answered = CompAllows outer inner inner.Answered outer.Answered := by
  funext v o
  rcases o with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

/-- `innerLens` between the restricted interfaces. -/
def innerLensUnder (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (innerAllows : (v : inner.View) → (o : inner.Op) → inner.spec v o → Prop)
    (outerAllows : (v : outer.View) → (o : outer.Op) → outer.spec v o → Prop) (v : inner.View) :
    Lens ((PFunctor.mk inner.Op (inner.spec v)).restrict (innerAllows v))
      ((PFunctor.mk _ (CompSpec outer inner v)).restrict
        (CompAllows outer inner innerAllows outerAllows v)) :=
  ⟨fun o => Sum.inl ⟨v, o⟩, fun _ b => b⟩

/-- `outerLens` between the restricted interfaces. -/
def outerLensUnder (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (innerAllows : (v : inner.View) → (o : inner.Op) → inner.spec v o → Prop)
    (outerAllows : (v : outer.View) → (o : outer.Op) → outer.spec v o → Prop) (v : inner.View)
    (v' : outer.View) :
    Lens ((PFunctor.mk outer.Op (outer.spec v')).restrict (outerAllows v'))
      ((PFunctor.mk _ (CompSpec outer inner v)).restrict
        (CompAllows outer inner innerAllows outerAllows v)) :=
  ⟨fun o => Sum.inr ⟨v', o⟩, fun _ b => b⟩

/-- The restricted composite program is the composite of the restricted programs. -/
theorem restrict_program_comp (outer : MeasuredProgram Mid Result ω)
    (inner : MeasuredProgram Input Mid ω)
    (innerAllows : (v : inner.View) → (o : inner.Op) → inner.spec v o → Prop)
    (outerAllows : (v : outer.View) → (o : outer.Op) → outer.spec v o → Prop) (v : inner.View) :
    ((outer.comp inner).program v).restrict (CompAllows outer inner innerAllows outerAllows v) =
      FreeM.bind (((inner.program v).restrict (innerAllows v)).mapLens
          (innerLensUnder outer inner innerAllows outerAllows v)) fun m =>
        ((outer.program (outer.view m)).restrict (outerAllows (outer.view m))).mapLens
          (outerLensUnder outer inner innerAllows outerAllows v (outer.view m)) := by
  simp only [FreeM.restrict, comp, mapLens_bind', mapLens_mapLens]
  rfl

/-- **Sized composition over allowed answers.** Over `CompAllows`, the composite stays within the
inner envelope plus the outer envelope at the inner output-size envelope, when the outer envelope
is monotone. -/
theorem CostWithinUnder.comp [AddMonoid ω] [Preorder ω] [AddLeftMono ω] [AddRightMono ω]
    {outer : MeasuredProgram Mid Result ω} {inner : MeasuredProgram Input Mid ω}
    {innerAllows : (v : inner.View) → (o : inner.Op) → inner.spec v o → Prop}
    {outerAllows : (v : outer.View) → (o : outer.Op) → outer.spec v o → Prop}
    {midSize : Mid → ℕ} {outerEnvelope innerEnvelope : ℕ → ω} {growth : ℕ → ℕ}
    (ho : outer.CostWithinUnder outerAllows midSize outerEnvelope) (hoe : Monotone outerEnvelope)
    (hi : inner.CostWithinUnder innerAllows size innerEnvelope)
    (hg : inner.OutputWithinUnder innerAllows size midSize growth) :
    (outer.comp inner).CostWithinUnder (CompAllows outer inner innerAllows outerAllows) size
      fun n => innerEnvelope n + outerEnvelope (growth n) := by
  intro i
  change ∀ q : Path (((outer.comp inner).program (inner.view i)).restrict
      (CompAllows outer inner innerAllows outerAllows (inner.view i))),
    Path.charge _ (((outer.comp inner).program (inner.view i)).restrict
      (CompAllows outer inner innerAllows outerAllows (inner.view i))) q ≤ _
  rw [restrict_program_comp]
  exact Path.charge_bind_mapLens_le_of_output _ _ _ _ (fun _ => rfl) (fun _ _ => rfl) (hi i)
    fun p q => (ho _ q).trans (hoe (hg i p))

/-- Output-size envelopes compose over allowed answers. -/
theorem OutputWithinUnder.comp {outer : MeasuredProgram Mid Result ω}
    {inner : MeasuredProgram Input Mid ω}
    {innerAllows : (v : inner.View) → (o : inner.Op) → inner.spec v o → Prop}
    {outerAllows : (v : outer.View) → (o : outer.Op) → outer.spec v o → Prop}
    {midSize : Mid → ℕ} {resultSize : Result → ℕ} {outerGrowth innerGrowth : ℕ → ℕ}
    (ho : outer.OutputWithinUnder outerAllows midSize resultSize outerGrowth)
    (hoe : Monotone outerGrowth)
    (hi : inner.OutputWithinUnder innerAllows size midSize innerGrowth) :
    (outer.comp inner).OutputWithinUnder (CompAllows outer inner innerAllows outerAllows) size
      resultSize (outerGrowth ∘ innerGrowth) := by
  intro i
  change ∀ q : Path (((outer.comp inner).program (inner.view i)).restrict
      (CompAllows outer inner innerAllows outerAllows (inner.view i))),
    resultSize (output (((outer.comp inner).program (inner.view i)).restrict
      (CompAllows outer inner innerAllows outerAllows (inner.view i))) q) ≤ _
  rw [restrict_program_comp]
  intro q
  obtain ⟨p, r, hq⟩ := Path.exists_output_bind_mapLens _ _ _ _ q
  exact (congrArg resultSize hq).trans_le ((ho _ r).trans (hoe (hi i p)))

/-! ## Changing the cost type -/

/-- A sized contract pushes forward along a monotone additive map. -/
theorem CostWithin.mapCost {ω' : Type w'} [AddMonoid ω] [AddMonoid ω'] [Preorder ω] [Preorder ω']
    {envelope : ℕ → ω} (h : M.CostWithin size envelope) (φ : ω →+ ω') (hφ : Monotone φ) :
    (M.mapCost φ).CostWithin size (φ ∘ envelope) := fun i p =>
  (Path.charge_map_addMonoidHom φ (c := M.cost) (M.program (M.view i)) p).trans_le (hφ (h i p))

/-- A per-kind contract is a contract for each kind. -/
theorem costWithin_pi_iff {K : Type uK} {ν : Type w} [AddMonoid ν] [Preorder ν]
    {M : MeasuredProgram Input Result (K → ν)} {envelope : ℕ → K → ν} :
    M.CostWithin size envelope ↔
      ∀ k, (M.mapCost fun c => c k).CostWithin size fun n => envelope n k := by
  constructor
  · exact fun h k i p =>
      (Path.charge_apply M.cost (M.program (M.view i)) p k).symm.trans_le (h i p k)
  · exact fun h i p k => (Path.charge_apply M.cost (M.program (M.view i)) p k).trans_le (h k i p)

/-- Over a finite set of kinds, the per-kind envelopes add up to an envelope of the program priced
by the sum of its per-kind prices. -/
theorem costWithin_finsetSum {K : Type uK} {ν : Type w} [AddCommMonoid ν] [PartialOrder ν]
    [IsOrderedAddMonoid ν] {M : MeasuredProgram Input Result (K → ν)} (s : Finset K)
    {envelope : K → ℕ → ν} (h : ∀ k ∈ s, (M.mapCost fun c => c k).CostWithin size (envelope k)) :
    (M.mapCost fun c => ∑ k ∈ s, c k).CostWithin size fun n => ∑ k ∈ s, envelope k n :=
  fun i (p : Path (M.program (M.view i))) => by
    change Path.charge (fun o => ∑ k ∈ s, M.cost o k) (M.program (M.view i)) p ≤
      ∑ k ∈ s, envelope k (size i)
    rw [Path.charge_finsetSum]
    exact Finset.sum_le_sum fun k hk => h k hk i p

/-! ## Polynomial contracts -/

/-- One natural-number polynomial `q` bounds the charges of the program's declared operations. On
each input `i`, every completed path, over every answer of every call, has a total price at most
`q.eval (size i)`. The view, the answering function and the code between calls are not charged. -/
def PolyCost (M : MeasuredProgram Input Result ℕ) (size : Input → ℕ) : Prop :=
  ∃ q : Polynomial ℕ, M.CostWithin size q.eval

/-- The program's results have size at most a natural-number polynomial in the size of its
input. -/
def PolyOutput (M : MeasuredProgram Input Result ω) (size : Input → ℕ) (resultSize : Result → ℕ) :
    Prop :=
  ∃ q : Polynomial ℕ, M.OutputWithin size resultSize q.eval

/-- Every program with a fixed budget has polynomial cost, in any size measure: a uniform budget is
a constant polynomial. -/
theorem PolyCost.of_costAtMost {M : MeasuredProgram Input Result ℕ} {B : ℕ} (h : M.CostAtMost B)
    (size : Input → ℕ) : M.PolyCost size :=
  ⟨Polynomial.C B, (h.costWithin size).mono fun _ => by simp⟩

theorem PolyCost.mono_size {M : MeasuredProgram Input Result ℕ} {size' : Input → ℕ}
    (h : M.PolyCost size) (hs : ∀ i, size i ≤ size' i) : M.PolyCost size' :=
  let ⟨q, hq⟩ := h
  ⟨q, hq.mono_size (Polynomial.monotone_eval _) hs⟩

theorem PolyCost.contramap {M : MeasuredProgram Input Result ℕ} {Input' : Type uI'}
    (h : M.PolyCost size) (g : Input' → Input) : (M.contramap g).PolyCost (size ∘ g) :=
  let ⟨q, hq⟩ := h
  ⟨q, hq.contramap g⟩

theorem PolyOutput.mono_size {resultSize : Result → ℕ} {size' : Input → ℕ}
    (h : M.PolyOutput size resultSize) (hs : ∀ i, size i ≤ size' i) :
    M.PolyOutput size' resultSize :=
  let ⟨q, hq⟩ := h
  ⟨q, hq.mono_size (Polynomial.monotone_eval _) hs⟩

theorem PolyOutput.contramap {Input' : Type uI'} {resultSize : Result → ℕ}
    (h : M.PolyOutput size resultSize) (g : Input' → Input) :
    (M.contramap g).PolyOutput (size ∘ g) resultSize :=
  let ⟨q, hq⟩ := h
  ⟨q, hq.contramap g⟩

/-- Polynomial output sizes compose. -/
theorem PolyOutput.comp {outer : MeasuredProgram Mid Result ω}
    {inner : MeasuredProgram Input Mid ω} {midSize : Mid → ℕ} {resultSize : Result → ℕ}
    (ho : outer.PolyOutput midSize resultSize) (hi : inner.PolyOutput size midSize) :
    (outer.comp inner).PolyOutput size resultSize := by
  obtain ⟨p, hp⟩ := ho
  obtain ⟨q, hq⟩ := hi
  exact ⟨p.comp q, (hp.comp (Polynomial.monotone_eval _) hq).mono fun n => by
    simp [Polynomial.eval_comp]⟩

/-- Polynomial contracts compose when the inner output size grows polynomially. -/
theorem PolyCost.comp {outer : MeasuredProgram Mid Result ℕ} {inner : MeasuredProgram Input Mid ℕ}
    {midSize : Mid → ℕ} (ho : outer.PolyCost midSize) (hi : inner.PolyCost size)
    (hg : inner.PolyOutput size midSize) : (outer.comp inner).PolyCost size := by
  obtain ⟨p, hp⟩ := ho
  obtain ⟨q, hq⟩ := hi
  obtain ⟨r, hr⟩ := hg
  exact ⟨q + p.comp r, (hp.comp (Polynomial.monotone_eval _) hq hr).mono fun n => by
    simp [Polynomial.eval_comp]⟩

/-! ## Polynomial contracts over allowed answers -/

/-- One natural-number polynomial `q` bounds the charges of the declared operations of the program
restricted to the answers `allows` admits. On each input `i`, every completed path of the restricted
program has a total price at most `q.eval (size i)`. The view, the answering function and the code
between calls are not charged. -/
def PolyCostUnder (M : MeasuredProgram Input Result ℕ)
    (allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop) (size : Input → ℕ) : Prop :=
  ∃ q : Polynomial ℕ, M.CostWithinUnder allows size q.eval

/-- Restricted to the answers `allows` admits, the program's results have size at most a
natural-number polynomial in the size of its input. -/
def PolyOutputUnder (M : MeasuredProgram Input Result ω)
    (allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop) (size : Input → ℕ)
    (resultSize : Result → ℕ) : Prop :=
  ∃ q : Polynomial ℕ, M.OutputWithinUnder allows size resultSize q.eval

/-- Over every answer, the restricted polynomial cost contract is the polynomial cost contract. -/
theorem polyCostUnder_true_iff {M : MeasuredProgram Input Result ℕ} :
    M.PolyCostUnder (fun _ _ _ => True) size ↔ M.PolyCost size :=
  exists_congr fun _ => costWithinUnder_true_iff

/-- Over every answer, the restricted polynomial output contract is the polynomial output
contract. -/
theorem polyOutputUnder_true_iff {resultSize : Result → ℕ} :
    M.PolyOutputUnder (fun _ _ _ => True) size resultSize ↔ M.PolyOutput size resultSize :=
  exists_congr fun _ => outputWithinUnder_true_iff

theorem PolyCostUnder.of_polyCost {M : MeasuredProgram Input Result ℕ} (h : M.PolyCost size)
    (allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop) : M.PolyCostUnder allows size :=
  let ⟨q, hq⟩ := h
  ⟨q, .of_costWithin hq allows⟩

theorem PolyOutputUnder.of_polyOutput {resultSize : Result → ℕ}
    (h : M.PolyOutput size resultSize) (allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop) :
    M.PolyOutputUnder allows size resultSize :=
  let ⟨q, hq⟩ := h
  ⟨q, .of_outputWithin hq allows⟩

/-- Admitting fewer answers keeps the polynomial cost contract. -/
theorem PolyCostUnder.mono_allows {M : MeasuredProgram Input Result ℕ}
    {allows allows' : (v : M.View) → (o : M.Op) → M.spec v o → Prop}
    (h : M.PolyCostUnder allows size) (hle : ∀ v o b, allows' v o b → allows v o b) :
    M.PolyCostUnder allows' size :=
  let ⟨q, hq⟩ := h
  ⟨q, hq.mono_allows hle⟩

/-- Admitting fewer answers keeps the polynomial output contract. -/
theorem PolyOutputUnder.mono_allows {resultSize : Result → ℕ}
    {allows' : (v : M.View) → (o : M.Op) → M.spec v o → Prop}
    (h : M.PolyOutputUnder allows size resultSize) (hle : ∀ v o b, allows' v o b → allows v o b) :
    M.PolyOutputUnder allows' size resultSize :=
  let ⟨q, hq⟩ := h
  ⟨q, hq.mono_allows hle⟩

theorem PolyCostUnder.mono_size {M : MeasuredProgram Input Result ℕ}
    {allows : (v : M.View) → (o : M.Op) → M.spec v o → Prop} {size' : Input → ℕ}
    (h : M.PolyCostUnder allows size) (hs : ∀ i, size i ≤ size' i) :
    M.PolyCostUnder allows size' :=
  let ⟨q, hq⟩ := h
  ⟨q, hq.mono_size (Polynomial.monotone_eval _) hs⟩

theorem PolyOutputUnder.mono_size {resultSize : Result → ℕ} {size' : Input → ℕ}
    (h : M.PolyOutputUnder allows size resultSize) (hs : ∀ i, size i ≤ size' i) :
    M.PolyOutputUnder allows size' resultSize :=
  let ⟨q, hq⟩ := h
  ⟨q, hq.mono_size (Polynomial.monotone_eval _) hs⟩

/-- Polynomial output sizes over allowed answers compose along `CompAllows`. -/
theorem PolyOutputUnder.comp {outer : MeasuredProgram Mid Result ω}
    {inner : MeasuredProgram Input Mid ω}
    {innerAllows : (v : inner.View) → (o : inner.Op) → inner.spec v o → Prop}
    {outerAllows : (v : outer.View) → (o : outer.Op) → outer.spec v o → Prop}
    {midSize : Mid → ℕ} {resultSize : Result → ℕ}
    (ho : outer.PolyOutputUnder outerAllows midSize resultSize)
    (hi : inner.PolyOutputUnder innerAllows size midSize) :
    (outer.comp inner).PolyOutputUnder (CompAllows outer inner innerAllows outerAllows) size
      resultSize := by
  obtain ⟨p, hp⟩ := ho
  obtain ⟨q, hq⟩ := hi
  exact ⟨p.comp q, (hp.comp (Polynomial.monotone_eval _) hq).mono fun n => by
    simp [Polynomial.eval_comp]⟩

/-- Polynomial contracts over allowed answers compose along `CompAllows` when the inner output
size over allowed answers grows polynomially. -/
theorem PolyCostUnder.comp {outer : MeasuredProgram Mid Result ℕ}
    {inner : MeasuredProgram Input Mid ℕ}
    {innerAllows : (v : inner.View) → (o : inner.Op) → inner.spec v o → Prop}
    {outerAllows : (v : outer.View) → (o : outer.Op) → outer.spec v o → Prop}
    {midSize : Mid → ℕ} (ho : outer.PolyCostUnder outerAllows midSize)
    (hi : inner.PolyCostUnder innerAllows size)
    (hg : inner.PolyOutputUnder innerAllows size midSize) :
    (outer.comp inner).PolyCostUnder (CompAllows outer inner innerAllows outerAllows) size := by
  obtain ⟨p, hp⟩ := ho
  obtain ⟨q, hq⟩ := hi
  obtain ⟨r, hr⟩ := hg
  exact ⟨q + p.comp r, (hp.comp (Polynomial.monotone_eval _) hq hr).mono fun n => by
    simp [Polynomial.eval_comp]⟩

/-! ## Families -/

section Family

variable {ι : Type uP} {Input : ι → Type uI} {Mid Result : ι → Type u}

/-- One natural-number polynomial `q` bounds the charges of the declared operations of every member
of a parameter-indexed family. On each input `i` of each member `M π`, every completed path, over
every answer of every call, has a total price at most `q.eval (size π i)`. The view, the answering
function and the code between calls are not charged. -/
def FamilyPolyCost (M : ∀ π, MeasuredProgram (Input π) (Result π) ℕ) (size : ∀ π, Input π → ℕ) :
    Prop :=
  ∃ q : Polynomial ℕ, ∀ π, (M π).CostWithin (size π) q.eval

/-- One polynomial bounds the result sizes of every member of a parameter-indexed family. -/
def FamilyPolyOutput (M : ∀ π, MeasuredProgram (Input π) (Result π) ω)
    (size : ∀ π, Input π → ℕ) (resultSize : ∀ π, Result π → ℕ) : Prop :=
  ∃ q : Polynomial ℕ, ∀ π, (M π).OutputWithin (size π) (resultSize π) q.eval

/-- Over finitely many parameters, every family whose members have fixed budgets has polynomial
cost. -/
theorem FamilyPolyCost.of_finite [Finite ι] {M : ∀ π, MeasuredProgram (Input π) (Result π) ℕ}
    {B : ι → ℕ} (h : ∀ π, (M π).CostAtMost (B π)) (size : ∀ π, Input π → ℕ) :
    FamilyPolyCost M size := by
  obtain ⟨N, hN⟩ := (Set.finite_range B).bddAbove
  exact ⟨Polynomial.C N, fun π => ((h π).costWithin (size π)).mono fun _ => by
    simpa using hN ⟨π, rfl⟩⟩

theorem FamilyPolyCost.mono_size {M : ∀ π, MeasuredProgram (Input π) (Result π) ℕ}
    {size size' : ∀ π, Input π → ℕ} (h : FamilyPolyCost M size)
    (hs : ∀ π i, size π i ≤ size' π i) : FamilyPolyCost M size' :=
  let ⟨q, hq⟩ := h
  ⟨q, fun π => (hq π).mono_size (Polynomial.monotone_eval _) (hs π)⟩

/-- Families with polynomial cost compose memberwise when the inner output sizes grow
polynomially. -/
theorem FamilyPolyCost.comp {outer : ∀ π, MeasuredProgram (Mid π) (Result π) ℕ}
    {inner : ∀ π, MeasuredProgram (Input π) (Mid π) ℕ} {size : ∀ π, Input π → ℕ}
    {midSize : ∀ π, Mid π → ℕ} (ho : FamilyPolyCost outer midSize)
    (hi : FamilyPolyCost inner size) (hg : FamilyPolyOutput inner size midSize) :
    FamilyPolyCost (fun π => (outer π).comp (inner π)) size := by
  obtain ⟨p, hp⟩ := ho
  obtain ⟨q, hq⟩ := hi
  obtain ⟨r, hr⟩ := hg
  exact ⟨q + p.comp r, fun π => ((hp π).comp (Polynomial.monotone_eval _) (hq π)
    (hr π)).mono fun n => by simp [Polynomial.eval_comp]⟩

/-- Families with polynomial output sizes compose memberwise. -/
theorem FamilyPolyOutput.comp {outer : ∀ π, MeasuredProgram (Mid π) (Result π) ω}
    {inner : ∀ π, MeasuredProgram (Input π) (Mid π) ω} {size : ∀ π, Input π → ℕ}
    {midSize : ∀ π, Mid π → ℕ} {resultSize : ∀ π, Result π → ℕ}
    (ho : FamilyPolyOutput outer midSize resultSize) (hi : FamilyPolyOutput inner size midSize) :
    FamilyPolyOutput (fun π => (outer π).comp (inner π)) size resultSize := by
  obtain ⟨p, hp⟩ := ho
  obtain ⟨q, hq⟩ := hi
  exact ⟨p.comp q, fun π => ((hp π).comp (Polynomial.monotone_eval _) (hq π)).mono
    fun n => by simp [Polynomial.eval_comp]⟩

/-- One natural-number polynomial `q` bounds the charges of the declared operations of every member
`M π` of a parameter-indexed family, restricted to the answers `allows π` admits. On each input `i`
of each member, every completed path of the restricted member has a total price at most
`q.eval (size π i)`. The view, the answering function and the code between calls are not
charged. -/
def FamilyPolyCostUnder (M : ∀ π, MeasuredProgram (Input π) (Result π) ℕ)
    (allows : ∀ π, (v : (M π).View) → (o : (M π).Op) → (M π).spec v o → Prop)
    (size : ∀ π, Input π → ℕ) : Prop :=
  ∃ q : Polynomial ℕ, ∀ π, (M π).CostWithinUnder (allows π) (size π) q.eval

/-- Restricted to the answers `allows π` admits, one polynomial bounds the result sizes of every
member of a parameter-indexed family. -/
def FamilyPolyOutputUnder (M : ∀ π, MeasuredProgram (Input π) (Result π) ω)
    (allows : ∀ π, (v : (M π).View) → (o : (M π).Op) → (M π).spec v o → Prop)
    (size : ∀ π, Input π → ℕ) (resultSize : ∀ π, Result π → ℕ) : Prop :=
  ∃ q : Polynomial ℕ, ∀ π, (M π).OutputWithinUnder (allows π) (size π) (resultSize π) q.eval

/-- Over every answer, the restricted family contract is the family contract. -/
theorem familyPolyCostUnder_true_iff {M : ∀ π, MeasuredProgram (Input π) (Result π) ℕ}
    {size : ∀ π, Input π → ℕ} :
    FamilyPolyCostUnder M (fun _ _ _ _ => True) size ↔ FamilyPolyCost M size :=
  exists_congr fun _ => forall_congr' fun _ => costWithinUnder_true_iff

/-- Families with polynomial cost over allowed answers compose memberwise along `CompAllows` when
the inner output sizes over allowed answers grow polynomially. -/
theorem FamilyPolyCostUnder.comp {outer : ∀ π, MeasuredProgram (Mid π) (Result π) ℕ}
    {inner : ∀ π, MeasuredProgram (Input π) (Mid π) ℕ}
    {innerAllows : ∀ π, (v : (inner π).View) → (o : (inner π).Op) → (inner π).spec v o → Prop}
    {outerAllows : ∀ π, (v : (outer π).View) → (o : (outer π).Op) → (outer π).spec v o → Prop}
    {size : ∀ π, Input π → ℕ} {midSize : ∀ π, Mid π → ℕ}
    (ho : FamilyPolyCostUnder outer outerAllows midSize)
    (hi : FamilyPolyCostUnder inner innerAllows size)
    (hg : FamilyPolyOutputUnder inner innerAllows size midSize) :
    FamilyPolyCostUnder (fun π => (outer π).comp (inner π))
      (fun π => CompAllows (outer π) (inner π) (innerAllows π) (outerAllows π)) size := by
  obtain ⟨p, hp⟩ := ho
  obtain ⟨q, hq⟩ := hi
  obtain ⟨r, hr⟩ := hg
  exact ⟨q + p.comp r, fun π => ((hp π).comp (Polynomial.monotone_eval _) (hq π)
    (hr π)).mono fun n => by simp [Polynomial.eval_comp]⟩

/-- Families with polynomial output sizes over allowed answers compose memberwise along
`CompAllows`. -/
theorem FamilyPolyOutputUnder.comp {outer : ∀ π, MeasuredProgram (Mid π) (Result π) ω}
    {inner : ∀ π, MeasuredProgram (Input π) (Mid π) ω}
    {innerAllows : ∀ π, (v : (inner π).View) → (o : (inner π).Op) → (inner π).spec v o → Prop}
    {outerAllows : ∀ π, (v : (outer π).View) → (o : (outer π).Op) → (outer π).spec v o → Prop}
    {size : ∀ π, Input π → ℕ} {midSize : ∀ π, Mid π → ℕ} {resultSize : ∀ π, Result π → ℕ}
    (ho : FamilyPolyOutputUnder outer outerAllows midSize resultSize)
    (hi : FamilyPolyOutputUnder inner innerAllows size midSize) :
    FamilyPolyOutputUnder (fun π => (outer π).comp (inner π))
      (fun π => CompAllows (outer π) (inner π) (innerAllows π) (outerAllows π)) size
      resultSize := by
  obtain ⟨p, hp⟩ := ho
  obtain ⟨q, hq⟩ := hi
  exact ⟨p.comp q, fun π => ((hp π).comp (Polynomial.monotone_eval _) (hq π)).mono
    fun n => by simp [Polynomial.eval_comp]⟩

end Family

end PFunctor.FreeM.MeasuredProgram
