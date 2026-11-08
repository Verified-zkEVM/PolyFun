/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Path.Charge
public import PolyFun.Control.Monad.Graded

/-!
# Measured programs and budgeted carriers

**Measured programs.** A `MeasuredProgram Input Result ω` computes a function by a free program
whose interface depends on a view of the input:
- the view is computed outside the program, and is not charged;
- calls are answered by a deterministic answering function (`answer`);
- each operation has a price (`cost`).

`run` interprets the program through the deterministic answers, and is the output of the one path
they pick (`run_eq_output`). `Realizes f` says the run computes `f`, and `CostAtMost B` bounds the
charge of every completed path of every view's program, so signed prices are allowed. `ofFun f`
computes `f` with no operations at cost `0`.

`comp outer inner` runs `inner`, computes `outer`'s view from the actual intermediate result, and
runs `outer`. It does this on the sum of the two interfaces, each operation tagged with the view it
belongs to, keeping both price lists. It computes the composite
(`run_comp`, `Realizes.comp`), and its budgets add (`CostAtMost.comp`). `contramap` precomposes an
uncharged map on inputs. A `BudgetedProgram f ω` bundles a measured program realizing `f` with a
budget, and composes the same way.

**Budgeted carriers.** `Budgeted c B α` is the subtype of free programs within budget `B`. With
budgets graded by `Multiplicative ω`, it is a `GradedMonad`: `gbind` adds budgets.
-/

@[expose] public section

universe u v w uA uB uI uI'

namespace PFunctor.FreeM

/-! ## Measured programs -/

/-- A function computed by a free program over an interface that depends on an uncharged view of
the input, answered deterministically, with a price per operation.

Only the operations are charged. The view, the answering function and the code between calls are
free at this layer, so `ofFun f` realizes any `f` at cost `0`: a statement of the form
`∃ M, M.Realizes f ∧ M.CostAtMost B` is trivial. Cost statements name the measured program, and
the uncharged parts are bounded one layer down. -/
structure MeasuredProgram (Input : Type uI) (Result : Type u) (ω : Type w) where
  /-- What the program is allowed to depend on. -/
  View : Type u
  /-- The uncharged view of an input. -/
  view : Input → View
  /-- The operations the program may call. -/
  Op : Type u
  /-- The answers to an operation, which may depend on the view. -/
  spec : View → Op → Type u
  /-- The program of each view. -/
  program : (v : View) → FreeM ⟨Op, spec v⟩ Result
  /-- The deterministic answers of each view. -/
  answer : (v : View) → (o : Op) → spec v o
  /-- The price of each operation. -/
  cost : Op → ω

namespace MeasuredProgram

variable {Input : Type uI} {Mid Result : Type u} {ω : Type w}

/-- Run the program of the input's view, answering every call deterministically. -/
def run (M : MeasuredProgram Input Result ω) (i : Input) : Result :=
  ((M.program (M.view i)).liftM fun o => (pure (M.answer (M.view i) o) : Id _)).run

/-- The run is the output of the path the answers pick. -/
theorem run_eq_output (M : MeasuredProgram Input Result ω) (i : Input) :
    M.run i = output (M.program (M.view i)) (Path.ofHandler (M.answer (M.view i)) _) :=
  (output_ofHandler _ _).symm

/-- The program computes `f`. -/
def Realizes (M : MeasuredProgram Input Result ω) (f : Input → Result) : Prop :=
  ∀ i, f i = M.run i

/-- Every completed path of every view's program costs at most `B`. -/
def CostAtMost [Add ω] [Zero ω] [LE ω] (M : MeasuredProgram Input Result ω) (B : ω) : Prop :=
  ∀ v (p : Path (M.program v)), Path.charge M.cost (M.program v) p ≤ B

/-- A cost bound holds for every larger budget. -/
theorem CostAtMost.mono [Add ω] [Zero ω] [Preorder ω] {M : MeasuredProgram Input Result ω}
    {B B' : ω} (h : M.CostAtMost B) (hB : B ≤ B') : M.CostAtMost B' :=
  fun v p => (h v p).trans hB

/-- The program with no operations that computes `f` on its whole input. Its view is the input, so
the input shares the result's universe. -/
def ofFun {Input : Type u} (f : Input → Result) : MeasuredProgram Input Result ω where
  View := Input
  view := id
  Op := PEmpty
  spec _ _ := PEmpty
  program v := pure (f v)
  answer _ o := o.elim
  cost o := o.elim

theorem realizes_ofFun {Input : Type u} (f : Input → Result) : (ofFun f (ω := ω)).Realizes f :=
  fun _ => rfl

/-- A program with no operations costs nothing. -/
theorem costAtMost_ofFun [Add ω] [Zero ω] [Preorder ω] {Input : Type u} (f : Input → Result) :
    (ofFun f (ω := ω)).CostAtMost 0 :=
  fun _ _ => le_rfl

/-- The answers of the composite interface, which does not depend on the view: each operation is
tagged with the view it belongs to, `inner`'s or `outer`'s. -/
def CompSpec (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (_ : inner.View) : (Σ _ : inner.View, inner.Op) ⊕ (Σ _ : outer.View, outer.Op) → Type u
  | .inl ⟨v, o⟩ => inner.spec v o
  | .inr ⟨v', o⟩ => outer.spec v' o

/-- The inclusion of `inner`'s interface at view `v` into the composite interface. -/
def innerLens (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (v : inner.View) : Lens ⟨inner.Op, inner.spec v⟩ ⟨_, CompSpec outer inner v⟩ :=
  ⟨fun o => Sum.inl ⟨v, o⟩, fun _ b => b⟩

/-- The inclusion of `outer`'s interface at view `v'` into the composite interface. -/
def outerLens (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (v : inner.View) (v' : outer.View) :
    Lens ⟨outer.Op, outer.spec v'⟩ ⟨_, CompSpec outer inner v⟩ :=
  ⟨fun o => Sum.inr ⟨v', o⟩, fun _ b => b⟩

/-- Run `inner`, compute `outer`'s view from the actual intermediate result without charging it,
and run `outer`, on the sum of the two interfaces, each operation tagged with its view, with both
price lists. -/
def comp (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω) :
    MeasuredProgram Input Result ω where
  View := inner.View
  view := inner.view
  Op := (Σ _ : inner.View, inner.Op) ⊕ (Σ _ : outer.View, outer.Op)
  spec := CompSpec outer inner
  program v := (inner.program v).mapLens (innerLens outer inner v) >>= fun m =>
    (outer.program (outer.view m)).mapLens (outerLens outer inner v (outer.view m))
  answer _
    | .inl ⟨v, o⟩ => inner.answer v o
    | .inr ⟨v', o⟩ => outer.answer v' o
  cost
    | .inl ⟨_, o⟩ => inner.cost o
    | .inr ⟨_, o⟩ => outer.cost o

/-- The composite computes the composite function. -/
theorem run_comp (outer : MeasuredProgram Mid Result ω) (inner : MeasuredProgram Input Mid ω)
    (i : Input) : (outer.comp inner).run i = outer.run (inner.run i) := by
  simp only [run, comp, FreeM.liftM_bind, FreeM.liftM_mapLens]
  rfl

/-- The composite realizes the composite function. -/
theorem Realizes.comp {outer : MeasuredProgram Mid Result ω} {inner : MeasuredProgram Input Mid ω}
    {f : Input → Mid} {g : Mid → Result} (hg : outer.Realizes g) (hf : inner.Realizes f) :
    (outer.comp inner).Realizes (g ∘ f) := fun i => by
  rw [run_comp, Function.comp_apply, hf i, hg]

/-- Composite budgets add: the inner budget, then the outer one. Arguments come in the order of
`comp`, outer first. -/
theorem CostAtMost.comp [AddMonoid ω] [Preorder ω] [AddLeftMono ω] [AddRightMono ω]
    {outer : MeasuredProgram Mid Result ω} {inner : MeasuredProgram Input Mid ω}
    {outerBudget innerBudget : ω} (ho : outer.CostAtMost outerBudget)
    (hi : inner.CostAtMost innerBudget) :
    (outer.comp inner).CostAtMost (innerBudget + outerBudget) := by
  intro v
  exact Path.charge_bind_mapLens_le _ _ _ _ (fun _ => rfl) (fun _ _ => rfl) (hi v)
    fun m => ho (outer.view m)

/-- Precompose with an uncharged map on inputs. -/
def contramap {Input' : Type uI'} (M : MeasuredProgram Input Result ω) (g : Input' → Input) :
    MeasuredProgram Input' Result ω :=
  { M with view := M.view ∘ g }

theorem run_contramap {Input' : Type uI'} (M : MeasuredProgram Input Result ω) (g : Input' → Input)
    (i : Input') : (M.contramap g).run i = M.run (g i) :=
  rfl

theorem Realizes.contramap {Input' : Type uI'} {M : MeasuredProgram Input Result ω}
    {f : Input → Result} (h : M.Realizes f) (g : Input' → Input) :
    (M.contramap g).Realizes (f ∘ g) :=
  fun i => h (g i)

theorem CostAtMost.contramap [Add ω] [Zero ω] [LE ω] {Input' : Type uI'}
    {M : MeasuredProgram Input Result ω} {B : ω} (h : M.CostAtMost B) (g : Input' → Input) :
    (M.contramap g).CostAtMost B :=
  h

end MeasuredProgram

/-- A measured program realizing `f`, with a budget on every completed path. -/
structure BudgetedProgram {Input : Type uI} {Result : Type u} (f : Input → Result) (ω : Type w)
    [Add ω] [Zero ω] [LE ω] where
  /-- The measured program. -/
  program : MeasuredProgram Input Result ω
  /-- The bound on the charge of every completed path. -/
  budget : ω
  /-- The program computes `f`. -/
  realizes : program.Realizes f
  /-- Every completed path costs at most the budget. -/
  costAtMost : program.CostAtMost budget

namespace BudgetedProgram

variable {Input : Type uI} {Mid Result : Type u} {ω : Type w}

/-- Every function has a budgeted program with budget `0` and no operations. -/
def ofFun [Add ω] [Zero ω] [Preorder ω] {Input : Type u} (f : Input → Result) :
    BudgetedProgram f ω :=
  ⟨MeasuredProgram.ofFun f, 0, MeasuredProgram.realizes_ofFun f,
    MeasuredProgram.costAtMost_ofFun f⟩

/-- Precompose with an uncharged map on inputs. -/
def contramap [Add ω] [Zero ω] [LE ω] {Input' : Type uI'} {f : Input → Result}
    (M : BudgetedProgram f ω) (g : Input' → Input) : BudgetedProgram (f ∘ g) ω :=
  ⟨M.program.contramap g, M.budget, M.realizes.contramap g, M.costAtMost.contramap g⟩

/-- Compose budgeted programs; budgets add. -/
def comp [AddMonoid ω] [Preorder ω] [AddLeftMono ω] [AddRightMono ω] {f : Input → Mid}
    {g : Mid → Result} (outer : BudgetedProgram g ω) (inner : BudgetedProgram f ω) :
    BudgetedProgram (g ∘ f) ω :=
  ⟨outer.program.comp inner.program, inner.budget + outer.budget,
    outer.realizes.comp inner.realizes, outer.costAtMost.comp inner.costAtMost⟩

end BudgetedProgram

/-! ## Budgeted carriers -/

section Graded

variable {P : PFunctor.{uA, uB}} {ω : Type w}

/-- Free programs within budget `B`. -/
def Budgeted [Add ω] [LE ω] [Zero ω] (c : P.A → ω) (B : Multiplicative ω) (α : Type v) :
    Type (max uA uB v) :=
  {x : FreeM P α // x.IsChargeBound c (Multiplicative.toAdd B)}

variable [AddMonoid ω] [Preorder ω] [AddLeftMono ω] [AddRightMono ω] [CanonicallyOrderedAdd ω]

/-- Budgeted programs form a graded monad: sequencing adds budgets. -/
instance Budgeted.instGradedMonad (c : P.A → ω) :
    GradedMonad (Multiplicative ω) (Budgeted c) where
  gpure a := ⟨pure a, isChargeBound_pure a⟩
  gbind x f := ⟨FreeM.bind x.1 fun a => (f a).1, IsChargeBound.bind x.2 fun a => (f a).2⟩

end Graded

end PFunctor.FreeM
