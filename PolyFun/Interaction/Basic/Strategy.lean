/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Interaction

/-!
# One-player strategies

`Strategy.Plain m spec Output` is the one-participant strategy induced by
`Strategy.syntax`. At every node it chooses the next move and stores the
continuation in the ambient monad `m`; at a leaf it produces the
path-dependent output.

This is the singleton-agent specialization of `StrategyOver` over the empty
node context. `Strategy.run` is the corresponding specialization of the
generic `InteractionOver.runTypeTree` runner.

Dependent sequential composition `Strategy.comp` requires `PFunctor.FreeM.append` from
`PolyFun.Interaction.Basic.Append`.
-/

universe u

namespace Interaction
open PFunctor.FreeM.Displayed (Decoration)
namespace TypeTree

variable {m : Type u → Type u}

/-- One-participant syntax for ordinary monadic strategies.

At each node the strategy chooses a move `x` and provides the continuation in
the ambient monad `m`. -/
def Strategy.syntax (m : Type u → Type u) :
    SyntaxOver
      (PFunctor.Lens.id TypeTree.basePFunctor) PUnit.{u+1} Node.Context.empty.{u, u} where
  Node _ X _ Cont := (x : X) × m (Cont x)

/-- One-player strategy with monadic effects. -/
abbrev Strategy.Plain (m : Type u → Type u)
    (spec : TypeTree.{u}) (Output : Path spec → Type u) :=
  StrategyOver (Strategy.syntax m) (PUnit.unit : PUnit.{u+1}) spec
    (Decoration.empty.{u, u} spec) Output

/-- Transport a plain strategy across equality of its type tree and a
pointwise identification of the correspondingly transported output family.

The explicit family equality keeps dependent path transport localized here;
callers do not need to unfold the `StrategyOver` representation. -/
def Strategy.castSpec {m : Type u → Type u} {source target : TypeTree}
    {Source : Path source → Type u} {Target : Path target → Type u}
    (hSpec : source = target)
    (hOutput : (path : Path target) →
      Source (Equiv.cast (congrArg Path hSpec).symm path) = Target path)
    (strategy : Strategy.Plain m source Source) :
    Strategy.Plain m target Target := by
  subst target
  have hFamily : Source = Target := by
    funext path
    simpa using hOutput path
  subst Target
  exact strategy

@[simp]
theorem Strategy.castSpec_rfl {m : Type u → Type u} {spec : TypeTree}
    {Output : Path spec → Type u} (strategy : Strategy.Plain m spec Output) :
    Strategy.castSpec rfl (fun _ => rfl) strategy = strategy :=
  rfl

/-- One-step execution law for ordinary one-player strategies. -/
def Strategy.interaction (m : Type u → Type u) [Monad m] :
    InteractionOver
      (PFunctor.Lens.id TypeTree.basePFunctor) PUnit Node.Context.empty (Strategy.syntax m) m where
  interact := fun {_X} {_γ} {_Cont} {_Result} profile k => do
    let node := profile PUnit.unit
    let next ← node.2
    k node.1 (fun _ => next)

/-- Run the strategy, returning the full path and the dependent output. -/
def Strategy.run {m : Type u → Type u} [Monad m] :
    (spec : TypeTree) → {Output : Path spec → Type u} →
    Strategy.Plain m spec Output → m ((tr : Path spec) × Output tr)
  | spec, Output, strat =>
      InteractionOver.runTypeTree
        (Agent := PUnit.{u+1})
        (Γ := Node.Context.empty)
        (syn := Strategy.syntax m)
        (m := m)
        (spec := spec)
        (Out := fun _ => Output)
        (Result := Output)
        (Decoration.empty spec)
        (fun agent => by
          cases agent
          exact strat)
        (fun _ out => out PUnit.unit)
        (Strategy.interaction m)

/-- Map the dependent output family along a natural transformation over paths. -/
def Strategy.mapOutput {m : Type u → Type u} [Functor m] :
    {spec : TypeTree} → {A B : Path spec → Type u} →
    (∀ tr, A tr → B tr) → Strategy.Plain m spec A → Strategy.Plain m spec B
  | .done, _, _, f, a => f ⟨⟩ a
  | .node _ _, _, _, f, ⟨x, cont⟩ =>
      ⟨x, (mapOutput (fun p => f ⟨x, p⟩) ·) <$> cont⟩

/-- Pointwise identity on outputs is the identity on strategies (needs a lawful functor). -/
@[simp, grind =]
theorem Strategy.mapOutput_id {m : Type u → Type u} [Functor m] [LawfulFunctor m] {spec : TypeTree}
    {A : Path spec → Type u} (σ : Strategy.Plain m spec A) :
    Strategy.mapOutput (fun _ x => x) σ = σ := by
  induction spec with
  | done => rfl
  | node X rest ih =>
    rcases σ with ⟨x, cont⟩
    simp only [Strategy.mapOutput]
    congr 1
    have hid : ∀ s : Strategy.Plain m (rest x) (fun p => A ⟨x, p⟩),
        mapOutput (fun (p : Path (rest x)) (y : A ⟨x, p⟩) => y) s = s :=
      fun s => ih x s
    calc (mapOutput (fun (p : Path (rest x)) (y : A ⟨x, p⟩) => y) ·) <$> cont
        = id <$> cont := by congr 1; funext s; exact hid s
      _ = cont := LawfulFunctor.id_map cont

/-- `mapOutput` respects composition of output maps (needs a lawful functor). -/
theorem Strategy.mapOutput_comp
    {m : Type u → Type u} [Functor m] [LawfulFunctor m] {spec : TypeTree}
    {A B C : Path spec → Type u} (g : ∀ tr, B tr → C tr) (f : ∀ tr, A tr → B tr)
    (σ : Strategy.Plain m spec A) :
    Strategy.mapOutput (fun tr x => g tr (f tr x)) σ =
      Strategy.mapOutput g (Strategy.mapOutput f σ) := by
  induction spec with
  | done => rfl
  | node X rest ih =>
    rcases σ with ⟨x, cont⟩
    simp only [Strategy.mapOutput]
    congr 1
    have hcomp : ∀ s : Strategy.Plain m (rest x) (fun p => A ⟨x, p⟩),
        @mapOutput m _ (rest x) (fun p => A ⟨x, p⟩) (fun p => C ⟨x, p⟩)
            (fun p y => g ⟨x, p⟩ (f ⟨x, p⟩ y)) s =
          (@mapOutput m _ (rest x) (fun p => B ⟨x, p⟩) (fun p => C ⟨x, p⟩)
              (fun p y => g ⟨x, p⟩ y) ∘
            @mapOutput m _ (rest x) (fun p => A ⟨x, p⟩) (fun p => B ⟨x, p⟩)
              (fun p y => f ⟨x, p⟩ y)) s :=
      fun s => ih x (fun p y => g ⟨x, p⟩ y) (fun p y => f ⟨x, p⟩ y) s
    calc (mapOutput (fun (p : Path (rest x)) (y : A ⟨x, p⟩) => g ⟨x, p⟩ (f ⟨x, p⟩ y)) ·)
              <$> cont
        = ((mapOutput (fun p y => g ⟨x, p⟩ y) ·) ∘ (mapOutput (fun p y => f ⟨x, p⟩ y) ·))
              <$> cont := by congr 1; funext s; exact hcomp s
      _ = (mapOutput (fun p y => g ⟨x, p⟩ y) ·) <$>
            ((mapOutput (fun p y => f ⟨x, p⟩ y) ·) <$> cont) := by
            rw [LawfulFunctor.comp_map]

end TypeTree
end Interaction
