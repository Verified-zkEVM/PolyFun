/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Append
import PolyFun.Interaction.Basic.Replicate
import PolyFun.Interaction.TwoParty.Decoration
import PolyFun.Interaction.TwoParty.Strategy
import Mathlib.Control.Monad.Basic
import PolyFun.Control.Lawful.Basic
import Mathlib.Data.Sigma.Basic
import PolyFun.Interaction.Basic.StateChain

/-!
# Composing two-party protocols

Role-aware composition of strategies and counterparts along `PFunctor.FreeM.append`,
`Spec.replicate`, and `Spec.stateChain`. Each combinator dispatches on the role at
each node (sending or receiving) to compose the two-party strategies correctly.

For binary composition, `StrategyOver.TwoParty.Focal.comp` and
`StrategyOver.TwoParty.Counterpart.append` use `PFunctor.FreeM.Path.liftAppend`
for the output type (factored form). The flat variants (`compFlat`,
`StrategyOver.TwoParty.Counterpart.appendFlat`) take a single output
family on the combined transcript.
-/

open LawfulMonad

universe u v

namespace Interaction
namespace TwoParty

variable {m : Type u → Type u}
open TwoParty

/-- A lawful monad whose independent effects may be swapped.

This is the exact extra structure needed for the sequential-composition
execution theorems once both sides may perform effects after a sender move is
observed: the composed prover may prepare suffix state before the counterpart
finishes its sender-side observation, so proving the usual factorization law
requires commuting those independent effects. -/
class LawfulCommMonad (m : Type u → Type u) [Monad m] extends LawfulMonad m where
  bind_comm :
    {α β γ : Type u} →
    (ma : m α) →
    (mb : m β) →
    (k : α → β → m γ) →
    (do
      let a ← ma
      let b ← mb
      k a b) =
    (do
      let b ← mb
      let a ← ma
      k a b)

/-- Compose role-aware strategies along `PFunctor.FreeM.append` with a two-argument output family
lifted through `PFunctor.FreeM.Path.liftAppend`. The continuation receives the first phase's
output and produces a second-phase strategy. -/
def _root_.Interaction.StrategyOver.TwoParty.Focal.comp {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : PFunctor.FreeM.Path s₁ → Type u}
    {F : (tr₁ : PFunctor.FreeM.Path s₁) → PFunctor.FreeM.Path (s₂ tr₁) → Type u}
    (strat₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ Mid)
    (f : (tr₁ : PFunctor.FreeM.Path s₁) → Mid tr₁ →
      m (StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁) (F tr₁))) :
    m (StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₁.append s₂) (r₁.append r₂)
        (PFunctor.FreeM.Path.liftAppend s₁ s₂ F)) :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ =>
      pure <| do
        let ⟨x, next⟩ ← strat₁
        let rest ← comp next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
        pure ⟨x, rest⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      pure fun x => do
        let next ← strat₁ x
        comp next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)

/-- Compose role-aware strategies along `PFunctor.FreeM.append` with a single output family
on the combined transcript. The continuation indexes via `PFunctor.FreeM.Path.append`. -/
def _root_.Interaction.StrategyOver.TwoParty.Focal.compFlat {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : PFunctor.FreeM.Path s₁ → Type u}
    {Output : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ Mid)
    (f : (tr₁ : PFunctor.FreeM.Path s₁) → Mid tr₁ →
      m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂)))) :
    m (StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₁.append s₂) (r₁.append r₂) Output) :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ =>
      pure <| do
        let ⟨x, next⟩ ← strat₁
        let rest ← compFlat next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
        pure ⟨x, rest⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      pure fun x => do
        let next ← strat₁ x
        compFlat next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)

/-- Pure continuation specialization of `compFlat`. This stays private:
it only serves the weaker `[LawfulMonad]` execution theorem below. -/
private def _root_.Interaction.StrategyOver.TwoParty.Focal.compFlatPure
    {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : PFunctor.FreeM.Path s₁ → Type u}
    {Output : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ Mid)
    (f : (tr₁ : PFunctor.FreeM.Path s₁) → Mid tr₁ →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂))) :
    StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₁.append s₂) (r₁.append r₂) Output :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ => do
      let ⟨x, next⟩ ← strat₁
      pure ⟨x, compFlatPure next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      fun x => do
        let next ← strat₁ x
        pure (compFlatPure next (fun tr₁ mid => f ⟨x, tr₁⟩ mid))

private theorem _root_.Interaction.StrategyOver.TwoParty.Focal.compFlat_eq_pure_compFlatPure
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : PFunctor.FreeM.Path s₁ → Type u}
    {Output : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ Mid)
    (f : (tr₁ : PFunctor.FreeM.Path s₁) → Mid tr₁ →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂))) :
    StrategyOver.TwoParty.Focal.compFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid)) =
      pure (StrategyOver.TwoParty.Focal.compFlatPure strat₁ f) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {s₂ : PFunctor.FreeM.Path s₁ → Spec}
      {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
      {Mid : PFunctor.FreeM.Path s₁ → Type u}
      {Output : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
      (strat₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ Mid)
      (f : (tr₁ : PFunctor.FreeM.Path s₁) → Mid tr₁ →
        StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => Output (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂))) :
      StrategyOver.TwoParty.Focal.compFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid)) =
        pure (StrategyOver.TwoParty.Focal.compFlatPure strat₁ f) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        rfl
    | .node X rest, ⟨.sender, rRest⟩ =>
        rw [StrategyOver.TwoParty.Focal.compFlat.eq_2]
        refine congrArg pure ?_
        apply bind_congr
        intro xc
        cases xc with
        | mk x next =>
            simp only [bind_pure_comp]
            have hgo := go (rest x) (rRest x)
              (s₂ := fun tr₁ => s₂ ⟨x, tr₁⟩)
              (r₂ := fun tr₁ => r₂ ⟨x, tr₁⟩)
              (Output := fun tr => Output ⟨x, tr⟩)
              next
              (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
            exact (congrArg (fun z => Sigma.mk x <$> z) hgo).trans (map_pure _ _)
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        rw [StrategyOver.TwoParty.Focal.compFlat.eq_3]
        refine congrArg pure ?_
        funext x
        refine congrArg (fun k => strat₁ x >>= k) ?_
        funext next
        exact go (rest x) (rRest x)
          (s₂ := fun tr₁ => s₂ ⟨x, tr₁⟩)
          (r₂ := fun tr₁ => r₂ ⟨x, tr₁⟩)
          (Output := fun tr => Output ⟨x, tr⟩)
          next
          (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
  exact go s₁ r₁ strat₁ f

/-- Extract the first-phase role-aware strategy from a strategy on a composed
interaction. At each first-phase transcript `tr₁`, the remainder is the
second-phase strategy with output indexed by `PFunctor.FreeM.Path.append`. -/
def _root_.Interaction.StrategyOver.TwoParty.Focal.splitPrefix {m : Type u → Type u} [Functor m] :
    {s₁ : Spec} → {s₂ : PFunctor.FreeM.Path s₁ → Spec} →
    {r₁ : RoleDecoration s₁} →
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)} →
    {Output : PFunctor.FreeM.Path (s₁.append s₂) → Type u} →
    StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₁.append s₂) (r₁.append r₂) Output →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ (fun tr₁ =>
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂)))
  | .done, _, _, _, _, strat => strat
  | .node _ _, s₂, ⟨.sender, rRest⟩, r₂, _, strat =>
      (fun ⟨x, cont⟩ =>
        ⟨x, splitPrefix
          (s₂ := fun p => s₂ ⟨x, p⟩)
          (r₁ := rRest x)
          (r₂ := fun p => r₂ ⟨x, p⟩) cont⟩) <$> strat
  | .node _ _, s₂, ⟨.receiver, rRest⟩, r₂, _, respond =>
      fun x => (splitPrefix
        (s₂ := fun p => s₂ ⟨x, p⟩)
        (r₁ := rRest x)
        (r₂ := fun p => r₂ ⟨x, p⟩) ·) <$> respond x

/-- Recompose a role-aware strategy from its prefix decomposition. -/
theorem _root_.Interaction.StrategyOver.TwoParty.Focal.compFlat_splitPrefix
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {Output : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
    (strat :
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
        (s₁.append s₂) (r₁.append r₂) Output) :
    StrategyOver.TwoParty.Focal.compFlat
      (StrategyOver.TwoParty.Focal.splitPrefix (s₂ := s₂) (r₁ := r₁) (r₂ := r₂) strat)
      (fun _ strat₂ => pure strat₂) = pure strat := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {s₂ : PFunctor.FreeM.Path s₁ → Spec}
      {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
      {Output : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
      (strat : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
        (s₁.append s₂) (r₁.append r₂) Output) :
      StrategyOver.TwoParty.Focal.compFlat
        (StrategyOver.TwoParty.Focal.splitPrefix (s₂ := s₂) (r₁ := r₁) (r₂ := r₂) strat)
        (fun _ strat₂ => pure strat₂) = pure strat := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        rfl
    | .node X rest, ⟨.sender, rRest⟩ =>
        rw [StrategyOver.TwoParty.Focal.compFlat.eq_2,
          StrategyOver.TwoParty.Focal.splitPrefix.eq_2]
        refine congrArg pure ?_
        simp only [bind_map_left]
        calc
          (do
            let a ← strat
            let rest_1 ←
              StrategyOver.TwoParty.Focal.compFlat
                (StrategyOver.TwoParty.Focal.splitPrefix
                  (s₂ := fun p => s₂ ⟨a.1, p⟩)
                  (r₁ := rRest a.1)
                  (r₂ := fun p => r₂ ⟨a.1, p⟩) a.2)
                (fun _ strat₂ => pure strat₂)
            pure ⟨a.1, rest_1⟩) =
              strat >>= fun a => pure ⟨a.1, a.2⟩ := by
                refine congrArg (fun k => strat >>= k) ?_
                funext xc
                rcases xc with ⟨x, tail⟩
                let Suffix : X → Type u := fun y =>
                  StrategyOver (SyntaxOver.TwoParty.pairedSpec m) TwoParty.Participant.focal
                    ((fun b => PFunctor.FreeM.append (rest b) (fun path => s₂ ⟨b, path⟩)) y)
                    ((fun y =>
                      PFunctor.FreeM.Displayed.Decoration.append
                        (P := Spec.basePFunctor) (α := PUnit.{u+1}) (β := PUnit.{u+1})
                        (rRest y) (fun p => r₂ ⟨y, p⟩)) y)
                    (fun tr => Output ⟨y, tr⟩)
                have hgo :
                    (StrategyOver.TwoParty.Focal.compFlat
                      (StrategyOver.TwoParty.Focal.splitPrefix tail)
                      (fun _ strat₂ => pure strat₂)) = pure tail :=
                  go (rest x) (rRest x)
                    (s₂ := fun p => s₂ ⟨x, p⟩)
                    (r₂ := fun p => r₂ ⟨x, p⟩) tail
                exact LawfulMonad.bind_pure_sigma_mk (m := m) (α := X) (β := Suffix)
                  (x := x) (tail := tail)
                  (action := StrategyOver.TwoParty.Focal.compFlat
                    (StrategyOver.TwoParty.Focal.splitPrefix tail)
                    (fun _ strat₂ => pure strat₂)) hgo
          _ = strat := by
                simp
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        refine congrArg pure ?_
        funext x
        simp only [StrategyOver.TwoParty.Focal.splitPrefix.eq_3]
        have hcont :
            strat x >>= (fun next =>
              StrategyOver.TwoParty.Focal.compFlat
                (StrategyOver.TwoParty.Focal.splitPrefix
                  (s₂ := fun p => s₂ ⟨x, p⟩)
                  (r₁ := rRest x)
                  (r₂ := fun p => r₂ ⟨x, p⟩) next)
                (fun _ strat₂ => pure strat₂)) =
              strat x >>= fun next => pure next := by
          refine congrArg (fun k => strat x >>= k) ?_
          funext next
          simpa using
            go (rest x) (rRest x)
              (s₂ := fun p => s₂ ⟨x, p⟩)
              (r₂ := fun p => r₂ ⟨x, p⟩) next
        simpa [monad_norm] using hcont
  exact go s₁ r₁ strat

/-- Compose counterparts along `PFunctor.FreeM.append` with a two-argument output family
lifted through `PFunctor.FreeM.Path.liftAppend`. The continuation maps the first phase's
output to a second-phase counterpart. -/
def _root_.Interaction.StrategyOver.TwoParty.Counterpart.append {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {Output₁ : PFunctor.FreeM.Path s₁ → Type u}
    {F : (tr₁ : PFunctor.FreeM.Path s₁) → PFunctor.FreeM.Path (s₂ tr₁) → Type u} :
    StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart s₁ r₁ Output₁ →
    ((tr₁ : PFunctor.FreeM.Path s₁) → Output₁ tr₁ →
      StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart (s₂ tr₁) (r₂ tr₁) (F tr₁)) →
    StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart (s₁.append s₂) (r₁.append r₂)
        (PFunctor.FreeM.Path.liftAppend s₁ s₂ F) :=
  match s₁, r₁ with
  | .done, _ => fun out₁ c₂ => c₂ ⟨⟩ out₁
  | .node _ _, ⟨.sender, _⟩ => fun c₁ c₂ =>
      fun x => do
        let cRest ← c₁ x
        pure <| StrategyOver.TwoParty.Counterpart.append cRest (fun p o => c₂ ⟨x, p⟩ o)
  | .node _ _, ⟨.receiver, _⟩ => fun c₁ c₂ => do
      let ⟨x, cRest⟩ ← c₁
      return ⟨x, StrategyOver.TwoParty.Counterpart.append cRest (fun p o => c₂ ⟨x, p⟩ o)⟩

/-- Compose counterparts along `PFunctor.FreeM.append` with a single output family on the
combined transcript. The continuation indexes via `PFunctor.FreeM.Path.append`. -/
def _root_.Interaction.StrategyOver.TwoParty.Counterpart.appendFlat {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {Output₁ : PFunctor.FreeM.Path s₁ → Type u}
    {Output₂ : PFunctor.FreeM.Path (s₁.append s₂) → Type u} :
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart s₁ r₁ Output₁ →
    ((tr₁ : PFunctor.FreeM.Path s₁) → Output₁ tr₁ →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output₂ (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂))) →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
      (s₁.append s₂) (r₁.append r₂) Output₂ :=
  match s₁, r₁ with
  | .done, _ => fun out₁ c₂ => c₂ ⟨⟩ out₁
  | .node _ _, ⟨.sender, _⟩ => fun c₁ c₂ =>
      fun x => do
        let cRest ← c₁ x
        pure <| StrategyOver.TwoParty.Counterpart.appendFlat cRest (fun p o => c₂ ⟨x, p⟩ o)
  | .node _ _, ⟨.receiver, _⟩ => fun c₁ c₂ => do
      let ⟨x, cRest⟩ ← c₁
      return ⟨x, StrategyOver.TwoParty.Counterpart.appendFlat cRest (fun p o => c₂ ⟨x, p⟩ o)⟩

/-- `StrategyOver.TwoParty.Counterpart.append` equals `appendFlat` composed
with `mapOutput packAppend`.
This lets proofs that decompose an arbitrary strategy via `splitPrefix` +
`appendFlat` still work when `Reduction.comp` uses the non-flat `append`. -/
theorem _root_.Interaction.StrategyOver.TwoParty.Counterpart.append_eq_appendFlat_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m] :
    {s₁ : Spec} → {s₂ : PFunctor.FreeM.Path s₁ → Spec} →
    {r₁ : RoleDecoration s₁} →
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)} →
    {Output₁ : PFunctor.FreeM.Path s₁ → Type u} →
    {F : (tr₁ : PFunctor.FreeM.Path s₁) → PFunctor.FreeM.Path (s₂ tr₁) → Type u} →
    (c₁ : StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart s₁ r₁ Output₁) →
    (c₂ : (tr₁ : PFunctor.FreeM.Path s₁) → Output₁ tr₁ →
      StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart (s₂ tr₁) (r₂ tr₁) (F tr₁)) →
    StrategyOver.TwoParty.Counterpart.append c₁ c₂ =
      StrategyOver.TwoParty.Counterpart.appendFlat c₁ (fun tr₁ o =>
        StrategyOver.TwoParty.Counterpart.mapOutput
          (fun tr₂ x => PFunctor.FreeM.Path.packAppend s₁ s₂ F tr₁ tr₂ x) (c₂ tr₁ o))
  | .done, _, _, _, _, _, c₁, c₂ => by
      simp only [StrategyOver.TwoParty.Counterpart.append,
        StrategyOver.TwoParty.Counterpart.appendFlat, PFunctor.FreeM.Path.packAppend]
      exact (StrategyOver.TwoParty.Counterpart.mapOutput_id _).symm
  | .node _ rest, _, ⟨.sender, rRest⟩, _, _, _, c₁, c₂ => by
      funext x
      refine congrArg (fun k => c₁ x >>= k) ?_
      funext cRest
      simpa [monad_norm] using
        congrArg pure
          (append_eq_appendFlat_mapOutput cRest (fun p o => c₂ ⟨x, p⟩ o))
  | .node _ rest, _, ⟨.receiver, rRest⟩, _, _, _, c₁, c₂ => by
      simp only [StrategyOver.TwoParty.Counterpart.append,
        StrategyOver.TwoParty.Counterpart.appendFlat]
      congr 1; funext ⟨x, cRest⟩; congr 1
      simp only [PFunctor.FreeM.Path.packAppend]; congr 1
      exact append_eq_appendFlat_mapOutput cRest (fun p o => c₂ ⟨x, p⟩ o)

/-- `StrategyOver.TwoParty.Focal.comp` equals `compFlat` composed with
`mapOutput packAppend` on the suffix strategy produced by the continuation. -/
theorem _root_.Interaction.StrategyOver.TwoParty.Focal.comp_eq_compFlat_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m] :
    {s₁ : Spec} → {s₂ : PFunctor.FreeM.Path s₁ → Spec} →
    {r₁ : RoleDecoration s₁} →
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)} →
    {Mid : PFunctor.FreeM.Path s₁ → Type u} →
    {F : (tr₁ : PFunctor.FreeM.Path s₁) → PFunctor.FreeM.Path (s₂ tr₁) → Type u} →
    (strat₁ : StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ Mid) →
    (f : (tr₁ : PFunctor.FreeM.Path s₁) → Mid tr₁ →
      m (StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁) (F tr₁))) →
    StrategyOver.TwoParty.Focal.comp strat₁ f =
      StrategyOver.TwoParty.Focal.compFlat strat₁ (fun tr₁ mid => do
        let strat₂ ← f tr₁ mid
        pure (StrategyOver.TwoParty.Focal.mapOutput
          (fun tr₂ x => PFunctor.FreeM.Path.packAppend s₁ s₂ F tr₁ tr₂ x) strat₂))
  | .done, s₂, r₁, r₂, Mid, F, strat₁, f => by
      simp only [StrategyOver.TwoParty.Focal.comp, StrategyOver.TwoParty.Focal.compFlat,
        PFunctor.FreeM.Path.packAppend]
      symm
      calc
        (do
          let strat₂ ← f ⟨⟩ strat₁
          pure (StrategyOver.TwoParty.Focal.mapOutput (fun tr₂ x => x) strat₂)) =
            (fun strat₂ =>
              StrategyOver.TwoParty.Focal.mapOutput (fun tr₂ x => x) strat₂) <$>
              f ⟨⟩ strat₁ := bind_pure_comp _ _
        _ = (fun strat₂ => strat₂) <$> f ⟨⟩ strat₁ := by
          congr 1
          funext strat₂
          rw [StrategyOver.TwoParty.Focal.mapOutput_id]
        _ = f ⟨⟩ strat₁ := LawfulFunctor.id_map _
  | .node X rest, s₂, ⟨.sender, rRest⟩, r₂, Mid, F, strat₁, f => by
      simp only [StrategyOver.TwoParty.Focal.comp, StrategyOver.TwoParty.Focal.compFlat]
      refine congrArg pure ?_
      apply bind_congr
      intro xc
      cases xc with
      | mk x next =>
          let Tail : X → Type u := fun x =>
            StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
              (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
              (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                (fun path => r₂ ⟨x, path⟩))
              (fun tr => PFunctor.FreeM.Path.liftAppend (Spec.node X rest) s₂ F ⟨x, tr⟩)
          simpa [monad_norm, PFunctor.Lens.id, PFunctor.FreeM.Path.packAppend] using
            congrArg (fun z => z >>= fun tail => pure (⟨x, tail⟩ : (x : X) × Tail x))
              (comp_eq_compFlat_mapOutput next (fun p o => f ⟨x, p⟩ o))
  | .node X rest, s₂, ⟨.receiver, rRest⟩, r₂, Mid, F, strat₁, f => by
      simp only [StrategyOver.TwoParty.Focal.comp, StrategyOver.TwoParty.Focal.compFlat]
      refine congrArg pure ?_
      funext x
      apply bind_congr
      intro next
      simpa [monad_norm, PFunctor.FreeM.Path.packAppend] using
        comp_eq_compFlat_mapOutput next (fun p o => f ⟨x, p⟩ o)

/-- Executing a flat composed strategy/counterpart factors into first executing
the prefix interaction and then executing the suffix continuation. -/
theorem run_compFlat_appendFlat_pure
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {MidP MidC : PFunctor.FreeM.Path s₁ → Type u}
    {OutputP OutputC : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ MidP)
    (f : (tr₁ : PFunctor.FreeM.Path s₁) → MidP tr₁ →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputP (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂)))
    (cpt₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart s₁ r₁ MidC)
    (cpt₂ : (tr₁ : PFunctor.FreeM.Path s₁) → MidC tr₁ →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputC (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂))) :
    (do
      let strat ← StrategyOver.TwoParty.Focal.compFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid))
      run (s₁.append s₂) (r₁.append r₂) strat
        (StrategyOver.TwoParty.Counterpart.appendFlat cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, out₁⟩ ← run s₁ r₁ strat₁ cpt₁
        let ⟨tr₂, outP, outC⟩ ←
          run (s₂ tr₁) (r₂ tr₁) (f tr₁ mid) (cpt₂ tr₁ out₁)
        pure ⟨PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂, outP, outC⟩) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {MidP MidC : PFunctor.FreeM.Path s₁ → Type u}
      {s₂ : PFunctor.FreeM.Path s₁ → Spec}
      {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
      {OutputP OutputC : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
      {β : Type u}
      (strat₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ MidP)
      (f : (tr₁ : PFunctor.FreeM.Path s₁) → MidP tr₁ →
        StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputP (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂)))
      (cpt₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart s₁ r₁ MidC)
      (cpt₂ : (tr₁ : PFunctor.FreeM.Path s₁) → MidC tr₁ →
        StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputC (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂)))
      (g : ((tr : PFunctor.FreeM.Path (s₁.append s₂)) × OutputP tr × OutputC tr) → m β) :
      (do
        let r ←
          run (s₁.append s₂) (r₁.append r₂)
            (StrategyOver.TwoParty.Focal.compFlatPure strat₁ f)
            (StrategyOver.TwoParty.Counterpart.appendFlat cpt₁ cpt₂)
        g r) =
        (do
          let r₁ ← run s₁ r₁ strat₁ cpt₁
          let r₂ ←
            run (s₂ r₁.1) (r₂ r₁.1) (f r₁.1 r₁.2.1) (cpt₂ r₁.1 r₁.2.2)
          g ⟨PFunctor.FreeM.Path.append s₁ s₂ r₁.1 r₂.1, r₂.2.1, r₂.2.2⟩) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        simp [StrategyOver.TwoParty.Focal.compFlatPure,
          StrategyOver.TwoParty.Counterpart.appendFlat.eq_1, run_done,
          PFunctor.FreeM.Path.append_done]
    | .node X rest, ⟨.sender, rRest⟩ =>
        simp only [StrategyOver.TwoParty.Focal.compFlatPure,
          StrategyOver.TwoParty.Counterpart.appendFlat,
          PFunctor.FreeM.append_roll, PFunctor.FreeM.Displayed.Decoration.append_roll,
          run, InteractionOver.runSpec, InteractionOver.TwoParty.pairedSpec,
          InteractionOver.TwoParty.paired, participantProfile, collectParticipantOutputs,
          participantOutputFamily, bind_assoc, pure_bind]
        let mapStrat :
            ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
              (rest x) (rRest x) (fun tr => MidP ⟨x, tr⟩)) →
            ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
              (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
              (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                (fun path => r₂ ⟨x, path⟩))
              (fun tr => OutputP ⟨x, tr⟩)) :=
          fun a => ⟨a.1, StrategyOver.TwoParty.Focal.compFlatPure a.2
            (fun tr₁ mid => f ⟨a.1, tr₁⟩ mid)⟩
        simp only [LawfulMonad.do_bind_pure_comp]
        refine (bind_map_left mapStrat strat₁ _).trans ?_
        apply bind_congr
        intro xc
        cases xc with
        | mk x next =>
            let mapCpt :
                StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
                  (rest x) (rRest x) (fun tr => MidC ⟨x, tr⟩) →
                StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
                  (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                  (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                    (fun path => r₂ ⟨x, path⟩))
                  (fun tr => OutputC ⟨x, tr⟩) :=
              fun a => StrategyOver.TwoParty.Counterpart.appendFlat a
                (fun p o => cpt₂ ⟨x, p⟩ o)
            refine (bind_map_left mapCpt (cpt₁ x) _).trans ?_
            apply bind_congr
            intro cNext
            let addPrefix :
                ((tr : PFunctor.FreeM.Path (PFunctor.FreeM.append (rest x)
                  (fun path => s₂ ⟨x, path⟩))) ×
                  (fun tr => OutputP ⟨x, tr⟩) tr ×
                  (fun tr => OutputC ⟨x, tr⟩) tr) →
                ((tr : PFunctor.FreeM.Path
                  (PFunctor.FreeM.append (Spec.node X rest) s₂)) ×
                  OutputP tr × OutputC tr) :=
              fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
            simpa [monad_norm, addPrefix, PFunctor.FreeM.Path.append] using
              go (rest x) (rRest x)
                (s₂ := fun path => s₂ ⟨x, path⟩)
                (r₂ := fun path => r₂ ⟨x, path⟩)
                (OutputP := fun tr => OutputP ⟨x, tr⟩)
                (OutputC := fun tr => OutputC ⟨x, tr⟩)
                next
                (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
                cNext
                (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out)
                (fun a => g (addPrefix a))
    | .node X rest, ⟨.receiver, rRest⟩ =>
        simp only [StrategyOver.TwoParty.Focal.compFlatPure,
          StrategyOver.TwoParty.Counterpart.appendFlat,
          PFunctor.FreeM.append_roll, PFunctor.FreeM.Displayed.Decoration.append_roll,
          run, InteractionOver.runSpec, InteractionOver.TwoParty.pairedSpec,
          InteractionOver.TwoParty.paired, participantProfile, collectParticipantOutputs,
          participantOutputFamily, bind_assoc, pure_bind]
        let mapCpt :
            ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
              (rest x) (rRest x) (fun tr => MidC ⟨x, tr⟩)) →
            ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
              (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
              (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                (fun path => r₂ ⟨x, path⟩))
              (fun tr => OutputC ⟨x, tr⟩)) :=
          fun a => ⟨a.1, StrategyOver.TwoParty.Counterpart.appendFlat a.2
            (fun p o => cpt₂ ⟨a.1, p⟩ o)⟩
        simp only [LawfulMonad.do_bind_pure_comp]
        refine (bind_map_left mapCpt cpt₁ _).trans ?_
        apply bind_congr
        intro xc
        cases xc with
        | mk x cNext =>
            let mapStrat :
                StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
                  (rest x) (rRest x) (fun tr => MidP ⟨x, tr⟩) →
                StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
                  (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                  (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                    (fun path => r₂ ⟨x, path⟩))
                  (fun tr => OutputP ⟨x, tr⟩) :=
              fun a => StrategyOver.TwoParty.Focal.compFlatPure a
                (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
            refine (bind_map_left mapStrat (strat₁ x) _).trans ?_
            apply bind_congr
            intro next
            let addPrefix :
                ((tr : PFunctor.FreeM.Path (PFunctor.FreeM.append (rest x)
                  (fun path => s₂ ⟨x, path⟩))) ×
                  (fun tr => OutputP ⟨x, tr⟩) tr ×
                  (fun tr => OutputC ⟨x, tr⟩) tr) →
                ((tr : PFunctor.FreeM.Path
                  (PFunctor.FreeM.append (Spec.node X rest) s₂)) ×
                  OutputP tr × OutputC tr) :=
              fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
            simpa [monad_norm, addPrefix, PFunctor.FreeM.Path.append] using
              go (rest x) (rRest x)
                (s₂ := fun path => s₂ ⟨x, path⟩)
                (r₂ := fun path => r₂ ⟨x, path⟩)
                (OutputP := fun tr => OutputP ⟨x, tr⟩)
                (OutputC := fun tr => OutputC ⟨x, tr⟩)
                next
                (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
                cNext
                (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out)
                (fun a => g (addPrefix a))
  rw [StrategyOver.TwoParty.Focal.compFlat_eq_pure_compFlatPure strat₁ f]
  simpa [monad_norm] using go s₁ r₁ strat₁ f cpt₁ cpt₂ pure

/-- Executing a flat composed strategy/counterpart factors into first executing
the prefix interaction and then executing the suffix continuation. -/
theorem run_compFlat_appendFlat
    {m : Type u → Type u} [Monad m] [LawfulCommMonad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {MidP MidC : PFunctor.FreeM.Path s₁ → Type u}
    {OutputP OutputC : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ MidP)
    (f : (tr₁ : PFunctor.FreeM.Path s₁) → MidP tr₁ →
      m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputP (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂))))
    (cpt₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart s₁ r₁ MidC)
    (cpt₂ : (tr₁ : PFunctor.FreeM.Path s₁) → MidC tr₁ →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputC (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂))) :
    (do
      let strat ← StrategyOver.TwoParty.Focal.compFlat strat₁ f
      run (s₁.append s₂) (r₁.append r₂) strat
        (StrategyOver.TwoParty.Counterpart.appendFlat cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, out₁⟩ ← run s₁ r₁ strat₁ cpt₁
        let strat₂ ← f tr₁ mid
        let ⟨tr₂, outP, outC⟩ ←
          run (s₂ tr₁) (r₂ tr₁) strat₂ (cpt₂ tr₁ out₁)
        pure ⟨PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂, outP, outC⟩) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {MidP MidC : PFunctor.FreeM.Path s₁ → Type u}
      {s₂ : PFunctor.FreeM.Path s₁ → Spec}
      {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
      {OutputP OutputC : PFunctor.FreeM.Path (s₁.append s₂) → Type u}
      {β : Type u}
      (strat₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ MidP)
      (f : (tr₁ : PFunctor.FreeM.Path s₁) → MidP tr₁ →
        m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputP (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂))))
      (cpt₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart s₁ r₁ MidC)
      (cpt₂ : (tr₁ : PFunctor.FreeM.Path s₁) → MidC tr₁ →
        StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputC (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂)))
      (g : ((tr : PFunctor.FreeM.Path (s₁.append s₂)) × OutputP tr × OutputC tr) → m β) :
      (do
        let r ←
          do let strat ← StrategyOver.TwoParty.Focal.compFlat strat₁ f
             run (s₁.append s₂) (r₁.append r₂) strat
               (StrategyOver.TwoParty.Counterpart.appendFlat cpt₁ cpt₂)
        g r) =
        (do
          let r₁ ← run s₁ r₁ strat₁ cpt₁
          let strat₂ ← f r₁.1 r₁.2.1
          let r₂ ←
            run (s₂ r₁.1) (r₂ r₁.1) strat₂ (cpt₂ r₁.1 r₁.2.2)
          g ⟨PFunctor.FreeM.Path.append s₁ s₂ r₁.1 r₂.1, r₂.2.1, r₂.2.2⟩) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        simp [StrategyOver.TwoParty.Focal.compFlat.eq_1,
          StrategyOver.TwoParty.Counterpart.appendFlat.eq_1, run_done,
          PFunctor.FreeM.Path.append_done]
    | .node X rest, ⟨.sender, rRest⟩ =>
        simp only [StrategyOver.TwoParty.Focal.compFlat,
          StrategyOver.TwoParty.Counterpart.appendFlat,
          PFunctor.FreeM.append_roll, PFunctor.FreeM.Displayed.Decoration.append_roll,
          run, InteractionOver.runSpec, InteractionOver.TwoParty.pairedSpec,
          InteractionOver.TwoParty.paired, participantProfile, collectParticipantOutputs,
          participantOutputFamily, LawfulMonad.do_bind_assoc,
          LawfulMonad.do_bind_pure_comp, pure_bind]
        refine (LawfulMonad.do_bind_assoc strat₁
          (fun xc =>
            (fun restStrat =>
              (⟨xc.1, restStrat⟩ :
                (x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
                  (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                  (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                    (fun path => r₂ ⟨x, path⟩))
                  (fun tr => OutputP ⟨x, tr⟩))) <$>
              StrategyOver.TwoParty.Focal.compFlat xc.2
                (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid))
          _).trans ?_
        apply bind_congr
        intro xc
        cases xc with
        | mk x next =>
            let mapCpt :
                StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
                  (rest x) (rRest x) (fun tr => MidC ⟨x, tr⟩) →
                StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
                  (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                  (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                    (fun path => r₂ ⟨x, path⟩))
                  (fun tr => OutputC ⟨x, tr⟩) :=
              fun a => StrategyOver.TwoParty.Counterpart.appendFlat a
                (fun p o => cpt₂ ⟨x, p⟩ o)
            let mapStratTail :
                StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
                  (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                  (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                    (fun path => r₂ ⟨x, path⟩))
                  (fun tr => OutputP ⟨x, tr⟩) →
                (x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
                  (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                  (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                    (fun path => r₂ ⟨x, path⟩))
                  (fun tr => OutputP ⟨x, tr⟩) :=
              fun restStrat => ⟨x, restStrat⟩
            refine (bind_map_left mapStratTail
              (StrategyOver.TwoParty.Focal.compFlat next
                (s₂ := fun path => s₂ ⟨x, path⟩)
                (r₂ := fun path => r₂ ⟨x, path⟩)
                (Output := fun tr => OutputP ⟨x, tr⟩)
                (fun tr₁ mid => f ⟨x, tr₁⟩ mid)) _).trans ?_
            simp only [mapStratTail]
            let comp :=
              StrategyOver.TwoParty.Focal.compFlat next
                (s₂ := fun path => s₂ ⟨x, path⟩)
                (r₂ := fun path => r₂ ⟨x, path⟩)
                (Output := fun tr => OutputP ⟨x, tr⟩)
                (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
            let obs := mapCpt <$> cpt₁ x
            let k :=
              fun
                (a : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
                  (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                  (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                    (fun path => r₂ ⟨x, path⟩))
                  (fun tr => OutputP ⟨x, tr⟩))
                (a₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
                  (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                  (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                    (fun path => r₂ ⟨x, path⟩))
                  (fun tr => OutputC ⟨x, tr⟩)) => do
                  let y ←
                    (fun (a₂ :
                      (tr : PFunctor.FreeM.Path
                        (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))) ×
                        (fun tr => OutputP ⟨x, tr⟩) tr ×
                        (fun tr => OutputC ⟨x, tr⟩) tr) =>
                      (⟨⟨x, a₂.1⟩, a₂.2.1, a₂.2.2⟩ :
                      (tr : PFunctor.FreeM.Path
                        (PFunctor.FreeM.append (Spec.node X rest) s₂)) ×
                        OutputP tr × OutputC tr)) <$>
                      run (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                        (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                          (fun path => r₂ ⟨x, path⟩))
                        a a₁
                  g y
            change (do let a ← comp; let a₁ ← obs; k a a₁) = _
            refine (LawfulCommMonad.bind_comm comp obs k).trans ?_
            refine (bind_map_left mapCpt (cpt₁ x) _).trans ?_
            apply bind_congr
            intro cNext
            let addPrefix :
                ((tr : PFunctor.FreeM.Path (PFunctor.FreeM.append (rest x)
                  (fun path => s₂ ⟨x, path⟩))) ×
                  (fun tr => OutputP ⟨x, tr⟩) tr ×
                  (fun tr => OutputC ⟨x, tr⟩) tr) →
                ((tr : PFunctor.FreeM.Path
                  (PFunctor.FreeM.append (Spec.node X rest) s₂)) ×
                  OutputP tr × OutputC tr) :=
              fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
            simp only [comp, k, mapCpt]
            calc
              (do
                let strat ←
                  StrategyOver.TwoParty.Focal.compFlat next
                    (s₂ := fun path => s₂ ⟨x, path⟩)
                    (r₂ := fun path => r₂ ⟨x, path⟩)
                    (Output := fun tr => OutputP ⟨x, tr⟩)
                    (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
                let y ←
                  addPrefix <$> run
                    (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                    (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                      (fun path => r₂ ⟨x, path⟩))
                    strat
                    (StrategyOver.TwoParty.Counterpart.appendFlat cNext
                      (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out))
                g y) =
                  (do
                    let strat ←
                      StrategyOver.TwoParty.Focal.compFlat next
                        (s₂ := fun path => s₂ ⟨x, path⟩)
                        (r₂ := fun path => r₂ ⟨x, path⟩)
                        (Output := fun tr => OutputP ⟨x, tr⟩)
                        (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
                    let y ← run
                      (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                      (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                        (fun path => r₂ ⟨x, path⟩))
                      strat
                      (StrategyOver.TwoParty.Counterpart.appendFlat cNext
                        (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out))
                    g (addPrefix y)) := by
                      apply bind_congr
                      intro strat
                      exact bind_map_left addPrefix
                        (run
                          (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                          (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                            (fun path => r₂ ⟨x, path⟩))
                          strat
                          (StrategyOver.TwoParty.Counterpart.appendFlat cNext
                            (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out)))
                        g
              _ = _ := by
                simpa [monad_norm, addPrefix, PFunctor.FreeM.Path.append] using
                  go (rest x) (rRest x)
                    (s₂ := fun path => s₂ ⟨x, path⟩)
                    (r₂ := fun path => r₂ ⟨x, path⟩)
                    (OutputP := fun tr => OutputP ⟨x, tr⟩)
                    (OutputC := fun tr => OutputC ⟨x, tr⟩)
                    next
                    (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
                    cNext
                    (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out)
                    (fun a => g (addPrefix a))
    | .node X rest, ⟨.receiver, rRest⟩ =>
        simp only [StrategyOver.TwoParty.Focal.compFlat,
          StrategyOver.TwoParty.Counterpart.appendFlat,
          PFunctor.FreeM.append_roll, PFunctor.FreeM.Displayed.Decoration.append_roll,
          run, InteractionOver.runSpec, InteractionOver.TwoParty.pairedSpec,
          InteractionOver.TwoParty.paired, participantProfile, collectParticipantOutputs,
          participantOutputFamily, LawfulMonad.do_bind_assoc,
          LawfulMonad.do_bind_pure_comp, pure_bind]
        let mapCpt :
            ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
              (rest x) (rRest x) (fun tr => MidC ⟨x, tr⟩)) →
            ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
              (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
              (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                (fun path => r₂ ⟨x, path⟩))
              (fun tr => OutputC ⟨x, tr⟩)) :=
          fun a => ⟨a.1, StrategyOver.TwoParty.Counterpart.appendFlat a.2
            (fun p o => cpt₂ ⟨a.1, p⟩ o)⟩
        refine (bind_map_left mapCpt cpt₁ _).trans ?_
        apply bind_congr
        intro xc
        cases xc with
        | mk x cNext =>
            let comp :
                StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
                  (rest x) (rRest x) (fun tr => MidP ⟨x, tr⟩) →
                m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
                  (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                  (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                    (fun path => r₂ ⟨x, path⟩))
                  (fun tr => OutputP ⟨x, tr⟩)) :=
              fun next =>
                StrategyOver.TwoParty.Focal.compFlat next
                  (s₂ := fun path => s₂ ⟨x, path⟩)
                  (r₂ := fun path => r₂ ⟨x, path⟩)
                  (Output := fun tr => OutputP ⟨x, tr⟩)
                  (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
            let addPrefix :
                ((tr : PFunctor.FreeM.Path (PFunctor.FreeM.append (rest x)
                  (fun path => s₂ ⟨x, path⟩))) ×
                  (fun tr => OutputP ⟨x, tr⟩) tr ×
                  (fun tr => OutputC ⟨x, tr⟩) tr) →
                ((tr : PFunctor.FreeM.Path
                  (PFunctor.FreeM.append (Spec.node X rest) s₂)) ×
                  OutputP tr × OutputC tr) :=
              fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
            simp only [mapCpt]
            refine (LawfulMonad.do_bind_assoc (strat₁ x) comp
              (fun strat => do
                let y ←
                  addPrefix <$> run
                    (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                    (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                      (fun path => r₂ ⟨x, path⟩))
                    strat
                    (StrategyOver.TwoParty.Counterpart.appendFlat cNext
                      (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out))
                g y)).trans ?_
            calc
              (do
                let next ← strat₁ x
                let strat ← comp next
                let y ←
                  addPrefix <$> run
                    (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                    (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                      (fun path => r₂ ⟨x, path⟩))
                    strat
                    (StrategyOver.TwoParty.Counterpart.appendFlat cNext
                      (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out))
                g y) =
                  (do
                    let next ← strat₁ x
                    let strat ← comp next
                    let y ← run
                      (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                      (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                        (fun path => r₂ ⟨x, path⟩))
                      strat
                      (StrategyOver.TwoParty.Counterpart.appendFlat cNext
                        (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out))
                    g (addPrefix y)) := by
                      apply bind_congr
                      intro next
                      apply bind_congr
                      intro strat
                      exact bind_map_left addPrefix
                        (run
                          (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                          (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                            (fun path => r₂ ⟨x, path⟩))
                          strat
                          (StrategyOver.TwoParty.Counterpart.appendFlat cNext
                            (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out)))
                        g
              _ = _ := by
                apply bind_congr
                intro next
                let addPrefix₁ :
                    ((tr : PFunctor.FreeM.Path (rest x)) ×
                      (fun tr => MidP ⟨x, tr⟩) tr × (fun tr => MidC ⟨x, tr⟩) tr) →
                    ((tr : PFunctor.FreeM.Path (Spec.node X rest)) × MidP tr × MidC tr) :=
                  fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
                calc
                  (do
                    let strat ← comp next
                    let y ← run
                      (PFunctor.FreeM.append (rest x) (fun path => s₂ ⟨x, path⟩))
                      (PFunctor.FreeM.Displayed.Decoration.append (rRest x)
                        (fun path => r₂ ⟨x, path⟩))
                      strat
                      (StrategyOver.TwoParty.Counterpart.appendFlat cNext
                        (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out))
                    g (addPrefix y)) =
                      (do
                        let r₁ ← run (rest x) (rRest x) next cNext
                        let strat₂ ← f ⟨x, r₁.1⟩ r₁.2.1
                        let r₂ ←
                          run (s₂ ⟨x, r₁.1⟩) (r₂ ⟨x, r₁.1⟩) strat₂
                            (cpt₂ ⟨x, r₁.1⟩ r₁.2.2)
                        g ⟨⟨x, PFunctor.FreeM.Path.append (rest x)
                            (fun path => s₂ ⟨x, path⟩) r₁.1 r₂.1⟩,
                          r₂.2.1, r₂.2.2⟩) := by
                            simpa [monad_norm, comp, addPrefix, PFunctor.FreeM.Path.append] using
                              go (rest x) (rRest x)
                                (s₂ := fun path => s₂ ⟨x, path⟩)
                                (r₂ := fun path => r₂ ⟨x, path⟩)
                                (OutputP := fun tr => OutputP ⟨x, tr⟩)
                                (OutputC := fun tr => OutputC ⟨x, tr⟩)
                                next
                                (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
                                cNext
                                (fun tr₁ out => cpt₂ ⟨x, tr₁⟩ out)
                                (fun a => g (addPrefix a))
                  _ = _ := by
                    exact (bind_map_left addPrefix₁ (run (rest x) (rRest x) next cNext)
                      (fun r₁ => do
                        let strat₂ ← f r₁.1 r₁.2.1
                        let r₂ ← run (s₂ r₁.1) (r₂ r₁.1) strat₂ (cpt₂ r₁.1 r₁.2.2)
                        g ⟨PFunctor.FreeM.Path.append (Spec.node X rest) s₂ r₁.1 r₂.1,
                          r₂.2.1, r₂.2.2⟩)).symm
  simpa [monad_norm] using go s₁ r₁ strat₁ f cpt₁ cpt₂ pure

/-- Executing a factored composed strategy/counterpart (using `comp` and
`StrategyOver.TwoParty.Counterpart.append`) factors into first executing the
prefix interaction and then
executing the suffix continuation. Outputs are transported via `packAppend`. -/
theorem run_comp_append
    {m : Type u → Type u} [Monad m] [LawfulCommMonad m]
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → RoleDecoration (s₂ tr₁)}
    {MidP MidC : PFunctor.FreeM.Path s₁ → Type u}
    {FP FC : (tr₁ : PFunctor.FreeM.Path s₁) → PFunctor.FreeM.Path (s₂ tr₁) → Type u}
    (strat₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal s₁ r₁ MidP)
    (f : (tr₁ : PFunctor.FreeM.Path s₁) → MidP tr₁ →
      m (StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (s₂ tr₁) (r₂ tr₁) (FP tr₁)))
    (cpt₁ : StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart s₁ r₁ MidC)
    (cpt₂ : (tr₁ : PFunctor.FreeM.Path s₁) → MidC tr₁ →
      StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart (s₂ tr₁) (r₂ tr₁) (FC tr₁)) :
    (do
      let strat ← StrategyOver.TwoParty.Focal.comp strat₁ f
      run (s₁.append s₂) (r₁.append r₂) strat
        (StrategyOver.TwoParty.Counterpart.append cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, out₁⟩ ← run s₁ r₁ strat₁ cpt₁
        let strat₂ ← f tr₁ mid
        let ⟨tr₂, outP, outC⟩ ←
          run (s₂ tr₁) (r₂ tr₁) strat₂ (cpt₂ tr₁ out₁)
        pure ⟨PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂,
          PFunctor.FreeM.Path.packAppend s₁ s₂ FP tr₁ tr₂ outP,
          PFunctor.FreeM.Path.packAppend s₁ s₂ FC tr₁ tr₂ outC⟩) := by
    rw [StrategyOver.TwoParty.Focal.comp_eq_compFlat_mapOutput]
    rw [StrategyOver.TwoParty.Counterpart.append_eq_appendFlat_mapOutput]
    simpa [monad_norm, run_mapOutput_mapOutput] using
      (run_compFlat_appendFlat
        (s₁ := s₁) (s₂ := s₂) (r₁ := r₁) (r₂ := r₂)
        (strat₁ := strat₁)
        (f := fun tr₁ mid => do
          let strat₂ ← f tr₁ mid
          pure (StrategyOver.TwoParty.Focal.mapOutput
            (fun tr₂ x => PFunctor.FreeM.Path.packAppend s₁ s₂ FP tr₁ tr₂ x) strat₂))
        (cpt₁ := cpt₁)
        (cpt₂ := fun tr₁ out =>
          StrategyOver.TwoParty.Counterpart.mapOutput
            (fun tr₂ x => PFunctor.FreeM.Path.packAppend s₁ s₂ FC tr₁ tr₂ x)
            (cpt₂ tr₁ out)))

/-- Role swapping commutes with replication. -/
theorem RoleDecoration.swap_replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    RoleDecoration.swap
        (PFunctor.FreeM.Displayed.Decoration.replicate
          (P := Spec.basePFunctor) (α := PUnit.{u+1}) PUnit.unit roles n) =
      PFunctor.FreeM.Displayed.Decoration.replicate
        (P := Spec.basePFunctor) (α := PUnit.{u+1}) PUnit.unit (RoleDecoration.swap roles) n :=
  PFunctor.FreeM.Displayed.Decoration.map_replicate
    (P := Spec.basePFunctor) (α := PUnit.{u+1})
    (fun _ => Role.swap) PUnit.unit roles n

/-- `n`-fold counterpart iteration on `spec.replicate n`, threading state `β`
through each round. -/
def _root_.Interaction.StrategyOver.TwoParty.Counterpart.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {β : Type u} :
    (n : Nat) →
    (Fin n → β →
      StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles (fun _ => β)) →
    β →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
      (spec.replicate n)
      (PFunctor.FreeM.Displayed.Decoration.replicate
        (P := Spec.basePFunctor) (α := PUnit.{u+1}) PUnit.unit roles n)
      (fun _ => β)
  | 0, _, b => b
  | n + 1, step, b =>
      StrategyOver.TwoParty.Counterpart.appendFlat (step 0 b)
        (fun _ b' => iterate n (fun i => step i.succ) b')

/-- `n`-fold role-aware strategy iteration on `spec.replicate n`, threading state `α`
through each round. -/
def _root_.Interaction.StrategyOver.TwoParty.Focal.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {α : Type u} :
    (n : Nat) →
    (step : Fin n → α →
      m (StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles (fun _ => α))) →
    α →
    m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
      (spec.replicate n)
      (PFunctor.FreeM.Displayed.Decoration.replicate
        (P := Spec.basePFunctor) (α := PUnit.{u+1}) PUnit.unit roles n)
      (fun _ => α))
  | 0, _, a => pure a
  | n + 1, step, a => do
    let strat ← step 0 a
    StrategyOver.TwoParty.Focal.compFlat strat
      (fun _ mid => iterate n (fun i => step i.succ) mid)

/-- Compose counterparts along a state chain with stage-dependent output. At each stage,
the step transforms `Family i s` into a counterpart whose output is
`Family (i+1) (advance i s tr)`. The full state chain output is
`PFunctor.FreeM.Path.stateChainFamily Family`. -/
def _root_.Interaction.StrategyOver.TwoParty.Counterpart.stateChainComp
    {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → PFunctor.FreeM.Path (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
        (spec i s) (roles i s) (fun tr => Family (i + 1) (advance i s tr))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
      (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)
      (PFunctor.FreeM.Displayed.Decoration.stateChain
        (P := Spec.basePFunctor) (α := PUnit.{u+1}) (a := PUnit.unit)
        (advance := advance) roles n i s)
      (PFunctor.FreeM.Path.stateChainFamily Family n i s)
  | 0, _, _, b => b
  | n + 1, i, s, b =>
      StrategyOver.TwoParty.Counterpart.append (step i s b)
        (fun tr b' => stateChainComp step n (i + 1) (advance i s tr) b')

/-- Compose role-aware strategies along a state chain with stage-dependent output.
At each stage, the step transforms `Family i s` into a strategy whose output is
`Family (i+1) (advance i s tr)`. The full state chain output is
`PFunctor.FreeM.Path.stateChainFamily Family`. -/
def _root_.Interaction.StrategyOver.TwoParty.Focal.stateChainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → PFunctor.FreeM.Path (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      m (StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (spec i s) (roles i s)
        (fun tr => Family (i + 1) (advance i s tr)))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
      (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)
      (PFunctor.FreeM.Displayed.Decoration.stateChain
        (P := Spec.basePFunctor) (α := PUnit.{u+1}) (a := PUnit.unit)
        (advance := advance) roles n i s)
      (PFunctor.FreeM.Path.stateChainFamily Family n i s))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    StrategyOver.TwoParty.Focal.comp strat
      (fun tr mid => stateChainComp step n (i + 1) (advance i s tr) mid)

end TwoParty
end Interaction
