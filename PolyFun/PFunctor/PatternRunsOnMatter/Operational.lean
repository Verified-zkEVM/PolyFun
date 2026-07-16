/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.PatternRunsOnMatter.Universal
public import PolyFun.PFunctor.Handler

/-!
# Operational laws for patterns running on matter

Decoding the object-level `runOn` construction gives an ordinary finite free
monad tree whose leaves contain the complete source pattern path and reached
matter vertex. This module proves its recursive and grafting laws, connects
the universal map to substitution monoids, and gives an executable handler
interpreter.
-/

@[expose] public section

universe pA pB qA qB u v

namespace PFunctor.FreeP

variable {P : PFunctor.{pA, pB}} {Q : PFunctor.{qA, qB}}

/-- Decode the synchronized object produced by `runObj` into an ordinary
finite free-monad tree. -/
def runTree (pattern : (FreeP P).A) (matter : (CofreeP Q).A) :
    FreeM (P ⊗ Q) (FreeM.Path pattern × M.Vertex matter) :=
  FreeP.decode (runObj pattern matter)

@[simp]
theorem runTree_pure (value : PUnit.{pB + 1})
    (matter : (CofreeP Q).A) :
    runTree (P := P) (pure value) matter =
      pure (PUnit.unit, M.Vertex.root matter) :=
  rfl

theorem runTree_liftBind (a : P.A)
    (rest : P.B a → FreeM P PUnit.{pB + 1})
    (matter : (CofreeP Q).A) :
    runTree (FreeM.liftBind a rest) matter =
      FreeM.liftBind (P := P ⊗ Q) (a, M.head matter) (fun direction :
          P.B a × Q.B (M.head matter) =>
        FreeM.map
          (fun pulled =>
            (FreeM.Path.cons a rest direction.1 pulled.1,
              M.Vertex.child direction.2 pulled.2))
          (runTree (rest direction.1)
            (M.children matter direction.2))) := by
  unfold runTree
  rw [runObj_liftBind, decode_node]
  apply congrArg (FreeM.liftBind (P := P ⊗ Q) (a, M.head matter))
  funext direction
  change P.B a × Q.B (M.head matter) at direction
  rw [decode_relabel]

private theorem freeM_map_id {R : PFunctor.{pA, pB}} {α : Type u}
    (x : FreeM R α) : FreeM.map id x = x := by
  induction x with
  | pure value => rfl
  | lift_bind operation continuation ih =>
      exact congrArg (FreeM.liftBind operation) (funext ih)

private theorem freeM_map_comp {R : PFunctor.{pA, pB}}
    {α : Type u} {β : Type v} {γ : Type qA}
    (g : β → γ) (f : α → β) (x : FreeM R α) :
    FreeM.map g (FreeM.map f x) = FreeM.map (g ∘ f) x := by
  induction x with
  | pure value => rfl
  | lift_bind operation continuation ih =>
      exact congrArg (FreeM.liftBind operation) (funext ih)

private theorem freeM_bind_map_left {R : PFunctor.{pA, pB}}
    {α : Type u} {β : Type v} {γ : Type qA}
    (f : α → β) (x : FreeM R α) (g : β → FreeM R γ) :
    FreeM.bind (FreeM.map f x) g = FreeM.bind x (g ∘ f) := by
  induction x with
  | pure value => rfl
  | lift_bind operation continuation ih =>
      exact congrArg (FreeM.liftBind operation) (funext ih)

/-- Running a grafted pattern first runs the outer tree and then, at each
reached leaf/vertex pair, runs the selected inner tree on the reached matter
subtree. Both dependent path indices compose in source order. -/
theorem runTree_append
    (pattern : (FreeP P).A)
    (next : FreeM.Path pattern → (FreeP P).A)
    (matter : (CofreeP Q).A) :
    runTree (FreeM.append pattern next) matter =
      FreeM.bind (runTree pattern matter) (fun pulled =>
        FreeM.map
          (fun inner =>
            (FreeM.Path.append pattern next pulled.1 inner.1,
              M.Vertex.append pulled.2 inner.2))
          (runTree (next pulled.1) (M.Vertex.subtree pulled.2))) := by
  induction pattern generalizing matter with
  | pure value =>
      cases value
      simp only [FreeM.append, FreeM.Path.append]
      change runTree (next PUnit.unit) matter =
        FreeM.map id (runTree (next PUnit.unit) matter)
      exact (freeM_map_id _).symm
  | liftBind a rest ih =>
      simp only [FreeM.append, runTree_liftBind, FreeM.bind]
      apply congrArg (FreeM.liftBind (P := P ⊗ Q) (a, M.head matter))
      funext direction
      change P.B a × Q.B (M.head matter) at direction
      rw [freeM_bind_map_left]
      rw [ih direction.1
        (fun path => next ⟨direction.1, path⟩)
        (M.children matter direction.2)]
      rw [← FreeM.bind_map_right]
      apply congrArg (FreeM.bind
        (runTree (rest direction.1) (M.children matter direction.2)))
      funext pulled
      rw [freeM_map_comp]
      rfl

/-- The universal interaction map is a substitution-monoid morphism: running
after pattern grafting is convolution multiplication of the two runs. -/
theorem runOn_preserves_substitution
    (P : PFunctor.{pA, max qA qB}) (Q : PFunctor.{qA, qB}) :
    Lens.curry (runOn P Q) ∘ₗ FreeP.mult =
      (SubstMonoid.convolution (CofreeP.comonoid Q)
          (FreeP.substMonoid (P ⊗ Q))).mult ∘ₗ
        (Lens.curry (runOn P Q) ◃ₗ Lens.curry (runOn P Q)) := by
  rw [runOn_eq_xi]
  exact (xiHom P Q).map_mult

section Handler

variable {P : PFunctor.{pA, pB}} {Q : PFunctor.{u, u}}
  {m : Type (max pB u) → Type v} [Monad m]

/-- Interpret the synchronized finite run using an effect handler for paired
pattern/matter operations. -/
def runWithHandler (handler : Handler m (P ⊗ Q))
    (pattern : (FreeP P).A) (matter : (CofreeP Q).A) :
    m (FreeM.Path pattern × M.Vertex matter) :=
  FreeM.liftM handler (runTree pattern matter)

@[simp]
theorem runWithHandler_pure (handler : Handler m (P ⊗ Q))
    (value : PUnit.{pB + 1}) (matter : (CofreeP Q).A) :
    runWithHandler handler (pure value) matter =
      pure (PUnit.unit, M.Vertex.root matter) :=
  rfl

theorem runWithHandler_liftBind [LawfulMonad m]
    (handler : Handler m (P ⊗ Q)) (a : P.A)
    (rest : P.B a → FreeM P PUnit.{pB + 1})
    (matter : (CofreeP Q).A) :
    runWithHandler handler (FreeM.liftBind a rest) matter =
      handler (a, M.head matter) >>= fun direction =>
        runWithHandler handler (rest direction.1)
          (M.children matter direction.2) >>= fun pulled =>
            pure
              (FreeM.Path.cons a rest direction.1 pulled.1,
                M.Vertex.child direction.2 pulled.2) := by
  rw [runWithHandler, runTree_liftBind]
  simp only [FreeM.liftM]
  apply bind_congr
  intro direction
  change P.B a × Q.B (M.head matter) at direction
  change FreeM.liftM handler
      ((fun pulled =>
        (FreeM.Path.cons a rest direction.1 pulled.1,
          M.Vertex.child direction.2 pulled.2)) <$>
        runTree (rest direction.1) (M.children matter direction.2)) = _
  rw [FreeM.liftM_map]
  rw [LawfulMonad.bind_pure_comp]
  rfl

theorem runWithHandler_append [LawfulMonad m]
    (handler : Handler m (P ⊗ Q))
    (pattern : (FreeP P).A)
    (next : FreeM.Path pattern → (FreeP P).A)
    (matter : (CofreeP Q).A) :
    runWithHandler handler (FreeM.append pattern next) matter =
      runWithHandler handler pattern matter >>= fun pulled =>
        runWithHandler handler (next pulled.1)
          (M.Vertex.subtree pulled.2) >>= fun inner =>
            pure
              (FreeM.Path.append pattern next pulled.1 inner.1,
                M.Vertex.append pulled.2 inner.2) := by
  unfold runWithHandler
  rw [runTree_append]
  rw [← FreeM.monad_bind_def, FreeM.liftM_bind]
  apply bind_congr
  intro pulled
  change FreeM.liftM handler
      ((fun inner =>
        (FreeM.Path.append pattern next pulled.1 inner.1,
          M.Vertex.append pulled.2 inner.2)) <$>
        runTree (next pulled.1) (M.Vertex.subtree pulled.2)) = _
  rw [FreeM.liftM_map]
  rw [LawfulMonad.bind_pure_comp]

end Handler

end PFunctor.FreeP
