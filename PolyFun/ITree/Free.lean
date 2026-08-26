/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.ResumptionWithTau
public import PolyFun.PFunctor.Handler.Free
public import PolyFun.PFunctor.Resumption.WellFounded

/-!
# Finite free programs as interaction trees

The canonical embedding of a free polynomial program into an interaction
tree factors through resumptions. Its image contains no silent steps and its
underlying resumption is well-founded. Free handlers map pointwise to ITree
handlers, and interpreting a finite program commutes with ITree simulation up
to weak bisimulation, accounting exactly for the productivity steps inserted
by `ITree.simulate`.
-/

@[expose] public section

universe uEA uEB uFA uFB uα uβ

namespace PFunctor.FreeM

variable {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
  {α : Type uα} {β : Type uβ}

/-- Embed a finite free program as a tau-free interaction tree. -/
def toITree (program : FreeM E α) : _root_.ITree E α :=
  Resumption.toITree (toResumption program)

@[simp] theorem toITree_pure (value : α) :
    toITree (pure value : FreeM E α) = ITree.pure value := by
  simp [toITree]

theorem toITree_liftBind (position : E.A)
    (next : E.B position → FreeM E α) :
    toITree (FreeM.liftBind position next) =
      ITree.query position fun direction => toITree (next direction) := by
  unfold toITree
  rw [FreeM.liftBind_eq, FreeM.toResumption_liftBind,
    Resumption.toITree_query]

@[simp] theorem toITree_bind (program : FreeM E α)
    (next : α → FreeM E β) :
    toITree (FreeM.bind program next) =
      ITree.bind (toITree program) fun value => toITree (next value) := by
  unfold toITree
  rw [toResumption_bind, Resumption.toITree_bind]

@[simp] theorem toITree_map (f : α → β) (program : FreeM E α) :
    toITree (FreeM.map f program) = ITree.map f (toITree program) := by
  unfold toITree
  rw [toResumption_map, Resumption.toITree_map]

@[simp] theorem toITree_mapLens (lens : Lens E F) (program : FreeM E α) :
    toITree (program.mapLens lens) = ITree.mapSpec lens (toITree program) := by
  unfold toITree
  rw [toResumption_mapLens, Resumption.toITree_mapLens]

@[simp] theorem toITree_tauFree (program : FreeM E α) :
    ITree.TauFree (toITree program) :=
  Resumption.toITree_tauFree _

/-- In the unrestricted resumption presentation of ITrees, a finite program
uses only the visible-event summand and never the added `y` tau event. -/
theorem toResumptionWithTau_toITree (program : FreeM E α) :
    ITree.toResumptionWithTau (toITree program) =
      Resumption.mapLens
        (Lens.inl (P := E) (Q := PFunctor.y.{uEA, uEB}))
        (toResumption program) := by
  induction program with
  | pure value => simp
  | lift_bind position next ih =>
      change ITree.toResumptionWithTau
          (toITree (FreeM.liftBind position next)) =
        Resumption.mapLens
          (Lens.inl (P := E) (Q := PFunctor.y.{uEA, uEB}))
          (toResumption (FreeM.liftBind position next))
      rw [toITree_liftBind, ITree.toResumptionWithTau_query,
        FreeM.liftBind_eq, toResumption_liftBind,
        Resumption.mapLens_query]
      congr 1
      funext direction
      exact ih direction

theorem toITree_injective :
    Function.Injective (toITree (E := E) (α := α)) :=
  Resumption.toITree_injective.comp toResumption_injective

/-- Exact, proof-relevant description of the finite fragment of ITrees: a
tree comes from `FreeM` iff it comes from a well-founded resumption. The latter
condition also entails `ITree.TauFree`. -/
theorem exists_toITree_iff (tree : _root_.ITree E α) :
    (∃ program : FreeM E α, toITree program = tree) ↔
      ∃ computation : Resumption E α,
        Resumption.WellFounded computation ∧
          Resumption.toITree computation = tree := by
  constructor
  · rintro ⟨program, rfl⟩
    exact ⟨toResumption program, wellFounded_toResumption program, rfl⟩
  · rintro ⟨computation, wellFounded, rfl⟩
    let program := equivWellFoundedResumption.symm ⟨computation, wellFounded⟩
    refine ⟨program, ?_⟩
    unfold toITree
    rw [equivWellFoundedResumption_symm_apply computation wellFounded]

/-- The finite-program embedding as a monad homomorphism. -/
def toITreeHom : FreeM E →ᵐ _root_.ITree E where
  toFun _ := toITree
  toFun_pure' := toITree_pure
  toFun_bind' := toITree_bind

@[simp] theorem toITreeHom_apply (program : FreeM E α) :
    toITreeHom program = toITree program :=
  rfl

end PFunctor.FreeM

namespace ITree.Handler

variable {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}

/-- Change the target of a free handler pointwise along the canonical
finite-program embedding. -/
def ofFree (handler : PFunctor.Handler (PFunctor.FreeM F) E) :
    ITree.Handler E F :=
  PFunctor.Handler.mapTarget PFunctor.FreeM.toITree handler

@[simp] theorem ofFree_apply
    (handler : PFunctor.Handler (PFunctor.FreeM F) E) (position : E.A) :
    ofFree handler position = PFunctor.FreeM.toITree (handler position) :=
  rfl

end ITree.Handler

namespace PFunctor.FreeM

variable {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
  {α : Type uEB}

/-- Folding a finite program through a free handler and then embedding it as
an ITree agrees with ITree simulation through the embedded handler, up to the
silent productivity steps inserted by `ITree.simulate`. -/
theorem toITree_liftM_weakBisim
    (handler : PFunctor.Handler (FreeM F) E) (program : FreeM E α) :
    ITree.WeakBisim
      (toITree (program.liftM handler))
      (ITree.simulate (ITree.Handler.ofFree handler) (toITree program)) := by
  induction program with
  | pure value =>
      simp only [FreeM.liftM_pure, toITree_pure, ITree.simulate_pure]
      exact ITree.WeakBisim.refl _
  | lift_bind position next ih =>
      change ITree.WeakBisim
        (toITree (FreeM.bind (handler position)
          (fun direction => (next direction).liftM handler)))
        (ITree.simulate (ITree.Handler.ofFree handler)
          (toITree (FreeM.liftBind position next)))
      rw [toITree_bind, toITree_liftBind]
      have hcontinuations :
          ITree.WeakBisim
            (ITree.bind (toITree (handler position))
              (fun direction => toITree ((next direction).liftM handler)))
            (ITree.bind (ITree.Handler.ofFree handler position)
              (fun direction => ITree.simulate (ITree.Handler.ofFree handler)
                (toITree (next direction)))) := by
        exact ITree.bind_weakBisim_cont ih
      exact hcontinuations.trans
        (ITree.simulate_query (ITree.Handler.ofFree handler) position
          (fun direction => toITree (next direction))).symm

end PFunctor.FreeM
