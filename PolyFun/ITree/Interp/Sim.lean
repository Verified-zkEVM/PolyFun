/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Interp.Defs
public import PolyFun.ITree.Sim.Facts
public import PolyFun.ITree.Bisim.Iter

/-!
# Interpretation into interaction trees

When the target monad is an interaction tree, `interp` is `simulate` by definition, so the strong
computation equations and the weak-bisimulation laws of simulation transfer verbatim: the
computation rules hold as equalities, interpretation respects weak bisimulation of the source,
and interpreting through the identity handler or through a composite handler behaves as expected.
The generic laws of `PolyFun.ITree.Interp.Laws` give the same facts up to the target's
equivalence, which for an interaction tree is weak bisimulation; these are the sharper forms.
-/

@[expose] public section

universe u uFA uFB

namespace ITree

variable {E : PFunctor.{u, u}} {F : PFunctor.{uFA, uFB}} {α : Type u}

theorem interp_pure_eq (h : PFunctor.Handler (ITree F) E) (r : α) :
    interp h (pure r) = pure r :=
  simulate_pure h r

theorem interp_step_eq (h : PFunctor.Handler (ITree F) E) (t : ITree E α) :
    interp h (step t) = step (interp h t) :=
  simulate_step_eq h t

theorem interp_query_eq_bind (h : PFunctor.Handler (ITree F) E) (a : E.A)
    (k : E.B a → ITree E α) :
    interp h (query a k) = bind (h a) (fun b => step (interp h (k b))) :=
  simulate_query_eq_bind h a k

/-- Interpretation respects weak bisimulation of the source tree. -/
theorem interp_weakBisimRel {β : Type u} {RR : α → β → Prop} (h : PFunctor.Handler (ITree F) E)
    {t : ITree E α} {s : ITree E β} (hts : WeakBisimRel RR t s) :
    WeakBisimRel RR (interp h t) (interp h s) :=
  simulate_weakBisimRel h hts

/-- Interpreting through the identity handler changes nothing up to weak bisimulation. -/
theorem interp_id_weak (t : ITree E α) : WeakBisim (interp (Handler.id E) t) t :=
  simulate_id t

/-- Interpreting twice is interpreting through the composite handler. -/
theorem interp_comp_weak {G : PFunctor.{u, u}} (outer : PFunctor.Handler (ITree F) G)
    (inner : PFunctor.Handler (ITree G) E) (t : ITree E α) :
    WeakBisim (interp outer (interp inner t)) (interp (Handler.comp outer inner) t) :=
  simulate_comp outer inner t

/-- Interpretation into a tree distributes over sequencing up to weak bisimulation. -/
theorem interp_bind_weak {β : Type u} (h : PFunctor.Handler (ITree F) E) (t : ITree E α)
    (k : α → ITree E β) :
    WeakBisim (interp h (bind t k)) (bind (interp h t) (fun a => interp h (k a))) :=
  simulate_bind h t k

end ITree
