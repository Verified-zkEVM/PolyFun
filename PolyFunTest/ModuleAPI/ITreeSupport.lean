/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.WP.Support

/-!
# Interaction-tree support through ordinary imports

The `MonadAttach` instances on interaction trees, the possible-output equations and the
identifications with the demonic and angelic readings are usable from a module that imports them
without `import all`, at independent universes.
-/

public section

universe uA uB uα uβ

namespace PolyFunTest.ModuleAPI.ITreeSupport

variable {F : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

example : ExactMonadAttach (ITree F) :=
  inferInstance

example (t : ITree F α) : Subtype.val <$> ITree.attach t = t :=
  ITree.map_attach t

example (t : ITree F α) (k : α → ITree F β) (b : β) :
    ITree.CanReturn (ITree.bind t k) b ↔ ∃ a, ITree.CanReturn t a ∧ ITree.CanReturn (k a) b :=
  ITree.canReturn_bind_iff

example (r : α) : ¬ ITree.CanReturn (ITree.diverge : ITree F α) r :=
  ITree.not_canReturn_diverge r

example (t : ITree F α) (post : α → Prop) :
    ITree.wpPartial (PFunctor.OpSpec.demonic F) t post ↔ MonadAttach.AllOutputs post t :=
  ITree.wpPartial_demonic_iff_allOutputs

example (t : ITree F α) (post : α → Prop) :
    ITree.wpTotal (PFunctor.OpSpec.angelic F) t post ↔ MonadAttach.SomeOutput post t :=
  ITree.wpTotal_angelic_iff_someOutput

end PolyFunTest.ModuleAPI.ITreeSupport
