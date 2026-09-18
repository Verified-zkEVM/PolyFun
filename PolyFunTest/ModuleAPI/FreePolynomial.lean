/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Display.Category
import PolyFun.PFunctor.M.Vertex

/-!
# Ordinary-import consumers of labelled free polynomials

The polynomial extension, free-handler equivalence, and M-type observations
use public object operations at independent universes. The concrete signature
has different response fibers and an operation with no responses.
-/

@[expose] public section

universe uA uB uA' uB' v w

namespace PolyFunTest.ModuleAPI.FreePolynomial

open PFunctor

example {P : PFunctor.{uA, uB}} {α : Type v} (program : FreeM P α) :
    FreeP.decode (FreeP.encode program) = program := by
  rw [FreeP.decode_encode]

example {P : PFunctor.{uA, uB}} {α : Type v} (x : (FreeP P).Obj α) :
    FreeP.encode (FreeP.decode x) = x := by
  rw [FreeP.encode_decode]

example {P : PFunctor.{uA, uB}} {α : Type v} (a : P.A)
    (children : P.B a → (FreeP P).Obj α) :
    (FreeP.node a children).fst = FreeM.liftBind a (fun b => (children b).fst) := by
  rw [FreeP.node_fst]

example {P : PFunctor.{uA, uB}} {α : Type v} (a : P.A)
    (children : P.B a → (FreeP P).Obj α) (b : P.B a)
    (path : FreeM.Path (children b).fst) :
    (FreeP.node a children).snd
        (FreeM.Path.cons a (fun b => (children b).fst) b path) =
      (children b).snd path :=
  FreeP.node_snd_cons a children b path

example {P : PFunctor.{uA, uB}} {α : Type v} (a : P.A)
    (children : P.B a → (FreeP P).Obj α) :
    FreeP.decode (FreeP.node a children) =
      FreeM.liftBind a (fun b => FreeP.decode (children b)) := by
  rw [FreeP.decode_node]

example {P : PFunctor.{uA, uB}} {α : Type v} {β : Type w}
    (f : α → β) (s : (FreeP P).A) (label : FreeM.Path s → α) :
    FreeP.relabel f (PFunctor.Obj.mk s label) =
      PFunctor.Obj.mk s (f ∘ label) := by
  rw [FreeP.relabel_eq_map, PFunctor.map_eq]

example {P : PFunctor.{uA, uB}} {α : Type v} (x : (FreeP P).Obj α) :
    ∃ s label, FreeP.decode x = FreeP.decodeAt s label := by
  cases x using PFunctor.Obj.rec with
  | mk s label => exact ⟨s, label, FreeP.decode_mk s label⟩

example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    (handler : Handler (FreeM Q) P) :
    Handler.ofFreeLens (Handler.toFreeLens handler) = handler :=
  Handler.freeLensEquiv.left_inv handler

example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    (lens : Lens P Q) (tree : M P) :
    (M.dest (M.mapLens lens tree)).fst = lens.toFunA (M.head tree) := by
  rw [M.dest_mapLens, PFunctor.Obj.fst_mk]

example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    (lens : Lens P Q) (tree : M P) (b : Q.B (M.head (M.mapLens lens tree))) :
    M.children (M.mapLens lens tree) b =
      M.mapLens lens (M.children tree (M.pullDirection lens tree b)) :=
  M.children_mapLens lens tree b

abbrev signature : PFunctor where
  A := Option Bool
  B
    | none => Empty
    | some false => Nat
    | some true => Bool

def program : FreeM signature Nat :=
  .liftBind (some false) fun n =>
    .liftBind (some true) fun b => .pure (if b then n + 1 else n)

example : FreeP.decode (FreeP.encode program) = program := by
  rw [FreeP.decode_encode]

/-- A response-free operation has a shape but no complete leaf path. -/
example : FreeP.decode
    (FreeP.node (P := signature) (α := Nat) none Empty.elim) =
      FreeM.liftBind none Empty.elim := by
  rw [FreeP.decode_node]
  congr 1
  funext impossible
  exact impossible.elim

end PolyFunTest.ModuleAPI.FreePolynomial
