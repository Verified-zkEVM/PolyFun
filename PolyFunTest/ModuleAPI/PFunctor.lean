/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Dynamical.DynComputation.Bounded
import PolyFun.PFunctor.Free.Basic
public import PolyFun.IPFunctor.Basic

/-!
# Ordinary-import canaries for the polynomial-functor API

These examples pin generic laws used by VCVio through ordinary imports, so
their availability does not accidentally depend on imported implementation
bodies.
-/

@[expose] public section

open scoped MonadHom

universe u v w uA uB uA₂ uB₂ uα uβ

namespace PolyFunTest.ModuleAPI.PFunctor

open _root_.PFunctor

example {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    (f : α → β) (x : α) :
    FreeM.map (P := P) f (pure x) = pure (f x) := by
  rw [FreeM.map_pure]

example {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    (f : α → β) (position : P.A) (next : P.B position → FreeM P α) :
    FreeM.map f (FreeM.liftBind position next) =
      FreeM.liftBind position (fun direction ↦ FreeM.map f (next direction)) :=
  FreeM.map_liftBind f position next

example {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    (f : α → β) (position : P.A) (next : P.B position → FreeM P α) :
    FreeM.map f ((FreeM.lift position).bind next) =
      (FreeM.lift position).bind
        (fun direction ↦ FreeM.map f (next direction)) := by
  rw [FreeM.map_bind]

example {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    {γ : Type w} (f : β → γ) (program : FreeM P α)
    (next : α → FreeM P β) :
    FreeM.map f (FreeM.bind program next) =
      FreeM.bind program (fun value ↦ FreeM.map f (next value)) := by
  rw [FreeM.map_bind]

example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
    {α : Type uα} (lens : Lens P Q) (position : P.A)
    (next : P.B position → FreeM P α) :
    FreeM.mapLens lens (FreeM.liftBind position next) =
      FreeM.liftBind (lens.toFunA position)
        (fun direction ↦ FreeM.mapLens lens (next (lens.toFunB position direction))) :=
  FreeM.mapLens_liftBind lens position next

example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
    {α : Type uα} {β : Type uβ}
    (M : DynSystem.DynComputation.{u} P α β) (lens : Lens P Q)
    (k : Nat) (state : M.State) :
    (M.wrap lens).unroll k state = FreeM.mapLens lens (M.unroll k state) :=
  M.unroll_wrap lens k state

example {P : PFunctor.{uA, uB}} {m : Type uB → Type v}
    {n : Type uB → Type w} [Monad m] [Monad n]
    (handler : (position : P.A) → m (P.B position))
    (hom : m →ᵐ n) {X : Type uB} (program : FreeM P X) :
    hom (program.liftM handler) =
      program.liftM (fun position => hom (handler position)) :=
  FreeM.liftM_natural handler hom program

/-- Lemmas staged in `ToCslib` reach PolyFun consumers through the ordinary re-export. -/
example {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {γ : Type w}
    (f : β → γ) (x : FreeM P α) (cont : α → FreeM P β) :
    FreeM.map f (x.bind cont) = x.bind fun a => (cont a).map f :=
  FreeM.map_bind f x cont

example {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} (onValue : α → β)
    (onEffect : (a : P.A) → (P.B a → β) → β) (a : P.A) (cont : P.B a → FreeM P α) :
    FreeM.foldFreeM onValue onEffect ((FreeM.lift a).bind cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  rw [FreeM.foldFreeM_bind, FreeM.foldFreeM_lift]

/-- Object equality works through the public projections at independent universes. -/
example {P : PFunctor.{uA, uB}} {α : Type uα} {x y : P α}
    (shapes : x.fst = y.fst) (children : HEq x.snd y.snd) : x = y := by
  ext
  · exact shapes
  · exact children

example {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    (f : α → β) (a : P.A) (children : P.B a → α) :
    P.map f (.mk a children) = .mk a (f ∘ children) := by
  rw [PFunctor.map_eq]

/-- Indexed mapping retains each child's source fiber, even when the fibers differ. -/
example {I : Type u} {J : Type v} {P : IPFunctor.{u, v, uA, uB} I J}
    {X : I → Type uα} {Y : I → Type uβ}
    (f : (i : I) → X i → Y i) {j : J} (a : P.A j)
    (children : (b : P.B j a) → X (P.src j a b)) (b : P.B j a) :
    (P.map f (.mk a children)).snd b = f (P.src j a b) (children b) := by
  rw [IPFunctor.map_snd]
  rfl

example {I : Type u} {J : Type v} {P : IPFunctor.{u, v, uA, uB} I J}
    {X : I → Type uα} {j : J} {x y : P.Obj X j}
    (shapes : x.fst = y.fst) (children : HEq x.snd y.snd) : x = y := by
  apply IPFunctor.Obj.ext
  · exact shapes
  · exact children

/-- Consumers can eliminate objects without accessing their Sigma representation. -/
example {I : Type u} {J : Type v} {P : IPFunctor.{u, v, uA, uB} I J}
    {X : I → Type uα} {j : J} (x : P.Obj X j) :
    ∃ a children, x = IPFunctor.Obj.mk a children := by
  cases x using IPFunctor.Obj.rec with
  | mk a children => exact ⟨a, children, rfl⟩

/-- Native constructor injectivity exposes dependent children through an ordinary import. -/
example {P : PFunctor.{uA, uB}} {α : Type uα}
    {a b : P.A} {f : P.B a → α} {g : P.B b → α}
    (h : PFunctor.Obj.mk a f = PFunctor.Obj.mk b g) : a = b ∧ HEq f g := by
  simpa only [PFunctor.Obj.mk.inj_iff] using h

/-- Eliminating a public object leaves the native map equation directly usable. -/
example {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    (f : α → β) (x : P.Obj α) :
    P.map f x = PFunctor.Obj.mk x.fst (f ∘ x.snd) := by
  cases x using PFunctor.Obj.rec with
  | mk a children =>
      rw [PFunctor.map_eq]
      rfl

/-- Two directions select genuinely different result types. -/
abbrev mixedFibers : IPFunctor Bool Unit where
  A _ := Unit
  B _ _ := Bool
  src _ _ direction := direction

abbrev mixedFamily : Bool → Type
  | false => Nat
  | true => Bool

def mixedObject : mixedFibers.Obj mixedFamily () :=
  .mk () (fun | false => 7 | true => false)

def mixedMap : (i : Bool) → mixedFamily i → mixedFamily i
  | false, n => n + 1
  | true, b => !b

/-- Mapping follows the source index instead of identifying the child fibers. -/
example : (mixedFibers.map mixedMap mixedObject).snd false = 8 ∧
    (mixedFibers.map mixedMap mixedObject).snd true = true := by
  constructor <;> rfl

/-! ### Indexed-sum positions

Positions of `PFunctor.sigma F` are built with `sigma.mk` and taken apart with `sigma.fst`,
`sigma.snd`, and `sigma.rec`. The constructor has type `(sigma F).A` at every transparency,
so a statement about such a position typechecks under the instance checker without a local
reducibility override on `sigma` (the wiring consumers previously needed one). -/

set_option linter.tacticCheckInstances true in
example (P : PFunctor.{0, 0}) (f : (PFunctor.sigma fun _ : Unit => P).A → Nat) (a : P.A) :
    f (PFunctor.sigma.mk () a) = f (PFunctor.sigma.mk () a) := by
  rfl

example {I : Type u} {F : I → PFunctor.{uA, uB}} (i : I) (a : (F i).A) :
    PFunctor.sigma.fst (PFunctor.sigma.mk (F := F) i a) = i ∧
      PFunctor.sigma.snd (PFunctor.sigma.mk (F := F) i a) = a := by
  simp

example {I : Type u} {F : I → PFunctor.{uA, uB}} (i : I) (a : (F i).A) :
    (PFunctor.sigma F).B (PFunctor.sigma.mk i a) = (F i).B a :=
  PFunctor.sigma.B_mk i a

/-- Eliminating a position by its index and member position. -/
example {I : Type u} {F : I → PFunctor.{uA, uB}} (x : (PFunctor.sigma F).A) :
    PFunctor.sigma.mk (PFunctor.sigma.fst x) (PFunctor.sigma.snd x) = x := by
  induction x using PFunctor.sigma.rec with
  | mk i a => rfl

/-- Two positions agree when their indices and member positions do. -/
example {I : Type u} {F : I → PFunctor.{uA, uB}} (i : I) (a b : (F i).A) (h : a = b) :
    PFunctor.sigma.mk (F := F) i a = PFunctor.sigma.mk i b :=
  PFunctor.sigma.ext rfl (heq_of_eq h)

/-- A sigma-indexed handler answers each member's request with that member's handler. -/
example {I : Type u} {F : I → PFunctor.{uA, u}} {m : Type u → Type v}
    (h : (i : I) → Handler m (F i)) (i : I) (a : (F i).A) :
    Handler.sigma h (PFunctor.sigma.mk i a) = h i a := by
  simp

end PolyFunTest.ModuleAPI.PFunctor
