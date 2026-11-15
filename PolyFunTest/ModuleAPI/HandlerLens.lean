/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Free
public import PolyFun.PFunctor.Handler.Sum

/-!
# Ordinary-import canaries for handlers along lenses

VCVio's `QueryImpl.comapLens` pulls an oracle implementation back along a lens, and its
`liftComp` relabels a program along the lens of an oracle inclusion. These examples check through
ordinary imports that `Handler.comapLens` satisfies its laws when the interfaces have different
position universes, that interpreting a relabelled program uses the pulled-back handler, that a
sum handler pulled back along an injection is its component, and that a concrete pull-back into
the state monad computes by `rfl`.
-/

@[expose] public section

universe u v uA₁ uA₂ uA₃

namespace PolyFunTest.ModuleAPI.HandlerLens

open _root_.PFunctor

section Generic

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
variable {P : PFunctor.{uA₁, u}} {Q : PFunctor.{uA₂, u}} {R : PFunctor.{uA₃, u}}

example (h : Handler m Q) (l : Lens P Q) (a : P.A) :
    h.comapLens l a = l.toFunB a <$> h (l.toFunA a) := by simp

example (h : Handler m P) : h.comapLens (Lens.id P) = h := by simp

example (h : Handler m R) (l₂ : Lens Q R) (l₁ : Lens P Q) :
    h.comapLens (l₂ ∘ₗ l₁) = (h.comapLens l₂).comapLens l₁ :=
  Handler.comapLens_comp h l₂ l₁

example (h : Handler m Q) (l : Lens P Q) {α : Type u} (x : FreeM P α) :
    (x.mapLens l).liftM h = x.liftM (h.comapLens l) :=
  FreeM.liftM_mapLens l h x

example (h : Handler m Q) (l : Lens P Q) : h.comp (Handler.ofLens l) = h.comapLens l :=
  Handler.comp_ofLens h l

example (f : Handler m P) (g : Handler m Q) :
    (Handler.sum f g).comapLens Lens.inl = f := by simp

example (f : Handler m P) (g : Handler m Q) :
    (Handler.sum f g).comapLens Lens.inr = g := by simp

example (l : Lens P Q) : FreeM.liftMHom (Handler.ofLens l) = FreeM.mapLensHom l :=
  Handler.liftMHom_ofLens l

example (l₂ : Lens Q R) (l₁ : Lens P Q) {α : Type u} (x : FreeM P α) :
    FreeM.mapLensHom (l₂ ∘ₗ l₁) x = FreeM.mapLensHom l₂ (FreeM.mapLensHom l₁ x) := by
  rw [FreeM.mapLensHom_comp, MonadHom.comp_apply]

end Generic

/-! ### A concrete pull-back into the state monad -/

/-- Two requests, `true` and `false`, each answered by a number. -/
abbrev pair : PFunctor.{0, 0} := ⟨Bool, fun _ => Nat⟩

/-- One request, answered by a number. -/
abbrev counter : PFunctor.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- Send both requests to the counter, and add `100` to the answer of a `false` request. -/
def collapse : Lens pair counter :=
  (fun _ => ()) ⇆ fun b n => if b then n else n + 100

/-- A counter in the state monad: answer with the count, then increment it. -/
def tick : Handler (StateM Nat) counter :=
  fun _ => modifyGet fun n => (n, n + 1)

/-- Ask `true`, then `false`, and return both answers in order. -/
def twoRequests : FreeM pair (Nat × Nat) :=
  FreeM.liftBind true fun a => FreeM.liftBind false fun b => pure (a, b)

/-- The pulled-back handler answers a `false` request from the counter, translated back. -/
example : ((tick.comapLens collapse) false).run 3 = (103, 4) := rfl

/-- The relabelled program reads the counter twice: `0`, then `1 + 100`. -/
example : ((twoRequests.mapLens collapse).liftM tick).run 0 = ((0, 101), 2) := rfl

/-- The same run, through the pulled-back handler. -/
example : ((twoRequests.mapLens collapse).liftM tick).run 0 =
    (twoRequests.liftM (tick.comapLens collapse)).run 0 := by
  rw [FreeM.liftM_mapLens]

end PolyFunTest.ModuleAPI.HandlerLens
