/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler
public import PolyFun.PFunctor.Free.Basic

/-!
# Handlers for binary sums of interfaces

`Handler.sum f g` answers the positions of `P + Q` by routing left positions to `f` and right
positions to `g`; `Handler.sumLift` first lifts each handler into a shared target monad.
Interpreting a free program through a sum handler routes each request by its summand: a
program over `P`, relabelled into `P + Q` along `Lens.inl`, is interpreted by the left handler
alone (`liftM_sum_mapLens_inl`), and symmetrically on the right. The general fact behind these
laws is `FreeM.liftM_mapLens`: interpreting a relabelled program pulls the handler back along
the lens.

No `HAdd` instance is registered here. `Handler` is a reducible function type, so an instance
keyed on it would compete with the pointwise addition of function types whenever the answer
types carry `Add`. A downstream layer that wraps its handlers in a dedicated type may register
the notation there and unfold it to `Handler.sum`.
-/

@[expose] public section

universe u v w uA uA₁ uA₂

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA₁, u}} {Q : PFunctor.{uA₂, u}} {m : Type u → Type v} {α : Type u}

/-- Interpreting a relabelled program pulls the handler back along the lens: the handler
answers at the relabelled position and the lens's backward map translates the direction. -/
theorem liftM_mapLens [Monad m] [LawfulMonad m] (l : Lens P Q) (h : Handler m Q) :
    ∀ x : FreeM P α, (x.mapLens l).liftM h = x.liftM fun a => l.toFunB a <$> h (l.toFunA a)
  | .pure _ => rfl
  | .liftBind a rest => by
    rw [FreeM.mapLens_liftBind]
    change (h (l.toFunA a) >>= fun d => ((rest (l.toFunB a d)).mapLens l).liftM h) =
      (l.toFunB a <$> h (l.toFunA a)) >>= fun d =>
        (rest d).liftM fun a => l.toFunB a <$> h (l.toFunA a)
    rw [bind_map_left]
    exact bind_congr fun d => liftM_mapLens l h (rest (l.toFunB a d))

end FreeM

namespace Handler

variable {P : PFunctor.{uA₁, u}} {Q : PFunctor.{uA₂, u}} {m : Type u → Type v}

/-- Route the positions of `P + Q` to a handler for `P` or a handler for `Q`. -/
def sum (f : Handler m P) (g : Handler m Q) : Handler m (P + Q : PFunctor.{max uA₁ uA₂, u})
  | .inl a => f a
  | .inr b => g b

@[simp] theorem sum_inl (f : Handler m P) (g : Handler m Q) (a : P.A) :
    sum f g (.inl a) = f a := rfl

@[simp] theorem sum_inr (f : Handler m P) (g : Handler m Q) (b : Q.A) :
    sum f g (.inr b) = g b := rfl

section SumLift

variable {n : Type u → Type w} {r : Type u → Type uA} [MonadLiftT m r] [MonadLiftT n r]

/-- `Handler.sum` after lifting both handlers into a shared target monad. -/
def sumLift (f : Handler m P) (g : Handler n Q) : Handler r (P + Q : PFunctor.{max uA₁ uA₂, u}) :=
  sum (mapTarget (fun {α} (x : m α) => (monadLift x : r α)) f)
    (mapTarget (fun {α} (x : n α) => (monadLift x : r α)) g)

theorem sumLift_def (f : Handler m P) (g : Handler n Q) :
    sumLift (r := r) f g =
      sum (mapTarget (fun {α} (x : m α) => (monadLift x : r α)) f)
        (mapTarget (fun {α} (x : n α) => (monadLift x : r α)) g) :=
  rfl

@[simp] theorem sumLift_inl (f : Handler m P) (g : Handler n Q) (a : P.A) :
    sumLift (r := r) f g (.inl a) = (monadLift (f a) : r _) := rfl

@[simp] theorem sumLift_inr (f : Handler m P) (g : Handler n Q) (b : Q.A) :
    sumLift (r := r) f g (.inr b) = (monadLift (g b) : r _) := rfl

end SumLift

/-! ### Requests against the sum

The constructor-form routing equations hold by definition; the `lift` forms need the monad's
right unit law and are not `simp` lemmas, since `simp` derives them from `FreeM.liftM_lift`
and `sum_inl` / `sum_inr`. -/

section Monad

variable [Monad m] {α : Type u}

theorem liftM_sum_liftBind_inl (f : Handler m P) (g : Handler m Q) (a : P.A)
    (k : (P + Q : PFunctor.{max uA₁ uA₂, u}).B (.inl a) →
      FreeM (P + Q : PFunctor.{max uA₁ uA₂, u}) α) :
    (FreeM.liftBind (P := (P + Q : PFunctor.{max uA₁ uA₂, u})) (.inl a) k).liftM
        (sum f g) =
      f a >>= fun d => (k d).liftM (sum f g) :=
  rfl

theorem liftM_sum_liftBind_inr (f : Handler m P) (g : Handler m Q) (b : Q.A)
    (k : (P + Q : PFunctor.{max uA₁ uA₂, u}).B (.inr b) →
      FreeM (P + Q : PFunctor.{max uA₁ uA₂, u}) α) :
    (FreeM.liftBind (P := (P + Q : PFunctor.{max uA₁ uA₂, u})) (.inr b) k).liftM
        (sum f g) =
      g b >>= fun d => (k d).liftM (sum f g) :=
  rfl

end Monad

section LawfulMonad

variable [Monad m] [LawfulMonad m] {α : Type u}

theorem liftM_sum_lift_inl (f : Handler m P) (g : Handler m Q) (a : P.A) :
    (FreeM.lift (P := (P + Q : PFunctor.{max uA₁ uA₂, u})) (.inl a)).liftM (sum f g) = f a := by
  simp

theorem liftM_sum_lift_inr (f : Handler m P) (g : Handler m Q) (b : Q.A) :
    (FreeM.lift (P := (P + Q : PFunctor.{max uA₁ uA₂, u})) (.inr b)).liftM (sum f g) = g b := by
  simp

/-! ### Relabelled programs

A program over one summand, relabelled into the sum along `Lens.inl` or `Lens.inr`, is
interpreted by the handler of that summand. The `_eq_of_apply` forms need only the handler's
values on the relevant injection, not its shape as a `sum`. -/

theorem liftM_mapLens_inl_eq_of_apply (h : Handler m (P + Q : PFunctor.{max uA₁ uA₂, u}))
    (f : Handler m P) (hf : ∀ a, h (.inl a) = f a) (x : FreeM P α) :
    (x.mapLens Lens.inl).liftM h = x.liftM f := by
  rw [FreeM.liftM_mapLens]
  congr 1
  funext a
  simp [Lens.inl, hf]

theorem liftM_mapLens_inr_eq_of_apply (h : Handler m (P + Q : PFunctor.{max uA₁ uA₂, u}))
    (g : Handler m Q) (hg : ∀ b, h (.inr b) = g b) (x : FreeM Q α) :
    (x.mapLens Lens.inr).liftM h = x.liftM g := by
  rw [FreeM.liftM_mapLens]
  congr 1
  funext b
  simp [Lens.inr, hg]

theorem liftM_sum_mapLens_inl (f : Handler m P) (g : Handler m Q) (x : FreeM P α) :
    (x.mapLens Lens.inl).liftM (sum f g) = x.liftM f :=
  liftM_mapLens_inl_eq_of_apply _ _ (fun _ => rfl) x

theorem liftM_sum_mapLens_inr (f : Handler m P) (g : Handler m Q) (x : FreeM Q α) :
    (x.mapLens Lens.inr).liftM (sum f g) = x.liftM g :=
  liftM_mapLens_inr_eq_of_apply _ _ (fun _ => rfl) x

end LawfulMonad

section SumLiftLaws

variable {n : Type u → Type w} {r : Type u → Type uA} [Monad r] [LawfulMonad r] [MonadLiftT m r]
  [MonadLiftT n r] {α : Type u}

theorem liftM_sumLift_mapLens_inl (f : Handler m P) (g : Handler n Q) (x : FreeM P α) :
    (x.mapLens Lens.inl).liftM (sumLift (r := r) f g) =
      x.liftM (mapTarget (fun {α} (y : m α) => (monadLift y : r α)) f) :=
  liftM_mapLens_inl_eq_of_apply _ _ (fun _ => rfl) x

theorem liftM_sumLift_mapLens_inr (f : Handler m P) (g : Handler n Q) (x : FreeM Q α) :
    (x.mapLens Lens.inr).liftM (sumLift (r := r) f g) =
      x.liftM (mapTarget (fun {α} (y : n α) => (monadLift y : r α)) g) :=
  liftM_mapLens_inr_eq_of_apply _ _ (fun _ => rfl) x

end SumLiftLaws

end Handler

end PFunctor
