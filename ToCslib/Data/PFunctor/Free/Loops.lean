/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToCslib.Data.PFunctor.Free.Basic
public import ToCslib.Control.Monad.HomTransport

/-!
# Interpretation commutes with loops

`FreeM.liftM s` preserves `pure` and `bind`, so the transport lemmas of
`ToCslib.Control.Monad.HomTransport` specialise to it: interpreting a free program that loops
over a list (or over any `PureForIn` container) is looping over the interpreted bodies.
-/

public section

universe u v w u₁ w₁ uA uB

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {m : Type uB → Type v} [Monad m] [LawfulMonad m]
  (s : (a : P.A) → m (P.B a))

theorem liftM_forIn' {α : Type u₁} {β : Type uB} (l : List α) (init : β)
    (f : (a : α) → a ∈ l → β → P.FreeM (ForInStep β)) :
    FreeM.liftM s (forIn' l init f) = forIn' l init fun a h b => FreeM.liftM s (f a h b) :=
  Cslib.map_listForIn' (fun x => FreeM.liftM s x) (FreeM.liftM_pure s) (FreeM.liftM_bind s)
    l init f

theorem liftM_forIn {α : Type u₁} {β : Type uB} (l : List α) (init : β)
    (f : α → β → P.FreeM (ForInStep β)) :
    FreeM.liftM s (forIn l init f) = forIn l init fun a b => FreeM.liftM s (f a b) :=
  Cslib.map_listForIn (fun x => FreeM.liftM s x) (FreeM.liftM_pure s) (FreeM.liftM_bind s)
    l init f

theorem liftM_forM {α : Type u₁} (l : List α) (f : α → P.FreeM PUnit) :
    FreeM.liftM s (l.forM f) = l.forM fun a => FreeM.liftM s (f a) :=
  Cslib.map_listForM (fun x => FreeM.liftM s x) (FreeM.liftM_pure s) (FreeM.liftM_bind s) l f

theorem liftM_foldlM {σ : Type uB} {α : Type u₁} (f : σ → α → P.FreeM σ) (init : σ)
    (l : List α) :
    FreeM.liftM s (l.foldlM f init) = l.foldlM (fun acc a => FreeM.liftM s (f acc a)) init :=
  Cslib.map_listFoldlM (fun x => FreeM.liftM s x) (FreeM.liftM_pure s) (FreeM.liftM_bind s)
    f init l

theorem liftM_mapM {α : Type u₁} {β : Type uB} (f : α → P.FreeM β) (l : List α) :
    FreeM.liftM s (l.mapM f) = l.mapM fun a => FreeM.liftM s (f a) :=
  Cslib.map_listMapM (fun x => FreeM.liftM s x) (FreeM.liftM_pure s) (FreeM.liftM_bind s) f l

theorem liftM_forIn_of_pureForIn {ρ : Type w₁} {α : Type u₁} {β : Type uB}
    [ForIn (P.FreeM) ρ α] [ForIn m ρ α] [ForIn Id ρ α]
    [Std.Internal.PureForIn (P.FreeM) ρ α] [Std.Internal.PureForIn m ρ α]
    (xs : ρ) (init : β) (f : α → β → P.FreeM (ForInStep β)) :
    FreeM.liftM s (forIn xs init f) = forIn xs init fun a b => FreeM.liftM s (f a b) :=
  Cslib.map_forIn_of_pureForIn (fun x => FreeM.liftM s x) (FreeM.liftM_pure s)
    (FreeM.liftM_bind s) xs init f

end PFunctor.FreeM
