/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Displayed.Append
public import PolyFun.PFunctor.Free.Path

/-!
# `n`-fold append of free polynomial trees

`FreeM.replicate a s n` is the non-dependent `n`-fold append of `s` with a
constant continuation, terminating with the leaf value `a`. Together with
the displayed-layer `Decoration.replicate` and `Decoration.Over.replicate`,
this captures uniform iteration of a `FreeM` tree without referring to the
protocol layer.
-/

@[expose] public section

universe u v w w₂ w₃ w₄

namespace PFunctor
namespace FreeM

variable {P : PFunctor.{u, v}} {α : Type w}

/-- Non-dependent `n`-fold append of a free tree with a constant continuation. -/
def replicate (a : α) (s : FreeM P α) : (n : Nat) → FreeM P α
  | 0 => FreeM.pure a
  | n + 1 => s.append (fun _ => replicate a s n)

@[simp, grind =, freeM_unfold]
theorem replicate_zero (a : α) (s : FreeM P α) :
    replicate a s 0 = FreeM.pure a := rfl

@[simp, freeM_unfold]
theorem replicate_succ (a : α) (s : FreeM P α) (n : Nat) :
    replicate a s (n + 1) = s.append (fun _ => replicate a s n) := rfl

namespace Displayed
namespace Decoration

/-- Replicate a decoration along `FreeM.replicate`. -/
def replicate {Γ : P.A → Type w₂} (a : α) {s : FreeM P α} (d : Decoration Γ s) :
    (n : Nat) → Decoration Γ (FreeM.replicate a s n)
  | 0 => ⟨⟩
  | n + 1 => Decoration.append d (fun _ => Decoration.replicate a d n)

@[simp, freeM_unfold]
theorem replicate_zero {Γ : P.A → Type w₂} (a : α) {s : FreeM P α} (d : Decoration Γ s) :
    Decoration.replicate a d 0 = (⟨⟩ : Decoration Γ (FreeM.replicate a s 0)) :=
  rfl

@[simp, freeM_unfold]
theorem replicate_succ {Γ : P.A → Type w₂} (a : α) {s : FreeM P α} (d : Decoration Γ s)
    (n : Nat) :
    Decoration.replicate a d (n + 1) =
      Decoration.append d (fun _ => Decoration.replicate a d n) :=
  rfl

namespace Over

/-- Replicate a dependent decoration along replicated base decorations. -/
def replicate {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (a : α) {s : FreeM P α} {d : Decoration Γ s} (r : Decoration.Over Γ F s d) :
    (n : Nat) → Decoration.Over Γ F (FreeM.replicate a s n) (d.replicate a n)
  | 0 => ⟨⟩
  | n + 1 => Decoration.Over.append r (fun _ => Over.replicate a r n)

@[simp, freeM_unfold]
theorem replicate_zero {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (a : α) {s : FreeM P α} {d : Decoration Γ s} (r : Decoration.Over Γ F s d) :
    Decoration.Over.replicate a r 0 =
      (⟨⟩ : Decoration.Over Γ F (FreeM.replicate a s 0) (d.replicate a 0)) :=
  rfl

@[simp, freeM_unfold]
theorem replicate_succ {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (a : α) {s : FreeM P α} {d : Decoration Γ s} (r : Decoration.Over Γ F s d) (n : Nat) :
    Decoration.Over.replicate a r (n + 1) =
      Decoration.Over.append r (fun _ => Over.replicate a r n) :=
  rfl

/-- `Decoration.Over.map` commutes with `Over.replicate`. -/
theorem map_replicate {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    {G : (a : P.A) → Γ a → Type w₄} (η : ∀ a γ, F a γ → G a γ) (a : α)
    {s : FreeM P α} {d : Decoration Γ s} (r : Decoration.Over Γ F s d) (n : Nat) :
    Decoration.Over.map η (FreeM.replicate a s n) (d.replicate a n)
        (Decoration.Over.replicate a r n) =
      Decoration.Over.replicate a (Decoration.Over.map η s d r) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Decoration.Over.map_append, ih]

end Over

/-- `Decoration.map` commutes with `Decoration.replicate`. -/
theorem map_replicate {Γ : P.A → Type w₂} {Δ : P.A → Type w₃} (f : ∀ a, Γ a → Δ a)
    (a : α) {s : FreeM P α} (d : Decoration Γ s) : (n : Nat) →
    Decoration.map f (FreeM.replicate a s n) (d.replicate a n) =
      (Decoration.map f s d).replicate a n
  | 0 => rfl
  | n + 1 => by simp [Decoration.map_append, map_replicate f a d n]

end Decoration
end Displayed
end FreeM
end PFunctor

namespace PFunctor.FreeM
universe uA₂ uB₂
variable {P : PFunctor.{u, v}} {Q : PFunctor.{uA₂, uB₂}} {α : Type w}

/-- Prepend one path to a length-`n` replicated tail. -/
abbrev PathAlong.replicateCons (l : Lens P Q) (a : α) (spec : FreeM P α) (n : Nat) :
    PathAlong l spec → PathAlong l (FreeM.replicate a spec n) →
    PathAlong l (FreeM.replicate a spec (n + 1)) :=
  PFunctor.FreeM.PathAlong.append l spec (fun _ => FreeM.replicate a spec n)

/-- Split the head round from a length-`(n+1)` replicated path. -/
abbrev PathAlong.replicateUncons (l : Lens P Q) (a : α) (spec : FreeM P α) (n : Nat) :
    PathAlong l (FreeM.replicate a spec (n + 1)) →
    PathAlong l spec × PathAlong l (FreeM.replicate a spec n) :=
  fun tr =>
    let ⟨hd, tl⟩ := PFunctor.FreeM.PathAlong.split l spec (fun _ => FreeM.replicate a spec n) tr
    (hd, tl)

/-- Combine `n` paths of `spec` into one of `FreeM.replicate a spec n`. -/
def PathAlong.replicateJoin (l : Lens P Q) (a : α) (spec : FreeM P α) :
    (n : Nat) → (Fin n → PathAlong l spec) → PathAlong l (FreeM.replicate a spec n)
  | 0, _ => ⟨⟩
  | n + 1, trs =>
      PFunctor.FreeM.PathAlong.append l spec (fun _ => FreeM.replicate a spec n)
        (trs 0) (PathAlong.replicateJoin l a spec n (fun i => trs i.succ))

/-- Split `FreeM.replicate a spec n` into `n` per-round paths. -/
def PathAlong.replicateSplit (l : Lens P Q) (a : α) (spec : FreeM P α) :
    (n : Nat) → PathAlong l (FreeM.replicate a spec n) → (Fin n → PathAlong l spec)
  | 0, _ => fun i => i.elim0
  | n + 1, tr => fun i =>
      let ⟨hd, tl⟩ := PFunctor.FreeM.PathAlong.split l spec (fun _ => FreeM.replicate a spec n) tr
      match i with
        | ⟨0, _⟩ => hd
        | ⟨i + 1, h⟩ => PathAlong.replicateSplit l a spec n tl ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[simp, grind =]
theorem PathAlong.replicateSplit_replicateJoin (l : Lens P Q) (a : α) (spec : FreeM P α) :
    (n : Nat) → (trs : Fin n → PathAlong l spec) → (i : Fin n) →
    PathAlong.replicateSplit l a spec n (PathAlong.replicateJoin l a spec n trs) i = trs i
  | 0, _, i => i.elim0
  | n + 1, trs, ⟨0, _⟩ => by
      simp [replicateSplit, replicateJoin, PFunctor.FreeM.PathAlong.split_append]
  | n + 1, trs, ⟨i + 1, h⟩ => by
      simp only [replicateSplit, replicateJoin, PFunctor.FreeM.PathAlong.split_append]
      exact replicateSplit_replicateJoin l a spec n (fun i => trs i.succ)
        ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem PathAlong.replicateSplit_join_zero (l : Lens P Q) (a : α) (spec : FreeM P α) (n : Nat)
    (hd : PathAlong l spec) (tl : PathAlong l (FreeM.replicate a spec n)) :
    PathAlong.replicateSplit l a spec (n + 1)
        (PFunctor.FreeM.PathAlong.append l spec (fun _ => FreeM.replicate a spec n) hd tl)
        ⟨0, n.succ_pos⟩ =
      hd := by
  simp [replicateSplit, PFunctor.FreeM.PathAlong.split_append]

theorem PathAlong.replicateSplit_join_succ (l : Lens P Q) (a : α) (spec : FreeM P α) (n : Nat)
    (hd : PathAlong l spec) (tl : PathAlong l (FreeM.replicate a spec n)) (i : Fin n) :
    PathAlong.replicateSplit l a spec (n + 1)
        (PFunctor.FreeM.PathAlong.append l spec (fun _ => FreeM.replicate a spec n) hd tl) i.succ =
      PathAlong.replicateSplit l a spec n tl i := by
  simp [replicateSplit, PFunctor.FreeM.PathAlong.split_append, Fin.succ]

@[simp, grind =]
theorem PathAlong.replicateJoin_replicateSplit (l : Lens P Q) (a : α) (spec : FreeM P α) (n : Nat)
    (tr : PathAlong l (FreeM.replicate a spec n)) :
    PathAlong.replicateJoin l a spec n (PathAlong.replicateSplit l a spec n tr) = tr := by
  induction n with
  | zero => cases tr; rfl
  | succ n ih =>
    let hd := (PFunctor.FreeM.PathAlong.split l spec (fun _ => FreeM.replicate a spec n) tr).1
    let tl := (PFunctor.FreeM.PathAlong.split l spec (fun _ => FreeM.replicate a spec n) tr).2
    have htr :
        tr = PFunctor.FreeM.PathAlong.append l spec (fun _ => FreeM.replicate a spec n) hd tl :=
      (PFunctor.FreeM.PathAlong.append_split l spec (fun _ => FreeM.replicate a spec n) tr).symm
    rw [htr, replicateJoin]
    congr 1
    · simpa using replicateSplit_join_zero l a spec n hd tl
    · have hfns :
          (fun i => PathAlong.replicateSplit l a spec (n + 1)
              (PathAlong.append l spec (fun _ => FreeM.replicate a spec n) hd tl) i.succ) =
            PathAlong.replicateSplit l a spec n tl := by
        funext i
        exact replicateSplit_join_succ l a spec n hd tl i
      rw [hfns, ih]


/-- Splitting a cons recovers both rounds. -/
theorem PathAlong.replicateUncons_replicateCons (l : Lens P Q) (a : α)
    (s : FreeM P α) (n : Nat) (hd : PathAlong l s)
    (tl : PathAlong l (FreeM.replicate a s n)) :
    PathAlong.replicateUncons l a s n (PathAlong.replicateCons l a s n hd tl) = (hd, tl) := by
  simp [PathAlong.replicateUncons, PathAlong.replicateCons, PathAlong.split_append]

/-- Joining the head and tail recovers a replicated transcript. -/
@[simp] theorem PathAlong.replicateCons_replicateUncons (l : Lens P Q) (a : α)
    (s : FreeM P α) (n : Nat) (tr : PathAlong l (FreeM.replicate a s (n + 1))) :
    PathAlong.replicateCons l a s n (PathAlong.replicateUncons l a s n tr).1
      (PathAlong.replicateUncons l a s n tr).2 = tr :=
  PathAlong.append_split l s (fun _ => FreeM.replicate a s n) tr

/-- The empty vector produces the empty transcript. -/
@[simp] theorem PathAlong.replicateJoin_zero (l : Lens P Q) (a : α)
    (s : FreeM P α) (trs : Fin 0 → PathAlong l s) :
    PathAlong.replicateJoin l a s 0 trs = PUnit.unit := rfl

/-- Join prepends the first round and recursively joins the remaining rounds. -/
theorem PathAlong.replicateJoin_succ (l : Lens P Q) (a : α)
    (s : FreeM P α) (n : Nat) (trs : Fin (n + 1) → PathAlong l s) :
    PathAlong.replicateJoin l a s (n + 1) trs =
      PathAlong.replicateCons l a s n (trs 0)
        (PathAlong.replicateJoin l a s n (fun i => trs i.succ)) := rfl

/-- A zero-round split has no coordinates. -/
@[simp] theorem PathAlong.replicateSplit_zero (l : Lens P Q) (a : α)
    (s : FreeM P α) (tr : PathAlong l (FreeM.replicate a s 0)) :
    PathAlong.replicateSplit l a s 0 tr = Fin.elim0 := rfl

/-- Splitting another round separates its head coordinate from the tail coordinates. -/
theorem PathAlong.replicateSplit_succ (l : Lens P Q) (a : α)
    (s : FreeM P α) (n : Nat) (tr : PathAlong l (FreeM.replicate a s (n + 1))) :
    PathAlong.replicateSplit l a s (n + 1) tr =
      Fin.cases (PathAlong.replicateUncons l a s n tr).1
        (PathAlong.replicateSplit l a s n (PathAlong.replicateUncons l a s n tr).2) := by
  funext i
  cases i using Fin.cases <;> rfl

end PFunctor.FreeM
