/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Transport
public import PolyFun.IPFunctor.Free.Traversal

/-!
# Binding signatures over changing parameter contexts

Each child can enter a different parameter context, reindex the types of existing
variables, and bind new value variables. The resulting well-founded syntax is an
indexed free polynomial tree, and each term is finite when every constructor has
finitely many arguments. Ordinary binding signatures are the constant-context case.

`ScopedFamily.Ambient` records how a child sees the ambient value context. A child that
stays in its parent's parameter context can `keep` that context, so its ambient variables
keep their sorts definitionally. A child that changes parameter context moves every ambient
sort along a `map`. Lookup always follows binding positions, so the map need not be
injective.
-/

public section

universe u v w z

namespace IPFunctor

/-- How a constructor argument sees the ambient value context: unchanged, in the parent's
parameter context, or with every sort moved along a map into the argument's parameter
context. -/
inductive ScopedFamily.Ambient {W : Type u} (S : W → Type v) : W → W → Type (max u v) where
  /-- The argument stays in the parent's parameter context and keeps the ambient context. -/
  | keep {w : W} : Ambient S w w
  /-- The argument moves every ambient sort along a map of sorts. -/
  | map {w w' : W} (f : S w → S w') : Ambient S w w'

namespace ScopedFamily.Ambient

variable {W : Type u} {S : W → Type v}

/-- The map of sorts: the identity for `keep`. -/
@[expose] def sort : {w w' : W} → Ambient S w w' → S w → S w'
  | _, _, .keep => fun a => a
  | _, _, .map f => f

/-- The ambient context of the argument: unchanged for `keep`, mapped for `map`. -/
@[expose] def context : {w w' : W} → Ambient S w w' → List (S w) → List (S w')
  | _, _, .keep, Γ => Γ
  | _, _, .map f, Γ => Γ.map f

@[simp] theorem sort_keep {w : W} (a : S w) : (keep : Ambient S w w).sort a = a := rfl

@[simp] theorem sort_map {w w' : W} (f : S w → S w') (a : S w) : (map f).sort a = f a := rfl

@[simp] theorem context_keep {w : W} (Γ : List (S w)) : (keep : Ambient S w w).context Γ = Γ :=
  rfl

@[simp] theorem context_map {w w' : W} (f : S w → S w') (Γ : List (S w)) :
    (map f).context Γ = Γ.map f := rfl

/-- Every ambient context is the positional image of the original one. -/
theorem context_eq_map {w w' : W} (c : Ambient S w w') (Γ : List (S w)) :
    c.context Γ = Γ.map c.sort := by
  cases c
  · exact (List.map_id' Γ).symm
  · rfl

@[simp] theorem context_nil {w w' : W} (c : Ambient S w w') : c.context [] = [] := by
  cases c <;> rfl

@[simp] theorem context_cons {w w' : W} (c : Ambient S w w') (a : S w) (Γ : List (S w)) :
    c.context (a :: Γ) = c.sort a :: c.context Γ := by
  cases c <;> rfl

/-- Compatible sort maps give the same ambient context in either order. -/
theorem map_context {w w' z z' : W} (c : Ambient S w w') (c' : Ambient S z z')
    {f : S w → S z} {g : S w' → S z'} (h : ∀ b, g (c.sort b) = c'.sort (f b))
    (Γ : List (S w)) : (c.context Γ).map g = c'.context (Γ.map f) := by
  rw [context_eq_map, context_eq_map, List.map_map, List.map_map]
  exact List.map_congr_left fun b _ => h b

/-- A variable at its original binding position in the argument's ambient context. -/
@[expose] def var : {w w' : W} → (c : Ambient S w w') → {Γ : List (S w)} → {a : S w} →
    ScopedVar Γ a → ScopedVar (c.context Γ) (c.sort a)
  | _, _, .keep, _, _, x => x
  | _, _, .map f, _, _, x => x.map f

@[simp] theorem var_keep {w : W} {Γ : List (S w)} {a : S w} (x : ScopedVar Γ a) :
    (keep : Ambient S w w).var x = x := rfl

@[simp] theorem var_map {w w' : W} (f : S w → S w') {Γ : List (S w)} {a : S w}
    (x : ScopedVar Γ a) : (map f).var x = x.map f := rfl

@[simp] theorem index_var {w w' : W} (c : Ambient S w w') {Γ : List (S w)} {a : S w}
    (x : ScopedVar Γ a) : (c.var x).index = x.index := by
  cases c
  · rfl
  · exact ScopedVar.index_map _ x

/-- Every variable of an ambient context comes from its original binding position. -/
@[elab_as_elim] theorem var_inductionOn {w w' : W} (c : Ambient S w w') {Γ : List (S w)}
    {motive : ∀ b, ScopedVar (c.context Γ) b → Prop}
    (h : ∀ a (x : ScopedVar Γ a), motive (c.sort a) (c.var x))
    {b : S w'} (x : ScopedVar (c.context Γ) b) : motive b x := by
  cases c
  · exact h b x
  · exact ScopedVar.map_inductionOn _ h x

/-- Read the argument's ambient context by original binding positions. -/
@[expose] def env : {w w' : W} → (c : Ambient S w w') → {V : S w' → Type z} →
    {Γ : List (S w)} → ScopedSignature.Env (fun a => V (c.sort a)) Γ →
      ScopedSignature.Env V (c.context Γ)
  | _, _, .keep, _, _, η => η
  | _, _, .map f, _, _, η => ScopedSignature.Env.reindex f η

@[simp] theorem env_keep {w : W} {V : S w → Type z} {Γ : List (S w)}
    (η : ScopedSignature.Env V Γ) : (keep : Ambient S w w).env η = η := rfl

@[simp] theorem env_map {w w' : W} (f : S w → S w') {V : S w' → Type z} {Γ : List (S w)}
    (η : ScopedSignature.Env (fun a => V (f a)) Γ) :
    (map f).env η = ScopedSignature.Env.reindex f η := rfl

/-- Looking up an original binding position retrieves its value. -/
@[simp] theorem env_var {w w' : W} (c : Ambient S w w') {V : S w' → Type z} {Γ : List (S w)}
    (η : ScopedSignature.Env (fun a => V (c.sort a)) Γ) {a : S w} (x : ScopedVar Γ a) :
    c.env η (c.sort a) (c.var x) = η a x := by
  cases c
  · rfl
  · exact ScopedSignature.Env.reindex_map _ _ x

/-- Move both contexts of a renaming into the argument, keeping binding positions. The name
avoids `renaming`, which is a Lean keyword. -/
@[expose] def mapRenaming {w w' : W} (c : Ambient S w w') {Γ Δ : List (S w)}
    (ρ : ScopedSignature.Renaming Γ Δ) :
    ScopedSignature.Renaming (c.context Γ) (c.context Δ) :=
  c.env fun a x => c.var (ρ a x)

@[simp] theorem mapRenaming_keep {w : W} {Γ Δ : List (S w)} (ρ : ScopedSignature.Renaming Γ Δ) :
    (keep : Ambient S w w).mapRenaming ρ = ρ := rfl

@[simp] theorem mapRenaming_map {w w' : W} (f : S w → S w') {Γ Δ : List (S w)}
    (ρ : ScopedSignature.Renaming Γ Δ) :
    (map f).mapRenaming ρ = ScopedSignature.Renaming.map f ρ := rfl

@[simp] theorem mapRenaming_var {w w' : W} (c : Ambient S w w') {Γ Δ : List (S w)}
    (ρ : ScopedSignature.Renaming Γ Δ) {a : S w} (x : ScopedVar Γ a) :
    c.mapRenaming ρ (c.sort a) (c.var x) = c.var (ρ a x) :=
  env_var c _ x

@[simp] theorem mapRenaming_id {w w' : W} (c : Ambient S w w') {Γ : List (S w)} :
    c.mapRenaming (fun _ x => x : ScopedSignature.Renaming Γ Γ) = fun _ x => x := by
  cases c
  · rfl
  · exact ScopedSignature.Renaming.map_id _

/-- Moving a composite renaming moves both renamings. -/
theorem mapRenaming_comp {w w' : W} (c : Ambient S w w') {Γ Δ Θ : List (S w)}
    (ρ : ScopedSignature.Renaming Γ Δ) (τ : ScopedSignature.Renaming Δ Θ) :
    c.mapRenaming (ScopedSignature.Env.rename ρ τ) =
      ScopedSignature.Env.rename (c.mapRenaming ρ) (c.mapRenaming τ) := by
  cases c
  · rfl
  · exact ScopedSignature.Renaming.map_comp _ ρ τ

/-- Reading through a renaming commutes with moving into the argument. -/
theorem env_rename {w w' : W} (c : Ambient S w w') {V : S w' → Type z} {Γ Δ : List (S w)}
    (ρ : ScopedSignature.Renaming Γ Δ) (η : ScopedSignature.Env (fun a => V (c.sort a)) Δ) :
    c.env (ScopedSignature.Env.rename ρ η) =
      ScopedSignature.Env.rename (c.mapRenaming ρ) (c.env η) := by
  cases c
  · rfl
  · exact ScopedSignature.Env.reindex_rename _ ρ η

/-- A renaming moved into the argument and then along a compatible sort map agrees, up to
its two contexts, with the renaming moved along the sort map and then into the target. -/
theorem map_mapRenaming_heq {w w' z z' : W} (c : Ambient S w w') (c' : Ambient S z z')
    {f : S w → S z} {g : S w' → S z'} (h : ∀ b, g (c.sort b) = c'.sort (f b))
    {Γ Δ : List (S w)} (ρ : ScopedSignature.Renaming Γ Δ) :
    HEq (ScopedSignature.Renaming.map g (c.mapRenaming ρ))
      (c'.mapRenaming (ScopedSignature.Renaming.map f ρ)) := by
  apply ScopedSignature.Renaming.heq_of_index (map_context c c' h Γ) (map_context c c' h Δ)
  intro a b x y hxy
  induction x using ScopedVar.map_inductionOn g with
  | h a x =>
    induction x using var_inductionOn c with
    | h a x =>
      induction y using var_inductionOn c' with
      | h b y =>
        induction y using ScopedVar.map_inductionOn f with
        | h b y =>
          simp only [ScopedSignature.Renaming.map_apply, mapRenaming_var, ScopedVar.index_map,
            index_var] at hxy ⊢
          cases ScopedVar.sigma_eq_of_index_eq x y hxy
          rfl

end ScopedFamily.Ambient

/-- Constructor arguments may change the parameter context and extend the value scope. -/
structure ScopedFamily (W : Type u) (S : W → Type v) where
  /-- Constructor heads at a parameter context and result sort. -/
  Op : (w : W) → S w → Type w
  /-- Recursive argument positions. -/
  Arg : {w : W} → {a : S w} → Op w a → Type z
  /-- The parameter context of an argument. -/
  world : {w : W} → {a : S w} → (op : Op w a) → Arg op → W
  /-- How the argument sees the ambient value context. -/
  ambient : {w : W} → {a : S w} → (op : Op w a) → (p : Arg op) →
    ScopedFamily.Ambient S w (world op p)
  /-- Additional value variables, nearest first. -/
  binders : {w : W} → {a : S w} → (op : Op w a) → (p : Arg op) → List (S (world op p))
  /-- The argument's result sort. -/
  sort : {w : W} → {a : S w} → (op : Op w a) → (p : Arg op) → S (world op p)

namespace ScopedFamily

variable {W : Type u} {S : W → Type v}

/-- The sort of an ambient variable in an argument's parameter context. -/
abbrev reindex (σ : ScopedFamily.{u, v, w, z} W S) {w : W} {a : S w} (op : σ.Op w a)
    (p : σ.Arg op) : S w → S (σ.world op p) :=
  (σ.ambient op p).sort

/-- Parameter context, value context, and result sort. -/
abbrev Judgment (S : W → Type v) := (w : W) × List (S w) × S w

/-- The polynomial associated with a context-changing binding signature. -/
@[expose, reducible] def polynomial (σ : ScopedFamily.{u, v, w, z} W S) :
    Endo (Judgment S) where
  A j := σ.Op j.1 j.2.2
  B _ op := σ.Arg op
  src j op p := ⟨σ.world op p,
    σ.binders op p ++ (σ.ambient op p).context j.2.1, σ.sort op p⟩

/-- Well-founded syntax with typed variables at the leaves. -/
abbrev Term (σ : ScopedFamily.{u, v, w, z} W S) (w : W) (Γ : List (S w)) (a : S w) :=
  IFreeM σ.polynomial (fun j => ScopedVar j.2.1 j.2.2) ⟨w, Γ, a⟩

namespace Term

variable {σ : ScopedFamily.{u, v, w, z} W S}

/-- A variable occurrence in its parameter and value contexts. -/
@[expose, match_pattern] def var {w : W} {Γ : List (S w)} {a : S w}
    (x : ScopedVar Γ a) : σ.Term w Γ a := .pure x

/-- A constructor whose children enter their prescribed contexts. -/
@[expose, match_pattern] def node {w : W} {Γ : List (S w)} {a : S w} (op : σ.Op w a)
    (args : (p : σ.Arg op) → σ.Term (σ.world op p)
      (σ.binders op p ++ (σ.ambient op p).context Γ) (σ.sort op p)) : σ.Term w Γ a :=
  .liftBind op args

/-- Structural induction, retaining the changing parameter context in the motive. -/
@[elab_as_elim] protected theorem inductionOn
    {C : ∀ w Γ a, σ.Term w Γ a → Prop}
    (hvar : ∀ w Γ a (x : ScopedVar Γ a), C w Γ a (var x))
    (hnode : ∀ w Γ a (op : σ.Op w a)
      (args : (p : σ.Arg op) → σ.Term (σ.world op p)
        (σ.binders op p ++ (σ.ambient op p).context Γ) (σ.sort op p)),
      (∀ p, C _ _ _ (args p)) → C w Γ a (node op args))
    {w : W} {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a) : C w Γ a t :=
  IFreeM.inductionOn (C := fun j t => C j.1 j.2.1 j.2.2 t)
    (fun j => hvar j.1 j.2.1 j.2.2) (fun j => hnode j.1 j.2.1 j.2.2) t

/-- Renaming follows value binders and moves old variable positions into each argument. -/
@[expose] def rename {w : W} {Γ Δ : List (S w)} {a : S w}
    (ρ : ScopedSignature.Renaming Γ Δ) (t : σ.Term w Γ a) : σ.Term w Δ a :=
  t.fold (D := fun j => ∀ Δ : List (S j.1),
      ScopedSignature.Renaming j.2.1 Δ → σ.Term j.1 Δ j.2.2)
    (fun _ x _ ρ => .pure (ρ _ x))
    (fun _ op next _ ρ => .liftBind op (fun p => next p _
      (ScopedSignature.Renaming.liftMany ((σ.ambient op p).mapRenaming ρ) (σ.binders op p)))) Δ ρ

@[simp] theorem rename_var {w : W} {Γ Δ : List (S w)} {a : S w}
    (ρ : ScopedSignature.Renaming Γ Δ) (x : ScopedVar Γ a) :
    (var (σ := σ) x).rename ρ = var (ρ a x) := rfl

@[simp] theorem rename_node {w : W} {Γ Δ : List (S w)} {a : S w}
    (ρ : ScopedSignature.Renaming Γ Δ) (op : σ.Op w a)
    (args : (p : σ.Arg op) → σ.Term (σ.world op p)
      (σ.binders op p ++ (σ.ambient op p).context Γ) (σ.sort op p)) :
    (node op args).rename ρ = node op (fun p => (args p).rename
      (ScopedSignature.Renaming.liftMany ((σ.ambient op p).mapRenaming ρ) (σ.binders op p))) := rfl

/-- Identity renaming remains identity under parameter-context changes. -/
@[simp] theorem rename_id {w : W} {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a) :
    t.rename (fun _ x => x) = t := by
  induction t using Term.inductionOn with
  | hvar w Γ a x => rfl
  | hnode w Γ a op args ih =>
      simp only [rename_node, Ambient.mapRenaming_id]
      congr 1
      funext p
      have h : (ScopedSignature.Renaming.liftMany
          (Γ := (σ.ambient op p).context Γ) (fun _ x => x) (σ.binders op p) :
          ScopedSignature.Renaming _ _) = fun _ x => x := by
        funext a x
        exact ScopedSignature.Renaming.liftMany_id _ x
      rw [h]
      exact ih p

/-- Renaming composition commutes with every parameter and value binder. -/
theorem rename_rename {w : W} {Γ Δ Θ : List (S w)} {a : S w} (t : σ.Term w Γ a)
    (ρ : ScopedSignature.Renaming Γ Δ) (τ : ScopedSignature.Renaming Δ Θ) :
    (t.rename ρ).rename τ = t.rename (ScopedSignature.Env.rename ρ τ) := by
  induction t using Term.inductionOn with
  | hvar w Γ a x => rfl
  | hnode w Γ a op args ih =>
      simp only [rename_node]
      congr 1
      funext p
      rw [ih p]
      congr 1
      funext a x
      rw [Ambient.mapRenaming_comp (σ.ambient op p) ρ τ]
      exact (ScopedSignature.Renaming.liftMany_comp _ _ _ x).symm

end Term
end ScopedFamily
end IPFunctor
