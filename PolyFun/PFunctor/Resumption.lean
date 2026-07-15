/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.M

/-!
# Coinductive resumptions over polynomial interfaces

A `Resumption p β` is a possibly infinite, tau-free computation that either
returns a value in `β` or exposes a visible query from `p` and continues from
the selected direction. It is the M-type of the return-or-query polynomial
`C β + p`, the coinductive counterpart of `FreeM p β`.

The named `map` and `bind` operations are maximally universe-polymorphic in
their source and target result types. The `Monad` and `LawfulMonad` instances
cover the ordinary specialization in which those result types live in one
chosen universe.
-/

@[expose] public section

universe uA uB uα uβ uγ uX uY

namespace PFunctor

/-- A possibly infinite, tau-free computation that returns a `β` or performs a
visible query from `p`. -/
abbrev Resumption (p : PFunctor.{uA, uB}) (β : Type uβ) :=
  M.{max uβ uA, uB} (C.{uβ, uB} β + p)

namespace Resumption

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {γ : Type uγ}

/-! ## One-step views -/

/-- Reassociate the extension of `C β + p` into the computational
return-or-query view. -/
def unpack {X : Type uX} : (C.{uβ, uB} β + p).Obj X → β ⊕ p.Obj X
  | ⟨Sum.inl value, _⟩ => Sum.inl value
  | ⟨Sum.inr position, next⟩ => Sum.inr ⟨position, next⟩

/-- Repack a computational return-or-query view as an extension of `C β + p`. -/
def pack {X : Type uX} : β ⊕ p.Obj X → (C.{uβ, uB} β + p).Obj X
  | Sum.inl value => ⟨Sum.inl value, PEmpty.elim⟩
  | Sum.inr ⟨position, next⟩ => ⟨Sum.inr position, next⟩

@[simp] theorem pack_inl {X : Type uX} (value : β) :
    pack (p := p) (X := X) (Sum.inl value) = ⟨Sum.inl value, PEmpty.elim⟩ := rfl

@[simp] theorem pack_inr {X : Type uX} (position : p.A) (next : p.B position → X) :
    pack (Sum.inr ⟨position, next⟩ : β ⊕ p.Obj X) = ⟨Sum.inr position, next⟩ := rfl

@[simp] theorem unpack_pack {X : Type uX} (step : β ⊕ p.Obj X) :
    unpack (pack step) = step := by
  cases step with
  | inl _ => rfl
  | inr step => rcases step with ⟨_, _⟩; rfl

@[simp] theorem pack_unpack {X : Type uX} (step : (C.{uβ, uB} β + p).Obj X) :
    pack (unpack step) = step := by
  rcases step with ⟨shape, next⟩
  cases shape with
  | inl value =>
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext direction
        exact PEmpty.elim direction
  | inr position => rfl

/-- The extension of `C β + p` is equivalent to the computational
return-or-query view. -/
def viewEquiv {X : Type uX} : (C.{uβ, uB} β + p).Obj X ≃ β ⊕ p.Obj X where
  toFun := unpack
  invFun := pack
  left_inv := pack_unpack
  right_inv := unpack_pack

@[simp] theorem unpack_map {X : Type uX} {Y : Type uY} (f : X → Y)
    (step : (C.{uβ, uB} β + p).Obj X) :
    unpack ((C.{uβ, uB} β + p).map f step) =
      Sum.map (fun value : β => value) (p.map f) (unpack step) := by
  rcases step with ⟨shape, next⟩
  cases shape <;> rfl

/-! ## Constructors, destructor, and corecursor -/

/-- A resumption that immediately returns `value`. -/
def pure (value : β) : Resumption p β :=
  M.mk (pack (Sum.inl value))

/-- A resumption that exposes `position` and continues according to the
selected direction. -/
def query (position : p.A) (next : p.B position → Resumption p β) : Resumption p β :=
  M.mk (pack (Sum.inr ⟨position, next⟩))

/-- Observe whether a resumption returns or performs a visible query. -/
def dest (computation : Resumption p β) : β ⊕ p.Obj (Resumption p β) :=
  unpack (M.dest computation)

@[simp] theorem pack_dest (computation : Resumption p β) :
    pack (dest computation) = M.dest computation :=
  pack_unpack _

/-- The computational destructor is injective, just as the underlying
M-type destructor is. -/
theorem eq_of_dest_eq {left right : Resumption p β} (h : dest left = dest right) :
    left = right := by
  apply M.eq_of_dest_eq
  rw [← pack_dest left, ← pack_dest right, h]

@[simp] theorem dest_inj {left right : Resumption p β} :
    dest left = dest right ↔ left = right :=
  ⟨eq_of_dest_eq, fun h => h ▸ rfl⟩

/-- Build a resumption from a return-or-query coalgebra. -/
def corec {X : Type uX} (step : X → β ⊕ p.Obj X) (seed : X) : Resumption p β :=
  M.corec (fun state => pack (step state)) seed

@[simp] theorem dest_pure (value : β) : dest (pure (p := p) value) = Sum.inl value := by
  simp only [dest, pure, M.dest_mk, unpack_pack]

@[simp] theorem dest_query (position : p.A) (next : p.B position → Resumption p β) :
    dest (query position next) = Sum.inr ⟨position, next⟩ := by
  simp only [dest, query, M.dest_mk, unpack_pack]

@[simp] theorem dest_corec {X : Type uX} (step : X → β ⊕ p.Obj X) (seed : X) :
    dest (corec step seed) =
      Sum.map (fun value : β => value) (p.map (corec step)) (step seed) := by
  unfold dest corec
  rw [M.dest_corec, unpack_map, unpack_pack]

/-- Corecursing from the destructor reconstructs the original resumption. -/
@[simp] theorem corec_dest (computation : Resumption p β) :
    corec dest computation = computation := by
  unfold corec
  have hstep : (fun state : Resumption p β => pack (dest state)) = M.dest := by
    funext state
    exact pack_dest state
  rw [hstep]
  exact M.corec_dest computation

/-! ## Functorial and monadic structure -/

/-- Lift one visible query, returning the selected direction. -/
def lift (position : p.A) : Resumption p (p.B position) :=
  query position pure

@[simp] theorem dest_lift (position : p.A) :
    dest (lift position) = Sum.inr ⟨position, pure⟩ := by
  simp [lift]

/-- Step coalgebra used by `bind`. The right summand records that execution has
entered the continuation selected by a returned source value. -/
def bindStep (k : α → Resumption p β) :
    Resumption p α ⊕ Resumption p β →
      β ⊕ p.Obj (Resumption p α ⊕ Resumption p β)
  | Sum.inl computation =>
      match dest computation with
      | Sum.inl value =>
          match dest (k value) with
          | Sum.inl result => Sum.inl result
          | Sum.inr ⟨position, next⟩ =>
              Sum.inr ⟨position, fun direction => Sum.inr (next direction)⟩
      | Sum.inr ⟨position, next⟩ =>
          Sum.inr ⟨position, fun direction => Sum.inl (next direction)⟩
  | Sum.inr computation =>
      match dest computation with
      | Sum.inl result => Sum.inl result
      | Sum.inr ⟨position, next⟩ =>
          Sum.inr ⟨position, fun direction => Sum.inr (next direction)⟩

/-- Monadic bind on resumptions. Named bind permits source and target result
types in different universes. -/
def bind (computation : Resumption p α) (k : α → Resumption p β) : Resumption p β :=
  corec (bindStep k) (Sum.inl computation)

/-- Map a function over the returned value of a resumption. Named map permits
source and target result types in different universes. -/
def map (f : α → β) (computation : Resumption p α) : Resumption p β :=
  bind computation (fun value => pure (f value))

private theorem corec_bindStep_inr (k : α → Resumption p β)
    (computation : Resumption p β) :
    corec (bindStep k) (Sum.inr computation) = computation := by
  refine M.bisim
    (fun left right => left = corec (bindStep k) (Sum.inr right)) ?_ _ _ rfl
  rintro left right rfl
  rcases h : dest right with result | ⟨position, next⟩
  · refine ⟨Sum.inl result, PEmpty.elim, PEmpty.elim, ?_, ?_, fun direction => ?_⟩
    · rw [← pack_dest, ← pack_inl]
      apply congrArg pack
      simp only [dest_corec, bindStep, h, Sum.map_inl]
    · rw [← pack_dest, ← pack_inl]
      exact congrArg pack h
    · exact PEmpty.elim direction
  · refine ⟨Sum.inr position,
      fun direction => corec (bindStep k) (Sum.inr (next direction)),
      next, ?_, ?_, fun direction => rfl⟩
    · rw [← pack_dest, ← pack_inr]
      apply congrArg pack
      simp only [dest_corec, bindStep, h, Sum.map_inr, PFunctor.map_eq]
      rfl
    · rw [← pack_dest, ← pack_inr]
      exact congrArg pack h

@[simp] theorem dest_bind (computation : Resumption p α) (k : α → Resumption p β) :
    dest (bind computation k) =
      match dest computation with
      | Sum.inl value => dest (k value)
      | Sum.inr ⟨position, next⟩ =>
          Sum.inr ⟨position, fun direction => bind (next direction) k⟩ := by
  unfold bind
  rw [dest_corec]
  rcases h : dest computation with value | ⟨position, next⟩
  · rcases hk : dest (k value) with result | ⟨position, next⟩
    · simp [bindStep, h, hk]
    · simp only [bindStep, h, hk, Sum.map_inr, PFunctor.map_eq]
      apply congrArg Sum.inr
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext direction
        exact corec_bindStep_inr k (next direction)
  · simp only [bindStep, h, Sum.map_inr, PFunctor.map_eq]
    rfl

@[simp] theorem bind_pure_left (value : α) (k : α → Resumption p β) :
    bind (pure value) k = k value := by
  apply eq_of_dest_eq
  simp

@[simp] theorem bind_query (position : p.A) (next : p.B position → Resumption p α)
    (k : α → Resumption p β) :
    bind (query position next) k = query position (fun direction => bind (next direction) k) := by
  apply eq_of_dest_eq
  simp

@[simp] theorem bind_pure_right (computation : Resumption p α) :
    bind computation pure = computation := by
  refine M.bisim
    (fun (left right : Resumption p α) =>
      ∃ source : Resumption p α, left = bind source pure ∧ right = source) ?_
    _ _ ⟨computation, rfl, rfl⟩
  rintro left right ⟨source, hleft, hright⟩
  rw [hleft, hright]
  rcases h : dest source with value | ⟨position, next⟩
  · refine ⟨Sum.inl value, PEmpty.elim, PEmpty.elim, ?_, ?_, fun direction => ?_⟩
    · rw [← pack_dest, ← pack_inl]
      apply congrArg pack
      simp [dest_bind, h]
    · rw [← pack_dest, ← pack_inl]
      exact congrArg pack h
    · exact PEmpty.elim direction
  · refine ⟨Sum.inr position, (fun direction => bind (next direction) pure), next,
      ?_, ?_, fun direction => ⟨next direction, rfl, rfl⟩⟩
    · rw [← pack_dest, ← pack_inr]
      apply congrArg pack
      simp [dest_bind, h]
      rfl
    · rw [← pack_dest, ← pack_inr]
      exact congrArg pack h

theorem bind_assoc (computation : Resumption p α) (k : α → Resumption p β)
    (k' : β → Resumption p γ) :
    bind (bind computation k) k' = bind computation (fun value => bind (k value) k') := by
  refine M.bisim
    (fun (left right : Resumption p γ) => left = right ∨ ∃ source : Resumption p α,
      left = bind (bind source k) k' ∧
      right = bind source (fun value => bind (k value) k')) ?_
    _ _ (Or.inr ⟨computation, rfl, rfl⟩)
  rintro left right hrel
  rcases hrel with hEq | ⟨source, hleft, hright⟩
  · subst left
    rcases h : M.dest right with ⟨shape, next⟩
    exact ⟨shape, next, next, rfl, rfl, fun _ => Or.inl rfl⟩
  · rw [hleft, hright]
    rcases h : dest source with value | ⟨position, next⟩
    · rw [show source = pure value by
        apply eq_of_dest_eq
        simpa using h]
      simp only [bind_pure_left]
      rcases hk : M.dest (bind (k value) k') with ⟨shape, next⟩
      exact ⟨shape, next, next, rfl, rfl, fun _ => Or.inl rfl⟩
    · refine ⟨Sum.inr position,
        fun direction => bind (bind (next direction) k) k',
        fun direction => bind (next direction) (fun value => bind (k value) k'),
        ?_, ?_, fun direction => Or.inr ⟨next direction, rfl, rfl⟩⟩
      · rw [← pack_dest, ← pack_inr]
        apply congrArg pack
        simp [dest_bind, h]
        rfl
      · rw [← pack_dest, ← pack_inr]
        apply congrArg pack
        simp [dest_bind, h]
        rfl

@[simp] theorem map_pure (f : α → β) (value : α) :
    map f (pure (p := p) value) = pure (f value) := by
  simp [map]

@[simp] theorem map_query (f : α → β) (position : p.A)
    (next : p.B position → Resumption p α) :
    map f (query position next) = query position (fun direction => map f (next direction)) := by
  simp [map]

@[simp] theorem map_id (computation : Resumption p α) :
    map id computation = computation := by
  change bind computation pure = computation
  exact bind_pure_right computation

theorem map_comp (g : β → γ) (f : α → β) (computation : Resumption p α) :
    map (g ∘ f) computation = map g (map f computation) := by
  rw [map, map, map, bind_assoc]
  simp

section Instances

universe u

variable {p : PFunctor.{uA, uB}} {α β γ : Type u}

instance instMonad : Monad (Resumption p) where
  pure := pure
  bind := bind

@[simp] theorem map_eq_functor_map (f : α → β) (computation : Resumption p α) :
    f <$> computation = map f computation := rfl

instance instLawfulMonad : LawfulMonad (Resumption p) := LawfulMonad.mk'
  (bind_pure_comp := by intros; rfl)
  (id_map := map_id)
  (pure_bind := bind_pure_left)
  (bind_assoc := bind_assoc)

end Instances

end Resumption

end PFunctor
