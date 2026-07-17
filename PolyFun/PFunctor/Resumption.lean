/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic
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

universe uA uB uA₂ uB₂ uA₃ uB₃ uα uβ uγ uX uY

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

theorem pack_sum_map {X : Type uX} {Y : Type uY} (f : X → Y)
    (step : β ⊕ p.Obj X) :
    pack (Sum.map (fun value : β => value) (p.map f) step) =
      (C.{uβ, uB} β + p).map f (pack step) := by
  rcases step with value | ⟨position, next⟩
  · apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext direction
      exact PEmpty.elim direction
  · rfl

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

/-! ## Coinduction and finality -/

/-- Two resumptions have matching computational heads with respect to `R`
when they return the same value, or expose the same query position and have
pointwise `R`-related continuations. -/
inductive HeadMatch (R : Resumption p β → Resumption p β → Prop) :
    Resumption p β → Resumption p β → Prop where
  | pure {left right : Resumption p β} (value : β)
      (left_dest : dest left = Sum.inl value)
      (right_dest : dest right = Sum.inl value) :
      HeadMatch R left right
  | query {left right : Resumption p β} (position : p.A)
      (left_next right_next : p.B position → Resumption p β)
      (left_dest : dest left = Sum.inr ⟨position, left_next⟩)
      (right_dest : dest right = Sum.inr ⟨position, right_next⟩)
      (next_rel : ∀ direction, R (left_next direction) (right_next direction)) :
      HeadMatch R left right

/-- Strengthen the relation used below a matching pair of resumption heads. -/
theorem HeadMatch.mono {R S : Resumption p β → Resumption p β → Prop}
    (hRS : ∀ {left right}, R left right → S left right)
    {left right : Resumption p β} (h : HeadMatch R left right) :
    HeadMatch S left right := by
  cases h with
  | pure value left_dest right_dest =>
      exact .pure value left_dest right_dest
  | query position left_next right_next left_dest right_dest next_rel =>
      exact .query position left_next right_next left_dest right_dest
        (fun direction => hRS (next_rel direction))

/-- Computational-view bisimulation principle for resumptions. Clients need
not expose the implementation polynomial `C β + p` or use raw `M.bisim`. -/
theorem bisim (R : Resumption p β → Resumption p β → Prop)
    (step : ∀ left right, R left right → HeadMatch R left right)
    {left right : Resumption p β} (h : R left right) : left = right := by
  refine M.bisim R ?_ left right h
  intro currentLeft currentRight hrel
  cases step currentLeft currentRight hrel with
  | pure value left_dest right_dest =>
      refine ⟨Sum.inl value, PEmpty.elim, PEmpty.elim, ?_, ?_, fun direction => ?_⟩
      · rw [← pack_dest, left_dest, pack_inl]
      · rw [← pack_dest, right_dest, pack_inl]
      · exact PEmpty.elim direction
  | query position left_next right_next left_dest right_dest next_rel =>
      refine ⟨Sum.inr position, left_next, right_next, ?_, ?_, next_rel⟩
      · rw [← pack_dest, left_dest, pack_inr]
      · rw [← pack_dest, right_dest, pack_inr]

/-- Finality of `Resumption`: a function satisfying the computational
coalgebra equation is the computational corecursor. -/
theorem corec_unique {X : Type uX} (step : X → β ⊕ p.Obj X)
    (f : X → Resumption p β)
    (hf : ∀ state, dest (f state) =
      Sum.map (fun value : β => value) (p.map f) (step state)) :
    f = corec step := by
  unfold corec
  apply M.corec_unique (fun state => pack (step state)) f
  intro state
  rw [← pack_dest, hf]
  exact pack_sum_map f (step state)

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

/-! ## Interface transport -/

section MapLens

variable {q : PFunctor.{uA₂, uB₂}} {r : PFunctor.{uA₃, uB₃}}

/-- One-step coalgebra for transporting a resumption along a polynomial
lens. The lens sends query positions forward and runtime directions backward. -/
def mapLensStep (lens : Lens p q) :
    Resumption p β → β ⊕ q.Obj (Resumption p β)
  | computation => match dest computation with
    | Sum.inl value => Sum.inl value
    | Sum.inr ⟨position, next⟩ =>
        Sum.inr ⟨lens.toFunA position,
          fun direction => next (lens.toFunB position direction)⟩

/-- Transport a resumption along a polynomial lens. -/
def mapLens (lens : Lens p q) (computation : Resumption p β) : Resumption q β :=
  corec (mapLensStep lens) computation

@[simp] theorem dest_mapLens (lens : Lens p q) (computation : Resumption p β) :
    dest (mapLens lens computation) = match dest computation with
      | Sum.inl value => Sum.inl value
      | Sum.inr ⟨position, next⟩ =>
          Sum.inr ⟨lens.toFunA position,
            fun direction => mapLens lens (next (lens.toFunB position direction))⟩ := by
  unfold mapLens
  rw [dest_corec]
  rcases h : dest computation with value | ⟨position, next⟩
  · simp [mapLensStep, h]
  · simp only [mapLensStep, h, Sum.map_inr, PFunctor.map_eq]
    rfl

@[simp] theorem mapLens_pure (lens : Lens p q) (value : β) :
    mapLens lens (pure value) = pure value := by
  apply eq_of_dest_eq
  simp

@[simp] theorem mapLens_query (lens : Lens p q) (position : p.A)
    (next : p.B position → Resumption p β) :
    mapLens lens (query position next) =
      query (lens.toFunA position)
        (fun direction => mapLens lens (next (lens.toFunB position direction))) := by
  apply eq_of_dest_eq
  simp

@[simp] theorem mapLens_id (computation : Resumption p β) :
    mapLens (Lens.id p) computation = computation := by
  apply bisim
    (fun left right => ∃ source,
      left = mapLens (Lens.id p) source ∧ right = source)
  · rintro left right ⟨source, hleft, hright⟩
    subst left
    subst right
    rcases h : dest source with value | ⟨position, next⟩
    · exact .pure value (by rw [dest_mapLens, h]) h
    · exact .query position
        (fun direction => mapLens (Lens.id p) (next direction)) next
        (by rw [dest_mapLens, h]; rfl) h
        (fun direction => ⟨next direction, rfl, rfl⟩)
  · exact ⟨computation, rfl, rfl⟩

@[simp] theorem mapLens_comp (lens₂ : Lens q r) (lens₁ : Lens p q)
    (computation : Resumption p β) :
    mapLens lens₂ (mapLens lens₁ computation) =
      mapLens (lens₂ ∘ₗ lens₁) computation := by
  apply bisim
    (fun left right => ∃ source,
      left = mapLens lens₂ (mapLens lens₁ source) ∧
      right = mapLens (lens₂ ∘ₗ lens₁) source)
  · rintro left right ⟨source, hleft, hright⟩
    subst left
    subst right
    rcases h : dest source with value | ⟨position, next⟩
    · exact .pure value (by simp [h]) (by simp [h])
    · exact .query (lens₂.toFunA (lens₁.toFunA position))
        (fun direction => mapLens lens₂
          (mapLens lens₁ (next (lens₁.toFunB position
            (lens₂.toFunB (lens₁.toFunA position) direction)))))
        (fun direction => mapLens (lens₂ ∘ₗ lens₁)
          (next (lens₁.toFunB position
            (lens₂.toFunB (lens₁.toFunA position) direction))))
        (by rw [dest_mapLens, dest_mapLens, h])
        (by rw [dest_mapLens, h]; rfl)
        (fun direction => ⟨_, rfl, rfl⟩)
  · exact ⟨computation, rfl, rfl⟩

theorem mapLens_bind (lens : Lens p q) (computation : Resumption p α)
    (k : α → Resumption p β) :
    mapLens lens (bind computation k) =
      bind (mapLens lens computation) (fun value => mapLens lens (k value)) := by
  apply bisim
    (fun left right => left = right ∨ ∃ source : Resumption p α,
      left = mapLens lens (bind source k) ∧
      right = bind (mapLens lens source) (fun value => mapLens lens (k value)))
  · intro left right hrel
    rcases hrel with hEq | ⟨source, hleft, hright⟩
    · subst left
      rcases h : dest right with value | ⟨position, next⟩
      · exact .pure value h h
      · exact .query position next next h h (fun _ => Or.inl rfl)
    · subst left
      subst right
      rcases h : dest source with value | ⟨position, next⟩
      · rw [show source = pure value by apply eq_of_dest_eq; simpa using h]
        simp only [bind_pure_left, mapLens_pure]
        rcases hk : dest (mapLens lens (k value)) with result | ⟨position, next⟩
        · exact .pure result hk hk
        · exact .query position next next hk hk (fun _ => Or.inl rfl)
      · exact .query (lens.toFunA position)
          (fun direction => mapLens lens
            (bind (next (lens.toFunB position direction)) k))
          (fun direction => bind
            (mapLens lens (next (lens.toFunB position direction)))
            (fun value => mapLens lens (k value)))
          (by simp [h]) (by simp [h])
          (fun direction => Or.inr ⟨next (lens.toFunB position direction), rfl, rfl⟩)
  · exact Or.inr ⟨computation, rfl, rfl⟩

theorem mapLens_map (lens : Lens p q) (f : α → β)
    (computation : Resumption p α) :
    mapLens lens (map f computation) = map f (mapLens lens computation) := by
  unfold map
  rw [mapLens_bind]
  simp

end MapLens

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
