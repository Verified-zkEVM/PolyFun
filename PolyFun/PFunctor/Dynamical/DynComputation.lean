/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Simulation
public import PolyFun.PFunctor.Free.Resumption

/-!
# Returning dynamical computations

A `DynComputation p α β` is a hidden-state realization of an `α`-indexed
family of `Resumption p β` computations. Its underlying `Machine` runs over
the return-or-query polynomial `C β + p`: a state either returns a value and
has no directions, or exposes a visible `p`-query whose direction selects the
next state.

Unlike a partial readout stored separately from the dynamics, this
representation carries no unreachable `p`-interaction data at returned
states. In particular, `DynComputation.ofFn` and the `Pure` instance are
available for every interface and do not require a chosen `Point p`.

State-sum sequential composition performs return handoff in one observation
and denotes exactly monadic bind on `Resumption`.
-/

@[expose] public section

universe u v w x uA uB uA₂ uB₂ uα uβ uγ uδ uε uζ

namespace PFunctor

namespace DynSystem

/-- A stateful realization of a returning computation over `p`. Its dynamics
are uniformly available as `.toDynSystem`, while `init` selects the
initial state for each input. -/
structure DynComputation (p : PFunctor.{uA, uB}) (α : Type uα) (β : Type uβ)
    extends Machine.{u, max uβ uA, uB} (C.{uβ, uB} β + p) where
  /-- Where the computation starts, given an input. -/
  init : α → State

namespace DynComputation

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-- The computational one-step view of a state: either a returned value or a
visible query paired with its state-valued continuation. -/
def view (M : DynComputation.{u} p α β) (state : M.State) : β ⊕ p.Obj M.State :=
  Resumption.unpack (M.toDynSystem.out state)

/-- The canonical state-free semantics of a dynamical computation. -/
def denote (M : DynComputation.{u} p α β) (input : α) : Resumption p β :=
  M.toDynSystem.behavior (M.init input)

/-- The resumption destructor of the behavior from an arbitrary hidden state
is exactly the computation's one-step view, with recursive behaviors in every
query continuation. -/
@[simp] theorem dest_behavior_view (M : DynComputation.{u} p α β) (state : M.State) :
    Resumption.dest (M.toDynSystem.behavior state) =
      Sum.map (fun value : β => value) (p.map M.toDynSystem.behavior) (M.view state) := by
  unfold Resumption.dest view
  rw [DynSystem.dest_behavior]
  change Resumption.unpack
      ((C.{uβ, uB} β + p).map M.toDynSystem.behavior
        (M.toDynSystem.out state)) = _
  exact Resumption.unpack_map _ _

/-- An immediately returning computation determined by its input. No point of
`p` is needed because a return is represented by a directionless position of
`C β`. -/
def ofFn (f : α → β) : DynComputation.{uβ} p α β where
  State := β
  toDynSystem := Sum.inl ⇆ fun _ => PEmpty.elim
  init := f

@[simp] theorem ofFn_State (f : α → β) : (ofFn (p := p) f).State = β := rfl

@[simp] theorem ofFn_init (f : α → β) (input : α) :
    (ofFn (p := p) f).init input = f input := rfl

@[simp] theorem view_ofFn (f : α → β) (value : β) :
    (ofFn (p := p) f).view value = Sum.inl value := rfl

@[simp] theorem view_init_ofFn (f : α → β) (input : α) :
    (ofFn (p := p) f).view ((ofFn (p := p) f).init input) = Sum.inl (f input) := rfl

@[simp] theorem denote_ofFn (f : α → β) (input : α) :
    (ofFn (p := p) f).denote input = Resumption.pure (f input) := by
  apply M.eq_of_dest_eq
  unfold denote Resumption.pure ofFn
  rw [DynSystem.dest_behavior, M.dest_mk]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext direction
    exact PEmpty.elim direction

/-- The `Pure` operation is the input-independent specialization of `ofFn`. -/
instance : Pure (DynComputation.{uβ} p α) where
  pure value := ofFn fun _ => value

theorem pure_eq_ofFn (value : β) :
    (pure value : DynComputation.{uβ} p α β) = ofFn (fun _ => value) := rfl

@[simp] theorem pure_State (value : β) :
    (pure value : DynComputation.{uβ} p α β).State = β := rfl

@[simp] theorem pure_init (value : β) (input : α) :
    (pure value : DynComputation.{uβ} p α β).init input = value := rfl

@[simp] theorem view_pure (value state : β) :
    (pure value : DynComputation.{uβ} p α β).view state = Sum.inl state := rfl

@[simp] theorem view_init_pure (value : β) (input : α) :
    (pure value : DynComputation.{uβ} p α β).view
      ((pure value : DynComputation.{uβ} p α β).init input) = Sum.inl value := rfl

@[simp] theorem denote_pure (value : β) (input : α) :
    (pure value : DynComputation.{uβ} p α β).denote input = Resumption.pure value := by
  change (ofFn (p := p) (fun _ : α => value)).denote input = Resumption.pure value
  exact denote_ofFn (fun _ : α => value) input

/-- The denotation exposes exactly the computational view at the initialized
state, recursively denoting every query continuation. -/
@[simp] theorem dest_denote (M : DynComputation.{u} p α β) (input : α) :
    Resumption.dest (M.denote input) =
      Sum.map (fun value : β => value) (p.map M.toDynSystem.behavior)
        (M.view (M.init input)) := by
  unfold denote
  exact dest_behavior_view M (M.init input)

/-! ## Observational equivalence and variance -/

/-- Two returning computations are observationally equivalent when their
state-free resumption semantics agree at every input. Their hidden state types
and state universes may be unrelated. -/
def ObsEq (M : DynComputation.{u} p α β) (N : DynComputation.{v} p α β) : Prop :=
  ∀ input, M.denote input = N.denote input

@[refl] theorem ObsEq.refl (M : DynComputation.{u} p α β) : ObsEq M M :=
  fun _ => rfl

@[symm] theorem ObsEq.symm {M : DynComputation.{u} p α β}
    {N : DynComputation.{v} p α β} (h : ObsEq M N) : ObsEq N M :=
  fun input => (h input).symm

@[trans] theorem ObsEq.trans {M : DynComputation.{u} p α β}
    {N : DynComputation.{v} p α β} {O : DynComputation.{w} p α β}
    (hMN : ObsEq M N) (hNO : ObsEq N O) : ObsEq M O :=
  fun input => (hMN input).trans (hNO input)

/-- Reindex a returning computation contravariantly along an input map. -/
def contramapInput {γ : Type uγ} (M : DynComputation.{u} p α β) (f : γ → α) :
    DynComputation.{u} p γ β where
  State := M.State
  toDynSystem := M.toDynSystem
  init := M.init ∘ f

@[simp] theorem contramapInput_State {γ : Type uγ} (f : γ → α)
    (M : DynComputation.{u} p α β) : (M.contramapInput f).State = M.State := rfl

@[simp] theorem contramapInput_init {γ : Type uγ} (f : γ → α)
    (M : DynComputation.{u} p α β) (input : γ) :
    (M.contramapInput f).init input = M.init (f input) := rfl

@[simp] theorem contramapInput_view {γ : Type uγ} (f : γ → α)
    (M : DynComputation.{u} p α β) (state : M.State) :
    (M.contramapInput f).view state = M.view state := rfl

@[simp] theorem contramapInput_denote {γ : Type uγ} (f : γ → α)
    (M : DynComputation.{u} p α β) (input : γ) :
    (M.contramapInput f).denote input = M.denote (f input) := rfl

private def mapResultLift {γ : Type uγ} (f : β → γ) :
    Lens.{max uβ uA, uB, max uγ uA, uB}
      (C.{uβ, uB} β + p) (C.{uγ, uB} γ + p) :=
  Lens.sumMap (Lens.toConst f) (Lens.id p)

/-- Map the returned value of a computation while preserving its hidden state
and visible-query interface. -/
def mapResult {γ : Type uγ} (M : DynComputation.{u} p α β) (f : β → γ) :
    DynComputation.{u} p α γ where
  State := M.State
  toDynSystem := Lens.comp
    (Lens.sumMap (Lens.toConst f) (Lens.id p)) M.toDynSystem
  init := M.init

@[simp] theorem mapResult_view {γ : Type uγ} (f : β → γ)
    (M : DynComputation.{u} p α β) (state : M.State) :
    (M.mapResult f).view state = match M.view state with
      | Sum.inl value => Sum.inl (f value)
      | Sum.inr query => Sum.inr query := by
  unfold view mapResult
  change Resumption.unpack
      (Lens.mapObj (mapResultLift f)
        (M.toDynSystem.out state)) = _
  rcases h : M.toDynSystem.out state with ⟨position, next⟩
  rcases position with value | position <;> rfl

@[simp] theorem mapResult_State {γ : Type uγ} (f : β → γ)
    (M : DynComputation.{u} p α β) : (M.mapResult f).State = M.State := rfl

@[simp] theorem mapResult_init {γ : Type uγ} (f : β → γ)
    (M : DynComputation.{u} p α β) (input : α) :
    (M.mapResult f).init input = M.init input := rfl

/-- Mapping returned values commutes exactly with state behavior. -/
theorem behavior_mapResult {γ : Type uγ} (f : β → γ)
    (M : DynComputation.{u} p α β) (state : M.State) :
    (M.mapResult f).toDynSystem.behavior state =
      Resumption.map f (M.toDynSystem.behavior state) := by
  apply Resumption.bisim
    (fun left right => ∃ current : M.State,
      left = (M.mapResult f).toDynSystem.behavior current ∧
      right = Resumption.map f (M.toDynSystem.behavior current))
  · rintro left right ⟨current, hleft, hright⟩
    subst left
    subst right
    rcases h : M.view current with value | ⟨position, next⟩
    · exact .pure (f value)
        (by rw [dest_behavior_view, mapResult_view, h]; rfl)
        (by simp [Resumption.map, dest_behavior_view, h])
    · exact .query position
        (fun direction => (M.mapResult f).toDynSystem.behavior (next direction))
        (fun direction => Resumption.map f
          (M.toDynSystem.behavior (next direction)))
        (by rw [dest_behavior_view, mapResult_view, h]; rfl)
        (by simp [Resumption.map, dest_behavior_view, h])
        (fun direction => ⟨next direction, rfl, rfl⟩)
  · exact ⟨state, rfl, rfl⟩

@[simp] theorem mapResult_denote {γ : Type uγ} (f : β → γ)
    (M : DynComputation.{u} p α β) (input : α) :
    (M.mapResult f).denote input = Resumption.map f (M.denote input) :=
  behavior_mapResult f M (M.init input)

private def wrapLift {q : PFunctor.{uA₂, uB₂}} (lens : Lens p q) :
    Lens.{max uβ uA, uB, max uβ uA₂, uB₂}
      (C.{uβ, uB} β + p) (C.{uβ, uB₂} β + q) :=
  Lens.sumMap (Lens.toConst (fun value : β => value)) lens

/-- Change a returning computation's visible-query interface along a lens while preserving its
hidden state and return values. -/
def wrap {q : PFunctor.{uA₂, uB₂}} (M : DynComputation.{u} p α β)
    (lens : Lens p q) : DynComputation.{u} q α β where
  State := M.State
  toDynSystem := Lens.comp
    (Lens.sumMap (Lens.toConst (fun value : β => value)) lens) M.toDynSystem
  init := M.init

@[simp] theorem wrap_view {q : PFunctor.{uA₂, uB₂}} (lens : Lens p q)
    (M : DynComputation.{u} p α β) (state : M.State) :
    (M.wrap lens).view state = match M.view state with
      | Sum.inl value => Sum.inl value
      | Sum.inr ⟨position, next⟩ =>
          Sum.inr ⟨lens.toFunA position,
            fun direction => next (lens.toFunB position direction)⟩ := by
  unfold view wrap
  change Resumption.unpack
      (Lens.mapObj (wrapLift lens)
        (M.toDynSystem.out state)) = _
  rcases h : M.toDynSystem.out state with ⟨position, next⟩
  rcases position with value | position <;> rfl

@[simp] theorem wrap_State {q : PFunctor.{uA₂, uB₂}} (lens : Lens p q)
    (M : DynComputation.{u} p α β) : (M.wrap lens).State = M.State := rfl

@[simp] theorem wrap_init {q : PFunctor.{uA₂, uB₂}} (lens : Lens p q)
    (M : DynComputation.{u} p α β) (input : α) :
    (M.wrap lens).init input = M.init input := rfl

/-- Interface transport commutes exactly with state behavior. -/
theorem behavior_wrap {q : PFunctor.{uA₂, uB₂}} (lens : Lens p q)
    (M : DynComputation.{u} p α β) (state : M.State) :
    (M.wrap lens).toDynSystem.behavior state =
      Resumption.mapLens lens (M.toDynSystem.behavior state) := by
  apply Resumption.bisim
    (fun left right => ∃ current : M.State,
      left = (M.wrap lens).toDynSystem.behavior current ∧
      right = Resumption.mapLens lens (M.toDynSystem.behavior current))
  · rintro left right ⟨current, hleft, hright⟩
    subst left
    subst right
    rcases h : M.view current with value | ⟨position, next⟩
    · exact .pure value
        (by rw [dest_behavior_view, wrap_view, h]; rfl)
        (by simp [dest_behavior_view, h])
    · exact .query (lens.toFunA position)
        (fun direction => (M.wrap lens).toDynSystem.behavior
          (next (lens.toFunB position direction)))
        (fun direction => Resumption.mapLens lens
          (M.toDynSystem.behavior (next (lens.toFunB position direction))))
        (by rw [dest_behavior_view, wrap_view, h]; rfl)
        (by simp [dest_behavior_view, h])
        (fun direction => ⟨next (lens.toFunB position direction), rfl, rfl⟩)
  · exact ⟨state, rfl, rfl⟩

@[simp] theorem wrap_denote {q : PFunctor.{uA₂, uB₂}} (lens : Lens p q)
    (M : DynComputation.{u} p α β) (input : α) :
    (M.wrap lens).denote input = Resumption.mapLens lens (M.denote input) :=
  behavior_wrap lens M (M.init input)

/-- Simultaneously reindex inputs and map returned values. -/
def dimap {γ : Type uγ} {δ : Type uδ} (M : DynComputation.{u} p α β)
    (f : γ → α) (g : β → δ) : DynComputation.{u} p γ δ :=
  (M.contramapInput f).mapResult g

@[simp] theorem dimap_State {γ : Type uγ} {δ : Type uδ} (f : γ → α) (g : β → δ)
    (M : DynComputation.{u} p α β) : (M.dimap f g).State = M.State := rfl

@[simp] theorem dimap_init {γ : Type uγ} {δ : Type uδ} (f : γ → α) (g : β → δ)
    (M : DynComputation.{u} p α β) (input : γ) :
    (M.dimap f g).init input = M.init (f input) := rfl

@[simp] theorem dimap_view {γ : Type uγ} {δ : Type uδ} (f : γ → α) (g : β → δ)
    (M : DynComputation.{u} p α β) (state : M.State) :
    (M.dimap f g).view state = match M.view state with
      | Sum.inl value => Sum.inl (g value)
      | Sum.inr query => Sum.inr query := by
  unfold dimap mapResult contramapInput view
  change Resumption.unpack
      (Lens.mapObj (mapResultLift g)
        (M.toDynSystem.out state)) = _
  rcases h : M.toDynSystem.out state with ⟨position, next⟩
  rcases position with value | position <;> rfl

@[simp] theorem dimap_denote {γ : Type uγ} {δ : Type uδ} (f : γ → α) (g : β → δ)
    (M : DynComputation.{u} p α β) (input : γ) :
    (M.dimap f g).denote input = Resumption.map g (M.denote (f input)) := by
  simp [dimap]

/-! ### Variance laws -/

private theorem mapResultLift_id :
    mapResultLift (p := p) (id : β → β) =
      Lens.id.{max uβ uA, uB} (C.{uβ, uB} β + p) := by
  refine Lens.ext _ _ (fun position => by cases position <;> rfl) ?_
  intro position
  cases position with
  | inl value =>
      funext direction
      exact PEmpty.elim direction
  | inr position => rfl

private theorem mapResultLift_comp {γ : Type uγ} {δ : Type uδ}
    (f : β → γ) (g : γ → δ) :
    Lens.comp (mapResultLift (p := p) g) (mapResultLift (p := p) f) =
      mapResultLift (p := p) (g ∘ f) := by
  refine Lens.ext _ _ (fun position => by cases position <;> rfl) ?_
  intro position
  cases position with
  | inl value =>
      funext direction
      exact PEmpty.elim direction
  | inr position => rfl

private theorem wrapLift_id :
    wrapLift (β := β) (Lens.id p) =
      Lens.id.{max uβ uA, uB} (C.{uβ, uB} β + p) := by
  refine Lens.ext _ _ (fun position => by cases position <;> rfl) ?_
  intro position
  cases position with
  | inl value =>
      funext direction
      exact PEmpty.elim direction
  | inr position => rfl

private theorem wrapLift_comp {q : PFunctor.{uA₂, uB₂}}
    {r : PFunctor.{uγ, uδ}} (lens₁ : Lens p q) (lens₂ : Lens q r) :
    Lens.comp (wrapLift (β := β) lens₂) (wrapLift (β := β) lens₁) =
      wrapLift (β := β) (lens₂ ∘ₗ lens₁) := by
  refine Lens.ext _ _ (fun position => by cases position <;> rfl) ?_
  intro position
  cases position with
  | inl value =>
      funext direction
      exact PEmpty.elim direction
  | inr position => rfl

private theorem mapResultLift_wrapLift {q : PFunctor.{uA₂, uB₂}}
    {γ : Type uγ} (f : β → γ) (lens : Lens p q) :
    Lens.comp (wrapLift (β := γ) lens) (mapResultLift (p := p) f) =
      Lens.comp (mapResultLift (p := q) f) (wrapLift (β := β) lens) := by
  refine Lens.ext _ _ (fun position => by cases position <;> rfl) ?_
  intro position
  cases position with
  | inl value =>
      funext direction
      exact PEmpty.elim direction
  | inr position => rfl

@[simp] theorem contramapInput_id (M : DynComputation.{u} p α β) :
    M.contramapInput id = M := by
  cases M
  rfl

@[simp] theorem contramapInput_comp {γ : Type uγ} {δ : Type uδ}
    (M : DynComputation.{u} p α β) (f : γ → α) (g : δ → γ) :
    (M.contramapInput f).contramapInput g = M.contramapInput (f ∘ g) := rfl

@[simp] theorem mapResult_id (M : DynComputation.{u} p α β) :
    M.mapResult id = M := by
  cases M with
  | mk machine init =>
      cases machine with
      | mk State system =>
          unfold mapResult
          have hsystem : Lens.comp (mapResultLift (p := p) (id : β → β)) system =
              system := by
            calc
              _ = Lens.comp (Lens.id.{max uβ uA, uB}
                    (C.{uβ, uB} β + p)) system :=
                congrArg (fun lifted => Lens.comp lifted system) mapResultLift_id
              _ = system := rfl
          change ({ State := State
                    toDynSystem := Lens.comp (mapResultLift (p := p) id) system
                    init := init } : DynComputation p α β) =
            { State := State, toDynSystem := system, init := init }
          rw [hsystem]

@[simp] theorem mapResult_comp {γ : Type uγ} {δ : Type uδ}
    (M : DynComputation.{u} p α β) (f : β → γ) (g : γ → δ) :
    (M.mapResult f).mapResult g = M.mapResult (g ∘ f) := by
  cases M with
  | mk machine init =>
      cases machine with
      | mk State system =>
          have hsystem : Lens.comp (mapResultLift (p := p) g)
              (Lens.comp (mapResultLift (p := p) f) system) =
              Lens.comp (mapResultLift (p := p) (g ∘ f)) system := by
            calc
              _ = Lens.comp
                    (Lens.comp (mapResultLift (p := p) g) (mapResultLift (p := p) f))
                    system := rfl
              _ = _ := congrArg (fun lifted => Lens.comp lifted system)
                (mapResultLift_comp f g)
          change ({ State := State
                    toDynSystem := Lens.comp (mapResultLift (p := p) g)
                      (Lens.comp (mapResultLift (p := p) f) system)
                    init := init } : DynComputation p α δ) =
            { State := State
              toDynSystem := Lens.comp (mapResultLift (p := p) (g ∘ f)) system
              init := init }
          rw [hsystem]

@[simp] theorem wrap_id (M : DynComputation.{u} p α β) :
    M.wrap (Lens.id p) = M := by
  cases M with
  | mk machine init =>
      cases machine with
      | mk State system =>
          have hsystem : Lens.comp (wrapLift (β := β) (Lens.id p)) system = system := by
            calc
              _ = Lens.comp (Lens.id.{max uβ uA, uB} (C.{uβ, uB} β + p)) system :=
                congrArg (fun lifted => Lens.comp lifted system) wrapLift_id
              _ = system := rfl
          change ({ State := State
                    toDynSystem := Lens.comp (wrapLift (β := β) (Lens.id p)) system
                    init := init } : DynComputation p α β) =
            { State := State, toDynSystem := system, init := init }
          rw [hsystem]

@[simp] theorem wrap_comp {q : PFunctor.{uA₂, uB₂}} {r : PFunctor.{uγ, uδ}}
    (M : DynComputation.{u} p α β) (lens₁ : Lens p q) (lens₂ : Lens q r) :
    (M.wrap lens₁).wrap lens₂ = M.wrap (Lens.comp lens₂ lens₁) := by
  cases M with
  | mk machine init =>
      cases machine with
      | mk State system =>
          have hsystem : Lens.comp (wrapLift (β := β) lens₂)
              (Lens.comp (wrapLift (β := β) lens₁) system) =
              Lens.comp (wrapLift (β := β) (Lens.comp lens₂ lens₁)) system := by
            calc
              _ = Lens.comp
                    (Lens.comp (wrapLift (β := β) lens₂) (wrapLift (β := β) lens₁))
                    system := rfl
              _ = _ := congrArg (fun lifted => Lens.comp lifted system)
                (wrapLift_comp lens₁ lens₂)
          change ({ State := State
                    toDynSystem := Lens.comp (wrapLift (β := β) lens₂)
                      (Lens.comp (wrapLift (β := β) lens₁) system)
                    init := init } : DynComputation r α β) =
            { State := State
              toDynSystem := Lens.comp
                (wrapLift (β := β) (Lens.comp lens₂ lens₁)) system
              init := init }
          rw [hsystem]

theorem mapResult_wrap {q : PFunctor.{uA₂, uB₂}} {γ : Type uγ}
    (M : DynComputation.{u} p α β) (f : β → γ) (lens : Lens p q) :
    (M.mapResult f).wrap lens = (M.wrap lens).mapResult f := by
  cases M with
  | mk machine init =>
      cases machine with
      | mk State system =>
          have hsystem : Lens.comp (wrapLift (β := γ) lens)
              (Lens.comp (mapResultLift (p := p) f) system) =
              Lens.comp (mapResultLift (p := q) f)
                (Lens.comp (wrapLift (β := β) lens) system) := by
            calc
              _ = Lens.comp
                    (Lens.comp (wrapLift (β := γ) lens) (mapResultLift (p := p) f))
                    system := rfl
              _ = Lens.comp
                    (Lens.comp (mapResultLift (p := q) f) (wrapLift (β := β) lens))
                    system := congrArg (fun lifted => Lens.comp lifted system)
                      (mapResultLift_wrapLift f lens)
              _ = _ := rfl
          change ({ State := State
                    toDynSystem := Lens.comp (wrapLift (β := γ) lens)
                      (Lens.comp (mapResultLift (p := p) f) system)
                    init := init } : DynComputation q α γ) =
            { State := State
              toDynSystem := Lens.comp (mapResultLift (p := q) f)
                (Lens.comp (wrapLift (β := β) lens) system)
              init := init }
          rw [hsystem]

@[simp] theorem dimap_id (M : DynComputation.{u} p α β) :
    M.dimap id id = M := by
  simp [dimap]

theorem contramapInput_mapResult {γ : Type uγ} {δ : Type uδ}
    (M : DynComputation.{u} p α β) (f : γ → α) (g : β → δ) :
    (M.mapResult g).contramapInput f = (M.contramapInput f).mapResult g := rfl

@[simp] theorem dimap_comp {γ : Type uγ} {δ : Type uδ}
    {ε : Type uε} {ζ : Type uζ}
    (M : DynComputation.{u} p α β) (f₁ : γ → α) (g₁ : β → δ)
    (f₂ : ε → γ) (g₂ : δ → ζ) :
    (M.dimap f₁ g₁).dimap f₂ g₂ =
      M.dimap (f₁ ∘ f₂) (g₂ ∘ g₁) := by
  unfold dimap
  rw [contramapInput_mapResult, contramapInput_comp, mapResult_comp]

/-! ### Observational congruence -/

theorem ObsEq.contramapInput {M : DynComputation.{u} p α β}
    {N : DynComputation.{v} p α β} (h : ObsEq M N) {γ : Type uγ} (f : γ → α) :
    ObsEq (M.contramapInput f) (N.contramapInput f) :=
  fun input => h (f input)

theorem ObsEq.mapResult {M : DynComputation.{u} p α β}
    {N : DynComputation.{v} p α β} (h : ObsEq M N) {γ : Type uγ} (f : β → γ) :
    ObsEq (M.mapResult f) (N.mapResult f) := by
  intro input
  simp only [mapResult_denote, h input]

theorem ObsEq.wrap {M : DynComputation.{u} p α β}
    {N : DynComputation.{v} p α β} (h : ObsEq M N)
    {q : PFunctor.{uA₂, uB₂}} (lens : Lens p q) :
    ObsEq (M.wrap lens) (N.wrap lens) := by
  intro input
  simp only [wrap_denote, h input]

theorem ObsEq.dimap {M : DynComputation.{u} p α β}
    {N : DynComputation.{v} p α β} (h : ObsEq M N)
    {γ : Type uγ} {δ : Type uδ} (f : γ → α) (g : β → δ) :
    ObsEq (M.dimap f g) (N.dimap f g) := by
  intro input
  simp only [dimap_denote, h (f input)]

/-! ## Sequential composition -/

private theorem view_of_packedStep {S : Type u}
    (step : S → β ⊕ p.Obj S) (init : α → S) (state : S) :
    ({ State := S
       toDynSystem :=
        (fun current => (Resumption.pack (step current)).1) ⇆
          fun current => (Resumption.pack (step current)).2
       init := init } : DynComputation p α β).view state = step state := by
  change Resumption.unpack (Resumption.pack (step state)) = step state
  exact Resumption.unpack_pack (step state)

/-- Run `M₁` until it returns an intermediate value, then immediately expose
the initial view of `M₂` at that value. The sum state records which machine
owns the next visible query; a return-to-query handoff introduces neither a
silent transition nor a fabricated query. -/
def seqComp {γ : Type uγ} (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) : DynComputation.{max u v} p α γ :=
  let step : M₁.State ⊕ M₂.State → γ ⊕ p.Obj (M₁.State ⊕ M₂.State)
    | Sum.inl state₁ =>
        match M₁.view state₁ with
        | Sum.inl value =>
            Sum.map (fun result : γ => result)
              (p.map (Sum.inr : M₂.State → M₁.State ⊕ M₂.State))
              (M₂.view (M₂.init value))
        | Sum.inr query =>
            Sum.inr (p.map (Sum.inl : M₁.State → M₁.State ⊕ M₂.State) query)
    | Sum.inr state₂ =>
        Sum.map (fun result : γ => result)
          (p.map (Sum.inr : M₂.State → M₁.State ⊕ M₂.State))
          (M₂.view state₂)
  { State := M₁.State ⊕ M₂.State
    toDynSystem :=
      (fun state => (Resumption.pack (step state)).1) ⇆
        fun state => (Resumption.pack (step state)).2
    init := fun input => Sum.inl (M₁.init input) }

@[simp] theorem seqComp_State {γ : Type uγ} (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) :
    (M₁.seqComp M₂).State = (M₁.State ⊕ M₂.State) := rfl

@[simp] theorem seqComp_init {γ : Type uγ} (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) (input : α) :
    (M₁.seqComp M₂).init input = Sum.inl (M₁.init input) := rfl

@[simp] theorem seqComp_view_inl {γ : Type uγ} (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) (state₁ : M₁.State) :
    (M₁.seqComp M₂).view (Sum.inl state₁) =
      match M₁.view state₁ with
      | Sum.inl value =>
          Sum.map (fun result : γ => result)
            (p.map (Sum.inr : M₂.State → M₁.State ⊕ M₂.State))
            (M₂.view (M₂.init value))
      | Sum.inr query =>
          Sum.inr (p.map (Sum.inl : M₁.State → M₁.State ⊕ M₂.State) query) := by
  unfold seqComp
  exact view_of_packedStep _ _ _

@[simp] theorem seqComp_view_inr {γ : Type uγ} (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) (state₂ : M₂.State) :
    (M₁.seqComp M₂).view (Sum.inr state₂) =
      Sum.map (fun result : γ => result)
        (p.map (Sum.inr : M₂.State → M₁.State ⊕ M₂.State))
        (M₂.view state₂) := by
  unfold seqComp
  exact view_of_packedStep _ _ _

private def seqCompSem {γ : Type uγ} (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) :
    M₁.State ⊕ M₂.State → Resumption p γ
  | Sum.inl state₁ => Resumption.bind (M₁.toDynSystem.behavior state₁) M₂.denote
  | Sum.inr state₂ => M₂.toDynSystem.behavior state₂

private theorem seqCompSem_coalg {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (state : M₁.State ⊕ M₂.State) :
    Resumption.dest (seqCompSem M₁ M₂ state) =
      Sum.map (fun result : γ => result) (p.map (seqCompSem M₁ M₂))
        ((M₁.seqComp M₂).view state) := by
  cases state with
  | inl state₁ =>
      rcases h₁ : M₁.view state₁ with value | ⟨position, next⟩
      · rcases h₂ : M₂.view (M₂.init value) with result | ⟨position, next⟩
        · rw [seqComp_view_inl, h₁]
          simp only [seqComp_State]
          rw [h₂]
          simp only [seqCompSem, Resumption.dest_bind, dest_behavior_view, h₁,
            dest_denote, h₂, Sum.map_inl]
        · rw [seqComp_view_inl, h₁]
          simp only [seqComp_State]
          rw [h₂]
          simp only [seqCompSem, Resumption.dest_bind, dest_behavior_view, h₁,
            dest_denote, h₂, Sum.map_inl, Sum.map_inr, PFunctor.map_eq]
          apply congrArg Sum.inr
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            funext direction
            rfl
      · rw [seqComp_view_inl, h₁]
        simp only [seqCompSem, Resumption.dest_bind, dest_behavior_view, h₁,
          Sum.map_inr, PFunctor.map_eq]
        apply congrArg Sum.inr
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext direction
          rfl
  | inr state₂ =>
      rcases h₂ : M₂.view state₂ with result | ⟨position, next⟩
      · rw [seqComp_view_inr, h₂]
        simp only [seqCompSem, dest_behavior_view, h₂, Sum.map_inl]
      · rw [seqComp_view_inr, h₂]
        simp only [seqCompSem, dest_behavior_view, h₂, Sum.map_inr, PFunctor.map_eq]
        apply congrArg Sum.inr
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext direction
          rfl

/-- State-level semantics of sequential composition. Phase-one states denote
resumption bind; phase-two states denote the second computation directly. -/
theorem behavior_seqComp {γ : Type uγ} (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) (state : M₁.State ⊕ M₂.State) :
    (M₁.seqComp M₂).toDynSystem.behavior state =
      match state with
      | Sum.inl state₁ =>
          Resumption.bind (M₁.toDynSystem.behavior state₁) M₂.denote
      | Sum.inr state₂ => M₂.toDynSystem.behavior state₂ := by
  have hsem : seqCompSem M₁ M₂ =
      Resumption.corec (M₁.seqComp M₂).view :=
    Resumption.corec_unique _ _ (seqCompSem_coalg M₁ M₂)
  have hbehavior : (M₁.seqComp M₂).toDynSystem.behavior =
      Resumption.corec (M₁.seqComp M₂).view :=
    Resumption.corec_unique _ _ (dest_behavior_view (M₁.seqComp M₂))
  change (M₁.seqComp M₂).toDynSystem.behavior state = seqCompSem M₁ M₂ state
  exact congrFun (hbehavior.trans hsem.symm) state

@[simp] theorem behavior_seqComp_inl {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (state₁ : M₁.State) :
    (M₁.seqComp M₂).toDynSystem.behavior (Sum.inl state₁) =
      Resumption.bind (M₁.toDynSystem.behavior state₁) M₂.denote :=
  behavior_seqComp M₁ M₂ (Sum.inl state₁)

@[simp] theorem behavior_seqComp_inr {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (state₂ : M₂.State) :
    (M₁.seqComp M₂).toDynSystem.behavior (Sum.inr state₂) =
      M₂.toDynSystem.behavior state₂ :=
  behavior_seqComp M₁ M₂ (Sum.inr state₂)

/-- Sequential composition realizes resumption bind exactly. -/
@[simp] theorem denote_seqComp {γ : Type uγ} (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) (input : α) :
    (M₁.seqComp M₂).denote input =
      Resumption.bind (M₁.denote input) M₂.denote := by
  unfold denote
  exact behavior_seqComp_inl M₁ M₂ (M₁.init input)

/-- Sequential composition is congruent in both computations, independently
of all four hidden-state types and universes. -/
theorem ObsEq.seqComp {γ : Type uγ}
    {M₁ : DynComputation.{u} p α β} {N₁ : DynComputation.{v} p α β}
    {M₂ : DynComputation.{w} p β γ} {N₂ : DynComputation.{x} p β γ}
    (h₁ : ObsEq M₁ N₁) (h₂ : ObsEq M₂ N₂) :
    ObsEq (M₁.seqComp M₂) (N₁.seqComp N₂) := by
  intro input
  simp only [denote_seqComp]
  exact congrArg₂ Resumption.bind (h₁ input) (funext h₂)

/-- Sequential composition is associative up to observational equivalence;
structural equality is intentionally not claimed because the sum states nest
in different ways. -/
theorem seqComp_assoc_obsEq {γ : Type uγ} {δ : Type uδ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (M₃ : DynComputation.{w} p γ δ) :
    ObsEq ((M₁.seqComp M₂).seqComp M₃) (M₁.seqComp (M₂.seqComp M₃)) := by
  intro input
  simp only [denote_seqComp]
  calc
    _ = Resumption.bind (M₁.denote input)
        (fun value => Resumption.bind (M₂.denote value) M₃.denote) :=
      Resumption.bind_assoc (M₁.denote input) M₂.denote M₃.denote
    _ = Resumption.bind (M₁.denote input) (M₂.seqComp M₃).denote := by
      apply congrArg (Resumption.bind (M₁.denote input))
      funext value
      exact (denote_seqComp M₂ M₃ value).symm

/-- An immediate first computation is observationally input substitution. -/
theorem ofFn_seqComp_obsEq {γ : Type uγ} (f : α → β)
    (M : DynComputation.{u} p β γ) :
    ObsEq ((ofFn (p := p) f).seqComp M) (M.contramapInput f) := by
  intro input
  simp only [denote_seqComp, denote_ofFn, Resumption.bind_pure_left,
    contramapInput_denote]

/-- An immediate second computation is observationally result mapping. -/
theorem seqComp_ofFn_obsEq {γ : Type uγ} (M : DynComputation.{u} p α β)
    (f : β → γ) :
    ObsEq (M.seqComp (ofFn (p := p) f)) (M.mapResult f) := by
  intro input
  simp only [denote_seqComp, mapResult_denote, Resumption.map]
  apply congrArg (Resumption.bind (M.denote input))
  funext value
  exact denote_ofFn f value

/-! ## Resumption realizations -/

/-- Realize a family of resumptions directly, using the resumption itself as
the hidden state. This is the canonical (generally infinite-state) realization
of state-free resumption semantics. -/
def ofResumption (semantics : α → Resumption p β) : DynComputation p α β where
  State := Resumption p β
  toDynSystem := (fun state => (M.dest state).1) ⇆ fun state => (M.dest state).2
  init := semantics

@[simp] theorem ofResumption_State (semantics : α → Resumption p β) :
    (ofResumption semantics).State = Resumption p β := rfl

@[simp] theorem ofResumption_init (semantics : α → Resumption p β) (input : α) :
    (ofResumption semantics).init input = semantics input := rfl

@[simp] theorem view_ofResumption (semantics : α → Resumption p β)
    (state : Resumption p β) :
    (ofResumption semantics).view state = Resumption.dest state := by
  unfold view ofResumption Resumption.dest
  rfl

@[simp] theorem denote_ofResumption (semantics : α → Resumption p β) (input : α) :
    (ofResumption semantics).denote input = semantics input := by
  unfold denote ofResumption
  exact M.corec_dest _

/-! ## Well-founded free programs -/

/-- Realize an input-indexed family of well-founded free programs as a returning
dynamical computation whose states are the residual programs. -/
def ofFreeM (program : α → FreeM p β) : DynComputation p α β where
  State := FreeM p β
  toDynSystem :=
    (fun
      | .pure value => Sum.inl value
      | .liftBind position _ => Sum.inr position) ⇆
    fun state => match state with
      | .pure _ => PEmpty.elim
      | .liftBind _ next => next
  init := program

@[simp] theorem ofFreeM_State (program : α → FreeM p β) :
    (ofFreeM program).State = FreeM p β := rfl

@[simp] theorem ofFreeM_init (program : α → FreeM p β) (input : α) :
    (ofFreeM program).init input = program input := rfl

@[simp] theorem view_ofFreeM_pure (program : α → FreeM p β) (value : β) :
    (ofFreeM program).view (pure value) = Sum.inl value := rfl

@[simp] theorem view_ofFreeM_liftBind (program : α → FreeM p β)
    (position : p.A) (next : p.B position → FreeM p β) :
    (ofFreeM program).view ((FreeM.lift position).bind next) =
      Sum.inr ⟨position, next⟩ := rfl

/-- `ofFreeM` has exactly the tau-free resumption semantics of its source
program. -/
@[simp] theorem denote_ofFreeM (program : α → FreeM p β) (input : α) :
    (ofFreeM program).denote input = FreeM.toResumption (program input) := by
  let machine := (ofFreeM program).toDynSystem
  have hsem : FreeM.toResumption = machine.behavior := by
    apply DynSystem.behavior_unique machine
    intro state
    cases state with
    | pure value =>
        simp only [FreeM.toResumption, Resumption.pure, M.dest_mk]
        change ⟨Sum.inl value, PEmpty.elim⟩ =
          (C β + p).map FreeM.toResumption ⟨Sum.inl value, PEmpty.elim⟩
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext direction
          exact PEmpty.elim direction
    | liftBind position next =>
        simp only [FreeM.toResumption, Resumption.query, M.dest_mk]
        change ⟨Sum.inr position, fun direction => FreeM.toResumption (next direction)⟩ =
          (C β + p).map FreeM.toResumption ⟨Sum.inr position, next⟩
        rfl
  exact (congrFun hsem (program input)).symm

/-- Qualitative semantic correctness of a returning dynamical computation
with respect to a well-founded free program. Resource bounds are deliberately not
part of this predicate. -/
def Implements (M : DynComputation p α β) (program : α → FreeM p β) : Prop :=
  ∀ input, M.denote input = FreeM.toResumption (program input)

/-- Two realizations of the same well-founded program family are observationally
equivalent, even when their hidden state types differ. -/
theorem ObsEq.of_implements {M : DynComputation.{u} p α β}
    {N : DynComputation.{v} p α β} {program : α → FreeM p β}
    (hM : M.Implements program) (hN : N.Implements program) : ObsEq M N :=
  fun input => (hM input).trans (hN input).symm

/-- Observationally equivalent computations implement exactly the same well-founded
program families. -/
theorem ObsEq.implements_iff {M : DynComputation.{u} p α β}
    {N : DynComputation.{v} p α β} (h : ObsEq M N) (program : α → FreeM p β) :
    M.Implements program ↔ N.Implements program := by
  constructor
  · intro hM input
    exact (h input).symm.trans (hM input)
  · intro hN input
    exact (h input).trans (hN input)

/-- Qualitative implementation is contravariant in the input type. -/
theorem Implements.contramapInput {M : DynComputation.{u} p α β}
    {program : α → FreeM p β} (h : M.Implements program)
    {γ : Type uγ} (f : γ → α) :
    (M.contramapInput f).Implements (program ∘ f) := by
  intro input
  exact h (f input)

/-- Mapping returned values transports qualitative implementation. -/
theorem Implements.mapResult {M : DynComputation.{u} p α β}
    {program : α → FreeM p β} (h : M.Implements program)
    {γ : Type uγ} (f : β → γ) :
    (M.mapResult f).Implements (fun input => FreeM.map f (program input)) := by
  intro input
  simp only [mapResult_denote, h input, FreeM.toResumption_map]

/-- Simultaneous input and result variance transports qualitative
implementation. -/
theorem Implements.dimap {M : DynComputation.{u} p α β}
    {program : α → FreeM p β} (h : M.Implements program)
    {γ : Type uγ} {δ : Type uδ} (f : γ → α) (g : β → δ) :
    (M.dimap f g).Implements
      (fun input => FreeM.map g (program (f input))) := by
  intro input
  simp only [dimap_denote, h (f input), FreeM.toResumption_map]

/-- Interface transport along a lens preserves qualitative implementation. -/
theorem Implements.wrap {M : DynComputation.{u} p α β}
    {program : α → FreeM p β} (h : M.Implements program)
    {q : PFunctor.{uA₂, uB₂}} (lens : Lens p q) :
    (M.wrap lens).Implements (fun input => (program input).mapLens lens) := by
  intro input
  simp only [wrap_denote, h input, FreeM.toResumption_mapLens]

/-- Sequentially composing qualitative implementations implements free-monad
bind, with the intermediate value selecting the second program. -/
theorem Implements.seqComp {γ : Type uγ}
    {M₁ : DynComputation.{u} p α β} {M₂ : DynComputation.{v} p β γ}
    {program₁ : α → FreeM p β} {program₂ : β → FreeM p γ}
    (h₁ : M₁.Implements program₁) (h₂ : M₂.Implements program₂) :
    (M₁.seqComp M₂).Implements
      (fun input => FreeM.bind (program₁ input) program₂) := by
  intro input
  rw [denote_seqComp, h₁ input]
  calc
    Resumption.bind (FreeM.toResumption (program₁ input)) M₂.denote =
        Resumption.bind (FreeM.toResumption (program₁ input))
          (fun value => FreeM.toResumption (program₂ value)) := by
      apply congrArg (Resumption.bind (FreeM.toResumption (program₁ input)))
      funext value
      exact h₂ value
    _ = FreeM.toResumption (FreeM.bind (program₁ input) program₂) :=
      (FreeM.toResumption_bind (program₁ input) program₂).symm

@[simp] theorem implements_ofFreeM (program : α → FreeM p β) :
    Implements (ofFreeM program) program :=
  denote_ofFreeM program

@[simp] theorem implements_ofResumption (program : α → FreeM p β) :
    Implements (ofResumption fun input => FreeM.toResumption (program input)) program :=
  denote_ofResumption _

/-- A synchronized state simulation from a dynamical implementation to the
canonical residual-program realization proves qualitative implementation. -/
theorem implements_of_isSimulation (M : DynComputation p α β)
    (program : α → FreeM p β) (R : M.State → FreeM p β → Prop)
    (simulation : IsSimulation M.toDynSystem (ofFreeM program).toDynSystem R)
    (init_rel : ∀ input, R (M.init input) (program input)) :
    M.Implements program := by
  intro input
  rw [← denote_ofFreeM program input]
  exact behavior_eq_of_isSimulation simulation (init_rel input)

end DynComputation

end DynSystem

end PFunctor

/-- Locally scoped notation for qualitative implementation of a well-founded free
program. The turnstile-style symbol follows the common model-satisfaction
notation used for semantic realization judgments. -/
scoped[PFunctor.DynComputation] infix:50 " ⊨ " =>
  PFunctor.DynSystem.DynComputation.Implements
