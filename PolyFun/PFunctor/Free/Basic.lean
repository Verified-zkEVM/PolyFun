/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/
module

public import PolyFun.Control.Monad.Hom
public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.Lens.Basic

/-!
# Free Monad of a Polynomial Functor

We define the free monad on a **polynomial functor** (`PFunctor`), and prove some basic properties.

-/

@[expose] public section

/--
Simp set for structurally unfolding `FreeM` and displayed-family operations.

This set is reserved for one-way unfolding lemmas: constructor equations for
`FreeM` operations, displayed-family operations, and local-hom recursion through
`roll`. Folding and normalization lemmas should not be tagged with this
attribute.
-/
register_simp_attr freeM_unfold

universe u v uA uB uA₂ uB₂ uA₃ uB₃

namespace PFunctor

/-- The free monad on a polynomial functor.
This extends the `W`-type construction with an extra `pure` constructor. -/
inductive FreeM (P : PFunctor.{uA, uB}) : Type v → Type (max uA uB v)
  | pure {α} (x : α) : FreeM P α
  | roll {α} (a : P.A) (r : P.B a → FreeM P α) : FreeM P α
deriving Inhabited

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α β γ : Type v}

/-- Forward direction of the equivalence with `P.W` when the leaf type is empty: every `pure`
case is unreachable, and every `roll` is reinterpreted as a W-node. -/
def toW [IsEmpty α] : FreeM P α → P.W
  | .pure y   => (IsEmpty.false y).elim
  | .roll a r => ⟨a, fun b => toW (r b)⟩

/-- Inverse direction of the equivalence with `P.W` when the leaf type is empty: every W-node
becomes a `roll`. -/
def ofW [IsEmpty α] : P.W → FreeM P α
  | ⟨a, f⟩ => FreeM.roll a (fun b => ofW (f b))

/-- When the value type is empty, every `pure` is unreachable and `FreeM P α` is structurally
identical to `P.W`. -/
def equivWOfIsEmpty [IsEmpty α] : FreeM P α ≃ P.W where
  toFun := toW
  invFun := ofW
  left_inv x := by
    induction x with
    | pure y => exact (IsEmpty.false y).elim
    | roll a r ih => exact congrArg (FreeM.roll a) (funext ih)
  right_inv w := by
    induction w with
    | mk a f ih => exact congrArg (WType.mk a) (funext ih)

/-- Lift an object of the base polynomial functor into the free monad. -/
@[always_inline, inline, reducible]
def lift (x : P.Obj α) : FreeM P α := FreeM.roll x.1 (fun y ↦ FreeM.pure (x.2 y))

/-- Lift a position of the base polynomial functor into the free monad. -/
@[always_inline, inline, reducible]
def liftA (a : P.A) : FreeM P (P.B a) := lift ⟨a, id⟩

instance : MonadLift P (FreeM P) where
  monadLift x := FreeM.lift x

@[simp] lemma lift_ne_pure (x : P α) (y : α) :
    (lift x : FreeM P α) ≠ PFunctor.FreeM.pure y := by simp [lift]

@[simp] lemma pure_ne_lift (x : P α) (y : α) :
    PFunctor.FreeM.pure y ≠ (lift x : FreeM P α) := by simp [lift]

-- @[simp]
lemma monadLift_eq_lift (x : P.Obj α) : (x : FreeM P α) = FreeM.lift x := rfl

/-- Bind operator on `FreeM P` operation used in the monad definition. -/
@[always_inline, inline]
protected def bind : FreeM P α → (α → FreeM P β) → FreeM P β
  | FreeM.pure x, g => g x
  | FreeM.roll x r, g => FreeM.roll x (fun u ↦ FreeM.bind (r u) g)

@[simp]
lemma bind_pure (x : α) (r : α → FreeM P β) :
    FreeM.bind (FreeM.pure x) r = r x := rfl

@[simp]
lemma bind_roll (a : P.A) (r : P.B a → FreeM P β) (g : β → FreeM P γ) :
    FreeM.bind (FreeM.roll a r) g = FreeM.roll a (fun u ↦ FreeM.bind (r u) g) := rfl

@[simp]
lemma bind_lift (x : P.Obj α) (r : α → FreeM P β) :
    FreeM.bind (FreeM.lift x) r = FreeM.roll x.1 (fun a ↦ r (x.2 a)) := rfl

@[simp] lemma bind_eq_pure_iff (x : FreeM P α) (y : α → FreeM P β) (y' : β) :
    FreeM.bind x y = FreeM.pure y' ↔ ∃ x', x = pure x' ∧ y x' = pure y' := by
  cases x <;> simp

@[simp] lemma pure_eq_bind_iff (x : FreeM P α) (y : α → FreeM P β) (y' : β) :
    FreeM.pure y' = FreeM.bind x y ↔ ∃ x', x = pure x' ∧ pure y' = y x' := by
  cases x <;> simp

instance : Monad (FreeM P) where
  pure := FreeM.pure
  bind := FreeM.bind

lemma monad_bind_def (x : FreeM P α) (g : α → FreeM P β) :
    x >>= g = FreeM.bind x g := rfl

instance : LawfulMonad (FreeM P) :=
  LawfulMonad.mk' (FreeM P)
    (fun x ↦ by
      induction x with
      | pure _ => rfl
      | roll a _ h => refine congr_arg (FreeM.roll a) (funext fun i ↦ h i))
    (fun x f ↦ rfl)
    (fun x f g ↦ by
      induction x with
      | pure _ => rfl
      | roll a _ h => refine congr_arg (FreeM.roll a) (funext fun i ↦ h i))

lemma pure_inj (x y : α) : FreeM.pure (P := P) x = FreeM.pure y ↔ x = y := by simp

lemma roll_inj (x x' : P.A) (y : P.B x → P.FreeM α) (y' : P.B x' → P.FreeM α) :
    FreeM.roll x y = FreeM.roll x' y' ↔ ∃ h : x = x', h ▸ y = y' := by
  simp only [FreeM.roll.injEq]
  by_cases hx : x = x'
  · cases hx
    simp
  · simp [hx]

section mapLens

variable {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- Transport a free polynomial tree along a polynomial lens.

The source polynomial `P` is the abstract/control interface. The target
polynomial `Q` is the concrete/runtime interface. At each `P`-node, the lens
chooses a `Q`-position by `toFunA`; when runtime supplies a `Q`-direction,
`toFunB` maps it back to the corresponding `P`-direction selecting the
control continuation. -/
protected def mapLens (l : Lens P Q) : FreeM P α → FreeM Q α
  | .pure x => .pure x
  | .roll a rest => .roll (l.toFunA a) fun d =>
      (rest (l.toFunB a d)).mapLens l

@[simp]
theorem mapLens_pure (l : Lens P Q) (x : α) :
    (FreeM.pure x : FreeM P α).mapLens l = FreeM.pure x :=
  rfl

@[simp]
theorem mapLens_roll (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) :
    (FreeM.roll a rest).mapLens l =
      FreeM.roll (l.toFunA a) (fun d => (rest (l.toFunB a d)).mapLens l) :=
  rfl

@[simp]
theorem mapLens_id (x : FreeM P α) :
    x.mapLens (Lens.id P) = x := by
  induction x with
  | pure _ => rfl
  | roll a rest ih =>
      exact congrArg (FreeM.roll a) (funext ih)

@[simp]
theorem mapLens_comp (l₂ : Lens Q R) (l₁ : Lens P Q) (x : FreeM P α) :
    (x.mapLens l₁).mapLens l₂ = x.mapLens (l₂ ∘ₗ l₁) := by
  induction x with
  | pure _ => rfl
  | roll a rest ih =>
      exact congrArg (FreeM.roll (l₂.toFunA (l₁.toFunA a))) (funext fun d => ih _)

@[simp]
theorem mapLens_bind (l : Lens P Q) (x : FreeM P α) (f : α → FreeM P β) :
    (FreeM.bind x f).mapLens l =
      FreeM.bind (x.mapLens l) (fun a => (f a).mapLens l) := by
  induction x with
  | pure _ => rfl
  | roll a rest ih =>
      exact congrArg (FreeM.roll (l.toFunA a)) (funext fun d => ih _)

@[simp]
theorem mapLens_bind' (l : Lens P Q) (x : FreeM P α) (f : α → FreeM P β) :
    (x >>= f).mapLens l =
      x.mapLens l >>= fun a => (f a).mapLens l :=
  mapLens_bind l x f

end mapLens

/-- Proving a predicate `C` of `FreeM P α` requires two cases:
* `pure x` for some `x : α`
* `roll x r h` for some `x : P.A`, `r : P.B x → FreeM P α`, and `h : ∀ y, C (r y)`
Note that we can't use `Sort v` instead of `Prop` due to universe levels. -/
@[elab_as_elim]
protected theorem inductionOn {C : FreeM P α → Prop}
    (pure : ∀ x, C (pure x))
    (roll : (x : P.A) → (r : P.B x → FreeM P α) → (∀ y, C (r y)) → C (FreeM.roll x r)) :
    (oa : FreeM P α) → C oa
  | FreeM.pure x => pure x
  | FreeM.roll x r => roll x _ (fun u ↦ FreeM.inductionOn pure roll (r u))

section construct

/-- Shoulde be possible to unify with the above -/
@[elab_as_elim]
protected def construct {C : FreeM P α → Type*}
    (pure : (x : α) → C (pure x))
    (roll : (x : P.A) → (r : P.B x → FreeM P α) → ((y : P.B x) → C (r y)) → C (FreeM.roll x r)) :
    (oa : FreeM P α) → C oa
  | .pure x => pure x
  | .roll x r => roll x _ (fun u ↦ FreeM.construct pure roll (r u))

variable {C : FreeM P α → Type*} (h_pure : (x : α) → C (pure x))
  (h_roll : (x : P.A) → (r : P.B x → FreeM P α) → ((y : P.B x) → C (r y)) → C (FreeM.roll x r))

@[simp]
lemma construct_pure (y : α) : FreeM.construct h_pure h_roll (pure y) = h_pure y := rfl

@[simp]
lemma construct_roll (x : P.A) (r : P.B x → FreeM P α) :
    (FreeM.construct h_pure h_roll (FreeM.roll x r) : C (FreeM.roll x r)) =
      (h_roll x r (fun u => FreeM.construct h_pure h_roll (r u))) := rfl

end construct

section mapM

variable {m : Type uB → Type v} {α : Type uB}

/-- Canonical mapping of `FreeM P` into any other monad, given a map `s : (a : P.A) → m (P.B a)`. -/
protected def mapM [Pure m] [Bind m] (s : (a : P.A) → m (P.B a)) : FreeM P α → m α
  | .pure a => Pure.pure a
  | .roll a r => (s a) >>= (fun u ↦ (r u).mapM s)

variable [Monad m] (s : (a : P.A) → m (P.B a))

@[simp]
lemma mapM_pure' (x : α) : (FreeM.pure x : FreeM P α).mapM s = Pure.pure x := rfl

@[simp]
lemma mapM_roll (x : P.A) (r : P.B x → FreeM P α) :
    (FreeM.roll x r).mapM s = s x >>= fun u => (r u).mapM s := rfl

@[simp] lemma mapM_pure (x : α) : (Pure.pure x : FreeM P α).mapM s = Pure.pure x := rfl

variable [LawfulMonad m]

@[simp]
lemma mapM_bind {α β} (x : FreeM P α) (y : α → FreeM P β) :
    (FreeM.bind x y).mapM s = x.mapM s >>= fun u => (y u).mapM s := by
  induction x using FreeM.inductionOn with
  | pure _ => simp
  | roll x r h => simp [h]

@[simp]
lemma mapM_bind' {α β} (x : FreeM P α) (y : α → FreeM P β) :
    (x >>= y).mapM s = x.mapM s >>= fun u => (y u).mapM s :=
  mapM_bind _ _ _

@[simp]
lemma mapM_map {α β} (x : FreeM P α) (f : α → β) :
    FreeM.mapM s (f <$> x) = f <$> FreeM.mapM s x := by
  simp [← bind_pure_comp]

@[simp]
lemma mapM_seq {α β}
    (s : (a : P.A) → m (P.B a)) (x : FreeM P (α → β)) (y : FreeM P α) :
    FreeM.mapM s (x <*> y) = (FreeM.mapM s x) <*> (FreeM.mapM s y) := by
  simp [monad_norm]

lemma mapM_lift (s : (a : P.A) → m (P.B a)) (x : P.Obj α) :
    FreeM.mapM s (FreeM.lift x) = s x.1 >>= (fun u ↦ (pure (x.2 u)).mapM s) := by
  simp [FreeM.mapM]

lemma mapM_liftA (s : (a : P.A) → m (P.B a)) (x : P.A) :
    FreeM.mapM s (FreeM.liftA x) = s x := by simp [liftA]

/-- `FreeM.mapM` as a monad homomorphism. -/
protected def mapMHom (s : (a : P.A) → m (P.B a)) : FreeM P →ᵐ m where
  toFun _ := FreeM.mapM s
  toFun_pure' x := rfl
  toFun_bind' x y := by
    induction x using FreeM.inductionOn <;> simp [FreeM.mapM, FreeM.monad_bind_def]

@[simp] lemma mapMHom_toFun_eq (s : (a : P.A) → m (P.B a)) :
    ((FreeM.mapMHom s).toFun α) = FreeM.mapM s := rfl

/-- `FreeM.mapM` as a monad homomorphism, packaging the interpretation of
positions as a natural transformation `NatHom P.Obj m`. -/
protected def mapMHom' (s : NatHom P.Obj m) : FreeM P →ᵐ m where
  toFun _ := FreeM.mapM (fun t => s ⟨t, id⟩)
  toFun_pure' x := by simp --[FreeM.mapM]
  toFun_bind' x y := by
    induction x using FreeM.inductionOn <;> simp [FreeM.mapM, FreeM.monad_bind_def]

@[simp] lemma mapMHom'_toFun_eq (s : NatHom P.Obj m) :
    (FreeM.mapMHom' s).toFun α = FreeM.mapM (fun t => s ⟨t, id⟩) := rfl

/-! ## Universal property and naturality of the fold

`FreeM.mapM s` is the universal fold: the *unique* monad homomorphism out of `FreeM P` extending a
handler `s` (`mapMHom_unique`), and it is *natural* in the target monad — post-composing with a
monad morphism `φ : m →ᵐ n` is the fold of the post-composed handler (`mapM_natural`,
`mapMHom_comp`). This is the freeness of `FreeM P`; downstream it lets a semantic monad morphism
(e.g. an evaluation-distribution map) be pushed through a fold uniformly, rather than re-run by
induction per interpretation. -/

variable {n : Type uB → Type u} [Monad n] [LawfulMonad n]

/-- **Universal property of `FreeM.mapM`** (freeness of `FreeM P`): a monad homomorphism out of
`FreeM P` is determined by its action on generators. If `F : FreeM P →ᵐ m` agrees with `s` on every
`FreeM.liftA a`, then `F = FreeM.mapMHom s`. So handlers `(a : P.A) → m (P.B a)` are in bijection
with monad homomorphisms `FreeM P →ᵐ m` — the universal property behind `simulateQ`. -/
theorem mapMHom_unique (F : FreeM P →ᵐ m) (h : ∀ a, F (FreeM.liftA a) = s a) :
    F = FreeM.mapMHom s := by
  refine MonadHom.ext' fun β x => ?_
  induction x with
  | pure x => exact F.mmap_pure x
  | roll a r ih =>
    change F (FreeM.roll a r) = FreeM.mapM s (FreeM.roll a r)
    rw [mapM_roll, show (FreeM.roll a r : FreeM P β) = FreeM.liftA a >>= r from rfl,
      MonadHom.mmap_bind, h]
    exact bind_congr fun d => ih d

omit [LawfulMonad m] [LawfulMonad n] in
/-- **Naturality of the fold along a monad morphism**: pushing a monad morphism `φ : m →ᵐ n` through
`FreeM.mapM s` is the fold of the post-composed handler `fun a => φ (s a)` — the value-level
naturality square of the universal fold. -/
@[simp] theorem mapM_natural (φ : m →ᵐ n) (x : FreeM P α) :
    φ (FreeM.mapM s x) = FreeM.mapM (fun a => φ (s a)) x := by
  induction x with
  | pure x => exact φ.mmap_pure x
  | roll a r ih => simp only [mapM_roll, MonadHom.mmap_bind, ih]

/-- Bundled form of `mapM_natural`: composing the fold monad-homomorphism `FreeM.mapMHom s` with a
monad morphism `φ` is the fold of the post-composed handler. -/
theorem mapMHom_comp (φ : m →ᵐ n) :
    φ ∘ₘ FreeM.mapMHom s = FreeM.mapMHom (fun a => φ (s a)) :=
  MonadHom.ext' fun β x => by simp only [MonadHom.comp_apply, mapMHom_toFun_eq, mapM_natural]

end mapM

section stateNaturality

variable {m : Type uB → Type v} {n : Type uB → Type u} [Monad m] [Monad n] {σ : Type uB}
  {α : Type uB}

/-- **Stateful naturality of the fold**: running a fold whose stateful handler is post-composed by
a `StateT`-lifted monad morphism `StateT.mapHom φ` is `φ` applied to the run of the original fold —
the shape a `StateT`-threaded semantic morphism (e.g. an evaluation-distribution map through a
stateful handler) instantiates, collapsing a per-interpretation induction to one use of
`mapM_natural`. -/
theorem run_mapM_mapHom (φ : m →ᵐ n) (impl : (a : P.A) → StateT σ m (P.B a))
    (x : FreeM P α) (s : σ) :
    (FreeM.mapM (fun a => StateT.mapHom φ (impl a)) x).run s = φ ((FreeM.mapM impl x).run s) := by
  rw [← mapM_natural impl (StateT.mapHom φ) x, StateT.run_mapHom]

end stateNaturality

section idFold

variable {α : Type uB}

/-- The fold with the canonical re-lifting handler `FreeM.liftA` is the identity: interpreting each
position back into the free monad recovers the tree (equivalently `FreeM.mapMHom FreeM.liftA` is the
identity homomorphism, `mapMHom_liftA`). The upstream form of `simulateQ` of the identity handler
being the identity — a corollary of the universal property. -/
@[simp] theorem mapM_liftA_eq_self (x : FreeM P α) : FreeM.mapM FreeM.liftA x = x := by
  induction x with
  | pure y => rfl
  | roll a r ih =>
    rw [mapM_roll]
    change FreeM.roll a (fun u => FreeM.mapM FreeM.liftA (r u)) = FreeM.roll a r
    exact congrArg (FreeM.roll a) (funext ih)

theorem mapMHom_liftA : FreeM.mapMHom (P := P) (m := FreeM P) FreeM.liftA = MonadHom.id (FreeM P) :=
  MonadHom.ext' fun _ x => by simp

end idFold

end FreeM

end PFunctor
