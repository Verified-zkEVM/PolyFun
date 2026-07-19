/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/
module

public import PolyFun.Control.Monad.Hom
public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.Lens.Basic
public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Free Monad of a Polynomial Functor

We define the free monad on a **polynomial functor** (`PFunctor`), and prove some basic properties.

-/

@[expose] public section

/--
Simp set for structurally unfolding `FreeM` and displayed-family operations.

This set is reserved for one-way unfolding lemmas: constructor equations for
`FreeM` operations, displayed-family operations, and local-hom recursion through
`liftBind`. Folding and normalization lemmas should not be tagged with this
attribute.
-/
register_simp_attr freeM_unfold

universe u v uA uB uA₂ uB₂ uA₃ uB₃ uδ uβ uγ

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α β γ : Type v}

/-- Test only the root of a free polynomial tree.

A leaf demands `leafPred` of its result, while an internal node demands
`positionPred` of its exposed position. This deliberately does not recurse
into the continuations; callers can quantify over paths or cursors when they
need a whole-tree property. -/
def RootSatisfies (positionPred : P.A → Prop) (leafPred : α → Prop) :
    FreeM P α → Prop
  | .pure result => leafPred result
  | .liftBind position _ => positionPred position

@[simp]
theorem rootSatisfies_pure (positionPred : P.A → Prop) (leafPred : α → Prop)
    (result : α) :
    RootSatisfies positionPred leafPred (pure result : FreeM P α) =
      leafPred result :=
  rfl

@[simp]
theorem rootSatisfies_liftBind (positionPred : P.A → Prop) (leafPred : α → Prop)
    (position : P.A) (next : P.B position → FreeM P α) :
    RootSatisfies positionPred leafPred
        ((FreeM.lift (P := P) position).bind next) =
      positionPred position :=
  rfl

/-- Forward direction of the equivalence with `P.W` when the leaf type is empty: every `pure`
case is unreachable, and every `liftBind` is reinterpreted as a W-node. -/
def toW [IsEmpty α] : FreeM P α → P.W
  | .pure y   => (IsEmpty.false y).elim
  | .liftBind a r => ⟨a, fun b => toW (r b)⟩

/-- Inverse direction of the equivalence with `P.W` when the leaf type is empty: every W-node
becomes a `liftBind`. -/
def ofW [IsEmpty α] : P.W → FreeM P α
  | ⟨a, f⟩ => FreeM.liftBind a (fun b => ofW (f b))

/-- When the value type is empty, every `pure` is unreachable and `FreeM P α` is structurally
identical to `P.W`. -/
def equivWOfIsEmpty [IsEmpty α] : FreeM P α ≃ P.W where
  toFun := toW
  invFun := ofW
  left_inv x := by
    induction x with
    | pure y => exact (IsEmpty.false y).elim
    | lift_bind a r ih => exact congrArg (FreeM.liftBind a) (funext ih)
  right_inv w := by
    induction w with
    | mk a f ih => exact congrArg (WType.mk a) (funext ih)

lemma monad_bind_def (x : FreeM P α) (g : α → FreeM P β) :
    x >>= g = FreeM.bind x g := rfl

/-- Mapping after a free-monad bind can be moved into each continuation. -/
theorem bind_map_right {δ : Type uδ} {β : Type uβ} {γ : Type uγ}
    (mx : FreeM P δ) (g : δ → FreeM P β) (f : β → γ) :
    FreeM.bind mx (fun x => FreeM.map f (g x)) =
      FreeM.map f (FreeM.bind mx g) := by
  simpa only [FreeM.bind_pure_comp] using
    (FreeM.bind_assoc mx g (pure ∘ f)).symm

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
  | .liftBind a rest => .liftBind (l.toFunA a) fun d =>
      (rest (l.toFunB a d)).mapLens l

@[simp]
theorem mapLens_pure (l : Lens P Q) (x : α) :
    (pure x : FreeM P α).mapLens l = FreeM.pure x :=
  rfl

@[simp]
theorem mapLens_lift_bind (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) :
    ((FreeM.lift a).bind rest).mapLens l =
      FreeM.liftBind (l.toFunA a) (fun d => (rest (l.toFunB a d)).mapLens l) := rfl

@[simp]
theorem mapLens_id (x : FreeM P α) :
    x.mapLens (Lens.id P) = x := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih => exact congrArg (FreeM.liftBind a) (funext ih)

@[simp]
theorem mapLens_comp (l₂ : Lens Q R) (l₁ : Lens P Q) (x : FreeM P α) :
    (x.mapLens l₁).mapLens l₂ = x.mapLens (l₂ ∘ₗ l₁) := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih =>
      exact congrArg (FreeM.liftBind (l₂.toFunA (l₁.toFunA a))) (funext fun d => ih _)

theorem mapLens_bind (l : Lens P Q) (x : FreeM P α) (f : α → FreeM P β) :
    (FreeM.bind x f).mapLens l =
      FreeM.bind (x.mapLens l) (fun a => (f a).mapLens l) := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih => exact congrArg (FreeM.liftBind (l.toFunA a)) (funext fun d => ih _)

@[simp]
theorem mapLens_bind' (l : Lens P Q) (x : FreeM P α) (f : α → FreeM P β) :
    (x >>= f).mapLens l = x.mapLens l >>= fun a => (f a).mapLens l := mapLens_bind l x f

end mapLens

section liftM

variable {m : Type uB → Type v} {α : Type uB} [Monad m] [LawfulMonad m]
  (s : (a : P.A) → m (P.B a))

/-- `FreeM.liftM` as a monad homomorphism. -/
protected def liftMHom (s : (a : P.A) → m (P.B a)) : FreeM P →ᵐ m where
  toFun _ x := x.liftM s
  toFun_pure' := FreeM.liftM_pure s
  toFun_bind' := FreeM.liftM_bind s

@[simp] lemma liftMHom_toFun_eq (s : (a : P.A) → m (P.B a)) :
    ((FreeM.liftMHom s).toFun α) = fun x => x.liftM s := rfl

/-- `FreeM.liftM` as a monad homomorphism, packaging the interpretation of
positions as a natural transformation `NatHom P.Obj m`. -/
protected def liftMHom' (s : NatHom P.Obj m) : FreeM P →ᵐ m where
  toFun _ x := x.liftM (fun t => s ⟨t, id⟩)
  toFun_pure' _ := rfl
  toFun_bind' x y := FreeM.liftM_bind _ x y

@[simp] lemma liftMHom'_toFun_eq (s : NatHom P.Obj m) :
    (FreeM.liftMHom' s).toFun α = fun x => x.liftM (fun t => s ⟨t, id⟩) := rfl

/-! ## Universal property and naturality of the fold

`FreeM.liftM s` is the universal fold: the *unique* monad homomorphism out of `FreeM P` extending a
handler `s` (`liftMHom_unique`), and it is *natural* in the target monad — post-composing with a
monad morphism `φ : m →ᵐ n` is the fold of the post-composed handler (`liftM_natural`,
`liftMHom_comp`). This is the freeness of `FreeM P`; downstream it lets a semantic monad morphism
(e.g. an evaluation-distribution map) be pushed through a fold uniformly, rather than re-run by
induction per interpretation. -/

variable {n : Type uB → Type u} [Monad n] [LawfulMonad n]

/-- **Universal property of `FreeM.liftM`** (freeness of `FreeM P`): a monad homomorphism out of
`FreeM P` is determined by its action on generators. If `F : FreeM P →ᵐ m` agrees with `s` on every
`FreeM.lift a`, then `F = FreeM.liftMHom s`. So handlers `(a : P.A) → m (P.B a)` are in bijection
with monad homomorphisms `FreeM P →ᵐ m` — the universal property behind `simulateQ`. -/
theorem liftMHom_unique (F : FreeM P →ᵐ m) (h : ∀ a, F (FreeM.lift a) = s a) :
    F = FreeM.liftMHom s := by
  refine MonadHom.ext' fun β x => ?_
  induction x with
  | pure x => exact F.mmap_pure x
  | lift_bind a r ih =>
    change F (FreeM.liftBind a r) = FreeM.liftM s (FreeM.liftBind a r)
    rw [show (FreeM.liftBind a r : FreeM P β) = FreeM.lift a >>= r from rfl,
      MonadHom.mmap_bind, h, FreeM.liftM_lift_bind]
    exact bind_congr fun d => ih d

omit [LawfulMonad m] [LawfulMonad n] in
/-- **Naturality of the fold along a monad morphism**: pushing a monad morphism `φ : m →ᵐ n` through
`FreeM.liftM s` is the fold of the post-composed handler `fun a => φ (s a)` — the value-level
naturality square of the universal fold. -/
@[simp] theorem liftM_natural (φ : m →ᵐ n) (x : FreeM P α) :
    φ (FreeM.liftM s x) = FreeM.liftM (fun a => φ (s a)) x := by
  induction x with
  | pure x => exact φ.mmap_pure x
  | lift_bind a r ih => simp [ih]

/-- Bundled form of `liftM_natural`: composing the fold monad-homomorphism `FreeM.liftMHom s` with
a monad morphism `φ` is the fold of the post-composed handler. -/
theorem liftMHom_comp (φ : m →ᵐ n) :
    φ ∘ₘ FreeM.liftMHom s = FreeM.liftMHom (fun a => φ (s a)) :=
  MonadHom.ext' fun β x => by simp

end liftM

section stateNaturality

variable {m : Type uB → Type v} {n : Type uB → Type u} [Monad m] [Monad n] {σ : Type uB}
  {α : Type uB}

/-- **Stateful naturality of the fold**: running a fold whose stateful handler is post-composed by
a `StateT`-lifted monad morphism `StateT.mapHom φ` is `φ` applied to the run of the original fold —
the shape a `StateT`-threaded semantic morphism (e.g. an evaluation-distribution map through a
stateful handler) instantiates, collapsing a per-interpretation induction to one use of
`liftM_natural`. -/
theorem run_liftM_mapHom (φ : m →ᵐ n) (impl : (a : P.A) → StateT σ m (P.B a))
    (x : FreeM P α) (s : σ) :
    (FreeM.liftM (fun a => StateT.mapHom φ (impl a)) x).run s =
      φ ((FreeM.liftM impl x).run s) := by
  rw [← liftM_natural impl (StateT.mapHom φ) x, StateT.run_mapHom]

end stateNaturality

section idFold

variable {α : Type uB}

/-- The fold with the canonical re-lifting handler `FreeM.lift` is the identity: interpreting each
position back into the free monad recovers the tree (equivalently `FreeM.liftMHom FreeM.lift` is
the identity homomorphism, `liftMHom_lift_eq_id`). The upstream form of `simulateQ` of the
identity handler being the identity — a corollary of the universal property. -/
@[simp] theorem liftM_lift_eq_self (x : FreeM P α) : FreeM.liftM FreeM.lift x = x := by
  induction x with
  | pure y => rfl
  | lift_bind a r ih => simp [ih]

theorem liftMHom_lift_eq_id :
    FreeM.liftMHom (P := P) (m := FreeM P) FreeM.lift = MonadHom.id (FreeM P) :=
  MonadHom.ext' fun _ x => by simp

/-- Interpreting a free tree by a free handler and then interpreting the
resulting free tree by an arbitrary monadic handler is the same as interpreting
once by their pointwise Kleisli composite. -/
theorem liftM_comp {Q : PFunctor.{uA₂, uB}} {m : Type uB → Type v}
    [Monad m] [LawfulMonad m]
    (x : FreeM P α)
    (first : (a : P.A) → FreeM Q (P.B a))
    (second : (a : Q.A) → m (Q.B a)) :
    (x.liftM first).liftM second =
      x.liftM (fun a => (first a).liftM second) := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih =>
      change
        ((first a >>= fun b => (rest b).liftM first).liftM second) =
          (first a).liftM second >>= fun b =>
            (rest b).liftM (fun a => (first a).liftM second)
      rw [FreeM.liftM_bind]
      exact congrArg (fun k => (first a).liftM second >>= k) (funext ih)

end idFold

end FreeM

end PFunctor
