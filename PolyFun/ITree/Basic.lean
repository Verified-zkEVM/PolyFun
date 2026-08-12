/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.M
public import PolyFun.Control.Monad.Iter

/-! # Interaction Trees

Interaction Trees (ITrees) are a coinductive datatype for representing
recursive and impure programs that interact with an environment through a
fixed set of events. We follow the construction of Xia, Zakowski, He, Hur,
Malecha, Pierce, and Zdancewic, *Interaction Trees: Representing Recursive
and Impure Programs in Coq* (POPL 2020), and adapt it to Lean 4 / Mathlib.

The Coq presentation defines

```coq
CoInductive itree (E : Type → Type) (R : Type) :=
| Ret (r : R) | Tau (t : itree E R) | Vis {X : Type} (e : E X) (k : X → itree E R).
```

In Lean we model the event signature as a *polynomial functor*
`F : PFunctor.{uA, uB}`: its positions are event names and its directions are
answer types. The event-name, answer, and return universes are independent.
For `α : Type uα`, the resulting tree lives in `Type (max uA uB uα)`.
The raw carrier is the M-type (final coalgebra) of the operation-first sum
`Poly F α := F + C α + X`. `ITree F α` is a one-field wrapper around that
carrier, with definitionally inverse `toM` and `ofM` maps. The separate
`ViewPoly F α` presents its layers ergonomically as pure leaves, silent steps,
or visible queries.

## Naming conventions

| Coq                | Lean                                    |
| ------------------ | --------------------------------------- |
| `itree E R`        | `ITree F α`                             |
| `itreeF E R T`     | `ITree.Shape F α`                       |
| `RetF` / `Ret`     | `ITree.Shape.pure` / `ITree.pure`       |
| `TauF` / `Tau`     | `ITree.Shape.step` / `ITree.step`       |
| `VisF` / `Vis`     | `ITree.Shape.query` / `ITree.query`     |
| `observe`          | `ITree.shape`                           |
| `ITree.bind`       | `ITree.bind` (also `>>=`)               |
| `ITree.iter`       | `ITree.iter`                            |
| `ITree.trigger e`  | `ITree.lift`                            |

## Main definitions

* `ITree.Shape F α` — one-step view of an ITree node.
* `ITree.Poly F α` — the raw polynomial `F + C α + X`.
* `ITree.ViewPoly F α` — the `Shape`-indexed ergonomic one-step view.
* `ITree F α` — interaction trees over events `F` with leaves of type `α`.
* `ITree.toM`, `ITree.ofM`, `ITree.equivM` — the raw-carrier equivalence.
* `ITree.pure`, `ITree.step`, `ITree.query` — smart constructors.
* `ITree.shape` — one-step destructor, the analogue of Coq's `observe`.
* `ITree.bind` — monadic bind, defined via `ITree.corec`.
* `ITree.iter` — iteration combinator turning `β → ITree F (β ⊕ α)` into
  `β → ITree F α`, the canonical `MonadIter` operator.
* `ITree.lift` — lift a single event into an ITree: `lift a = query a pure`.
* `Monad (ITree F)`, `MonadIter (ITree F)` — instances built from `bind`,
  `pure`, and `iter`.

## Implementation notes

Lean 4's `coinductive` keyword (v4.25) only builds coinductive *predicates*;
there is no built-in coinductive `Type`. We therefore use `PFunctor.M`, which
is the standard Mathlib coinductive-type construction. The `partial_fixpoint`
machinery is *also* not a substitute, because it requires a `CCPO` on the
return type, which `M F` does not have. Corecursive functions producing
ITrees go through `ITree.corec`, which packages `PFunctor.M.corec` while
presenting coalgebras through `ViewPoly`.
-/

@[expose] public section

universe u uA uB uα uβ uS uT

namespace ITree

/-! ### Carrier and computational-view polynomial functors -/

/-- One-step view of an ITree node: a pure leaf, a silent step, or a visible
query. Mirrors Coq's `itreeF` (`Core/ITreeDefinition.v`). -/
inductive Shape (F : PFunctor.{uA, uB}) (α : Type uα) : Type (max uA uα) where
  /-- A leaf carrying a result of type `α`. (Coq `RetF`.) -/
  | pure (r : α) : Shape F α
  /-- A silent (`τ`) step. (Coq `TauF`.) -/
  | step : Shape F α
  /-- A visible event named by `a : F.A`; the continuation will be indexed by
  `F.B a`. (Coq `VisF`.) -/
  | query (a : F.A) : Shape F α

/-- Computational-view polynomial for one layer of an ITree.

* `A := Shape F α`: which kind of node we are at.
* `B`: the position type encoding the *arity* of each kind of node.
  - `.pure r` has no children (`PEmpty`).
  - `.step` has exactly one child (`PUnit`).
  - `.query a` has children indexed by the answer type `F.B a`. -/
@[reducible]
def ViewPoly (F : PFunctor.{uA, uB}) (α : Type uα) : PFunctor.{max uA uα, uB} where
  A := Shape F α
  B
    | .pure _r => PEmpty.{uB + 1}
    | .step    => PUnit.{uB + 1}
    | .query a => F.B a

/-- The polynomial whose M-type is the raw carrier of `ITree F α`.

Visible queries come first, return leaves second, and silent steps third. This
is definitionally the polynomial expression `F + C α + X`. -/
@[reducible]
def Poly (F : PFunctor.{uA, uB}) (α : Type uα) : PFunctor.{max uA uα, uB} :=
  F + PFunctor.C α + PFunctor.X

/-! ### Raw/computational one-step conversion -/

variable {F : PFunctor.{uA, uB}} {α : Type uα}

/-- Repack an ergonomic `Shape`-based layer as a layer of `F + C α + X`. -/
def pack {X : Type uS} : (ViewPoly F α).Obj X → (Poly F α).Obj X
  | ⟨.pure value, _⟩ => ⟨.inl (.inr value), PEmpty.elim⟩
  | ⟨.step, next⟩ => ⟨.inr PUnit.unit, next⟩
  | ⟨.query position, next⟩ => ⟨.inl (.inl position), next⟩

/-- Unpack a layer of `F + C α + X` into the ergonomic `Shape` view. -/
def unpack {X : Type uS} : (Poly F α).Obj X → (ViewPoly F α).Obj X
  | ⟨.inl (.inl position), next⟩ => ⟨.query position, next⟩
  | ⟨.inl (.inr value), _⟩ => ⟨.pure value, PEmpty.elim⟩
  | ⟨.inr _, next⟩ => ⟨.step, next⟩

@[simp] theorem unpack_pack {X : Type uS} (layer : (ViewPoly F α).Obj X) :
    unpack (pack layer) = layer := by
  rcases layer with ⟨shape, next⟩
  cases shape with
  | pure value => exact Sigma.ext rfl (heq_of_eq (funext fun direction => direction.elim))
  | step => rfl
  | query position => rfl

@[simp] theorem pack_unpack {X : Type uS} (layer : (Poly F α).Obj X) :
    pack (unpack layer) = layer := by
  rcases layer with ⟨shape, next⟩
  rcases shape with ⟨position | value⟩ | step
  · rfl
  · exact Sigma.ext rfl (heq_of_eq (funext fun direction => direction.elim))
  · cases step
    rfl

/-- The raw sum-polynomial layer is equivalent to the ergonomic ITree view. -/
def viewEquiv {X : Type uS} : (Poly F α).Obj X ≃ (ViewPoly F α).Obj X where
  toFun := unpack
  invFun := pack
  left_inv := pack_unpack
  right_inv := unpack_pack

@[simp] theorem unpack_map {X : Type uS} {Y : Type uT} (f : X → Y)
    (layer : (Poly F α).Obj X) :
    unpack ((Poly F α).map f layer) = (ViewPoly F α).map f (unpack layer) := by
  rcases layer with ⟨shape, next⟩
  rcases shape with ⟨position | value⟩ | step
  · rfl
  · exact Sigma.ext rfl (heq_of_eq (funext fun direction => direction.elim))
  · cases step
    rfl

theorem pack_map {X : Type uS} {Y : Type uT} (f : X → Y)
    (layer : (ViewPoly F α).Obj X) :
    pack ((ViewPoly F α).map f layer) = (Poly F α).map f (pack layer) := by
  rcases layer with ⟨shape, next⟩
  cases shape with
  | pure value => exact Sigma.ext rfl (heq_of_eq (funext fun direction => direction.elim))
  | step => rfl
  | query position => rfl

end ITree

/-- Interaction trees over events `F : PFunctor.{uA, uB}` with leaves of type
`α : Type uα`, represented by the final coalgebra (M-type) of
`F + PFunctor.C α + PFunctor.X`.

Event names, event answers, and returned values may live in independent
universes. The resulting tree lives in `Type (max uA uB uα)`.

This is the Lean / Mathlib analogue of Coq's `itree E R`
(`InteractionTrees/theories/Core/ITreeDefinition.v`). -/
structure ITree (F : PFunctor.{uA, uB}) (α : Type uα) : Type (max uA uB uα) where
  /-- Wrap the raw sum-polynomial M-type as an interaction tree. -/
  ofM ::
  /-- The raw M-type representation of an interaction tree. -/
  toM : PFunctor.M (ITree.Poly F α)

namespace ITree

variable {F : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

attribute [local implicit_reducible] PFunctor.Obj

/-! ### Raw M-type equivalence -/

@[simp] theorem ofM_toM (tree : ITree F α) : ofM tree.toM = tree := rfl

@[simp] theorem toM_ofM (tree : PFunctor.M (Poly F α)) : (ofM tree : ITree F α).toM = tree := rfl

theorem toM_injective : Function.Injective (toM : ITree F α → PFunctor.M (Poly F α)) :=
  fun _ _ equality => congrArg ofM equality

@[simp] theorem toM_inj {left right : ITree F α} : left.toM = right.toM ↔ left = right :=
  toM_injective.eq_iff

@[ext] theorem ext {left right : ITree F α} (h : left.toM = right.toM) : left = right :=
  toM_injective h

/-- The equivalence with the raw M-type of `F + C α + X`. Both round trips
hold definitionally by structure eta. -/
def equivM : ITree F α ≃ PFunctor.M (Poly F α) where
  toFun := toM
  invFun := ofM
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equivM_apply (tree : ITree F α) : equivM tree = tree.toM := rfl

@[simp] theorem equivM_symm_apply (tree : PFunctor.M (Poly F α)) :
    equivM.symm tree = (ofM tree : ITree F α) := rfl

/-! ### One-step destructor and constructor -/

/-- One-step observation of an ITree in the ergonomic `Shape` view. -/
def shape' (tree : ITree F α) : (ViewPoly F α).Obj (ITree F α) :=
  (ViewPoly F α).map ofM (unpack (PFunctor.M.dest tree.toM))

/-- Repack an observed ITree layer into the raw sum polynomial. -/
def ofShape (layer : (ViewPoly F α).Obj (ITree F α)) : ITree F α :=
  ofM (PFunctor.M.mk (pack ((ViewPoly F α).map toM layer)))

private theorem viewMap_ofM_toM (layer : (ViewPoly F α).Obj (ITree F α)) :
    (ViewPoly F α).map ofM ((ViewPoly F α).map toM layer) = layer := by
  rcases layer with ⟨shape, next⟩
  cases shape with
  | pure value => exact Sigma.ext rfl (heq_of_eq (funext fun direction => direction.elim))
  | step => exact Sigma.ext rfl (heq_of_eq (funext fun _ => rfl))
  | query position => exact Sigma.ext rfl (heq_of_eq (funext fun _ => rfl))

private theorem viewMap_toM_ofM
    (layer : (ViewPoly F α).Obj (PFunctor.M (Poly F α))) :
    (ViewPoly F α).map toM ((ViewPoly F α).map ofM layer) = layer := by
  rcases layer with ⟨shape, next⟩
  cases shape with
  | pure value => exact Sigma.ext rfl (heq_of_eq (funext fun direction => direction.elim))
  | step => exact Sigma.ext rfl (heq_of_eq (funext fun _ => rfl))
  | query position => exact Sigma.ext rfl (heq_of_eq (funext fun _ => rfl))

@[simp] theorem shape'_ofShape (layer : (ViewPoly F α).Obj (ITree F α)) :
    shape' (ofShape layer) = layer := by
  unfold shape' ofShape
  rw [PFunctor.M.dest_mk, unpack_pack]
  exact viewMap_ofM_toM layer

/-- Destructing a tree assembled from one ergonomic shape layer recovers
that layer. This mirrors the constructor/destructor equation for `PFunctor.M`. -/
theorem shape'_mk (layer : (ViewPoly F α).Obj (ITree F α)) :
    shape' (ofShape layer) = layer :=
  shape'_ofShape layer

@[simp] theorem ofShape_shape' (tree : ITree F α) : ofShape (shape' tree) = tree := by
  apply toM_injective
  unfold ofShape shape'
  rw [viewMap_toM_ofM, pack_unpack, PFunctor.M.mk_dest]

/-! ### Smart constructors -/

/-- Build the `.pure` ITree node carrying a result `r : α`. (Coq `Ret`.) -/
def pure (r : α) : ITree F α :=
  ofShape ⟨.pure r, PEmpty.elim⟩

/-- Build the `.step` ITree node — a silent step in front of `t`. (Coq `Tau`.) -/
def step (t : ITree F α) : ITree F α :=
  ofShape ⟨.step, fun _ => t⟩

/-- Build the `.query` ITree node — a visible event `a : F.A` together with a
continuation `k : F.B a → ITree F α`. (Coq `Vis`.) -/
def query (a : F.A) (k : F.B a → ITree F α) : ITree F α :=
  ofShape ⟨.query a, k⟩

/-- One-step shape view of an ITree, dropping the continuation. The full data
remains accessible via `shape'`. -/
def shape (t : ITree F α) : Shape F α :=
  (shape' t).1

@[simp] theorem shape'_pure (r : α) : shape' (pure (F := F) r) = ⟨.pure r, PEmpty.elim⟩ := by
  rw [pure, shape'_ofShape]

@[simp] theorem shape'_step (t : ITree F α) : shape' (step t) = ⟨.step, fun _ => t⟩ := by
  rw [step, shape'_ofShape]

@[simp] theorem shape'_query (a : F.A) (k : F.B a → ITree F α) :
    shape' (query a k) = ⟨.query a, k⟩ :=
  shape'_ofShape _

@[simp] theorem shape_pure (r : α) : shape (pure (F := F) r) = .pure r := by
  rw [shape, shape'_pure]

@[simp] theorem shape_step (t : ITree F α) : shape (step t) = .step := by
  rw [shape, shape'_step]

@[simp] theorem shape_query (a : F.A) (k : F.B a → ITree F α) : shape (query a k) = .query a := by
  rw [shape, shape'_query]

/-! ### Corecursion and coinduction -/

/-- Build an ITree from a coalgebra stated in the ergonomic `Shape` view. -/
def corec {S : Type uS} (next : S → (ViewPoly F α).Obj S) (seed : S) : ITree F α :=
  ofM (PFunctor.M.corec (fun state => pack (next state)) seed)

@[simp] theorem toM_corec {S : Type uS} (next : S → (ViewPoly F α).Obj S) (seed : S) :
    (corec next seed).toM = PFunctor.M.corec (fun state => pack (next state)) seed := rfl

theorem shape'_corec_apply {S : Type uS} (next : S → (ViewPoly F α).Obj S) (seed : S) :
    shape' (corec next seed) =
      ⟨(next seed).1, fun direction => corec next ((next seed).2 direction)⟩ := by
  unfold shape' corec
  rw [PFunctor.M.dest_corec]
  rcases h : next seed with ⟨shape, children⟩
  cases shape with
  | pure value => exact Sigma.ext rfl (heq_of_eq (funext fun direction => direction.elim))
  | step => rfl
  | query position => rfl

theorem shape'_corec_eq {S : Type uS} {shape : (ViewPoly F α).A}
    {children : (ViewPoly F α).B shape → S}
    (next : S → (ViewPoly F α).Obj S) (seed : S)
    (h : next seed = ⟨shape, children⟩) :
    shape' (corec next seed) = ⟨shape, fun direction => corec next (children direction)⟩ := by
  rw [shape'_corec_apply, h]

/-- Recover the raw destructor by repacking `shape'` and unwrapping its children. -/
theorem pack_shape' (tree : ITree F α) :
    pack ((ViewPoly F α).map toM (shape' tree)) = PFunctor.M.dest tree.toM := by
  unfold shape'
  rw [viewMap_toM_ofM, pack_unpack]

/-- The computational destructor is injective. -/
theorem eq_of_shape'_eq {left right : ITree F α} (h : shape' left = shape' right) :
    left = right := by
  apply toM_injective
  apply PFunctor.M.eq_of_dest_eq
  rw [← pack_shape' left, ← pack_shape' right, h]

@[simp] theorem shape'_inj {left right : ITree F α} :
    shape' left = shape' right ↔ left = right :=
  ⟨eq_of_shape'_eq, fun h => h ▸ rfl⟩

/-- Coinduction stated entirely through the ergonomic ITree destructor. -/
theorem bisim (R : ITree F α → ITree F α → Prop)
    (step : ∀ left right, R left right → ∃ shape leftNext rightNext,
      shape' left = ⟨shape, leftNext⟩ ∧ shape' right = ⟨shape, rightNext⟩ ∧
        ∀ direction, R (leftNext direction) (rightNext direction)) :
    ∀ left right, R left right → left = right := by
  intro left right hrel
  apply toM_injective
  refine PFunctor.M.bisim (fun rawLeft rawRight => R (ofM rawLeft) (ofM rawRight)) ?_
      left.toM right.toM hrel
  intro rawLeft rawRight hraw
  obtain ⟨shape, leftNext, rightNext, hleft, hright, hnext⟩ :=
    step (ofM rawLeft) (ofM rawRight) hraw
  have hleftRaw : PFunctor.M.dest rawLeft =
      pack ((ViewPoly F α).map toM ⟨shape, leftNext⟩) := by
    rw [← pack_shape' (ofM rawLeft), hleft]
  have hrightRaw : PFunctor.M.dest rawRight =
      pack ((ViewPoly F α).map toM ⟨shape, rightNext⟩) := by
    rw [← pack_shape' (ofM rawRight), hright]
  cases shape with
  | pure value =>
      exact ⟨.inl (.inr value), PEmpty.elim, PEmpty.elim,
        hleftRaw, hrightRaw, fun direction => direction.elim⟩
  | step =>
      exact ⟨.inr PUnit.unit, fun direction => (leftNext direction).toM,
        fun direction => (rightNext direction).toM, hleftRaw, hrightRaw,
        fun direction => hnext direction⟩
  | query position =>
      exact ⟨.inl (.inl position), fun direction => (leftNext direction).toM,
        fun direction => (rightNext direction).toM, hleftRaw, hrightRaw,
        fun direction => hnext direction⟩

/-- Finality of `ITree.corec` in the computational view. -/
theorem corec_unique {S : Type uS} (next : S → (ViewPoly F α).Obj S)
    (f : S → ITree F α)
    (hf : ∀ state, shape' (f state) = (ViewPoly F α).map f (next state)) :
    f = corec next := by
  have hraw : (fun state => (f state).toM) =
      PFunctor.M.corec (fun state => pack (next state)) := by
    apply PFunctor.M.corec_unique
    intro state
    rw [← pack_shape' (f state), hf, pack_map, pack_map, PFunctor.map_map]
    rfl
  funext state
  apply toM_injective
  exact congrFun hraw state

/-- Corecursing from `shape'` reconstructs the original tree. -/
@[simp] theorem corec_shape' (tree : ITree F α) : corec shape' tree = tree := by
  have h := corec_unique (F := F) (α := α) shape' id
    (fun current => (ViewPoly F α).id_map (shape' current) |>.symm)
  exact (congrFun h tree).symm

/-- Relational comparison of two ITree corecursors. -/
theorem corec_eq_corec {S : Type uS} {T : Type uT}
    (leftStep : S → (ViewPoly F α).Obj S)
    (rightStep : T → (ViewPoly F α).Obj T)
    (R : S → T → Prop) (leftSeed : S) (rightSeed : T)
    (hseed : R leftSeed rightSeed)
    (hstep : ∀ left right, R left right → ∃ shape leftNext rightNext,
      leftStep left = ⟨shape, leftNext⟩ ∧ rightStep right = ⟨shape, rightNext⟩ ∧
        ∀ direction, R (leftNext direction) (rightNext direction)) :
    corec leftStep leftSeed = corec rightStep rightSeed := by
  let Srel : ITree F α → ITree F α → Prop := fun left right =>
    ∃ leftState rightState, R leftState rightState ∧
      left = corec leftStep leftState ∧ right = corec rightStep rightState
  refine bisim Srel ?_ _ _ ⟨leftSeed, rightSeed, hseed, rfl, rfl⟩
  rintro left right ⟨leftState, rightState, hrel, rfl, rfl⟩
  obtain ⟨shape, leftNext, rightNext, hleft, hright, hnext⟩ :=
    hstep leftState rightState hrel
  refine ⟨shape, fun direction => corec leftStep (leftNext direction),
    fun direction => corec rightStep (rightNext direction), ?_, ?_, ?_⟩
  · exact shape'_corec_eq leftStep leftState hleft
  · exact shape'_corec_eq rightStep rightState hright
  · intro direction
    exact ⟨leftNext direction, rightNext direction, hnext direction, rfl, rfl⟩

/-! ### Destructor-injectivity helpers -/

/-- A tree whose `shape'` exposes a `.pure` head is that pure leaf. The
direction continuation over the empty fiber is irrelevant. -/
theorem eq_pure_of_dest {t : ITree F α} {r : α}
    {c : (ViewPoly F α).B (.pure r) → ITree F α}
    (h : shape' t = ⟨.pure r, c⟩) : t = pure r := by
  apply eq_of_shape'_eq
  rw [h, shape'_pure]
  change (⟨.pure r, c⟩ : (ViewPoly F α).Obj _) = ⟨.pure r, PEmpty.elim⟩
  congr 1
  funext z
  exact z.elim

/-- A tree whose `shape'` exposes a `.step` head is a silent step in
front of its unique subtree. -/
theorem eq_step_of_dest {t : ITree F α} {c : (ViewPoly F α).B .step → ITree F α}
    (h : shape' t = ⟨.step, c⟩) : t = step (c PUnit.unit) := by
  apply eq_of_shape'_eq
  rw [h, shape'_step]

/-- A tree whose `shape'` exposes a `.query a` head is that visible
query with its continuation. -/
theorem eq_query_of_dest {t : ITree F α} {a : F.A}
    {c : (ViewPoly F α).B (.query a) → ITree F α}
    (h : shape' t = ⟨.query a, c⟩) : t = query a c := by
  apply eq_of_shape'_eq
  rw [h, shape'_query]

/-! ### Monadic bind via `ITree.corec`

The Coq `bind` (`Core/ITreeDefinition.v:157-168`) is a `cofix` over `subst`.
We translate it to `ITree.corec` by carrying a sum state: `Sum.inl t` means "we
are still consuming the original tree `t`", `Sum.inr u` means "we have spliced
in `k r` for some leaf `r` and are now propagating `u`'s structure". -/

/-- Step transformer used by `bind`: peel off one node from the current state
and emit the corresponding output node together with the next state. -/
def bindStep (k : α → ITree F β) :
    ITree F α ⊕ ITree F β → (ViewPoly F β).Obj (ITree F α ⊕ ITree F β)
  | .inl t =>
      match shape' t with
      | ⟨.pure r, _⟩ =>
          match shape' (k r) with
          | ⟨s, c⟩ => ⟨s, fun b => .inr (c b)⟩
      | ⟨.step, c⟩ => ⟨.step, fun _ => .inl (c PUnit.unit)⟩
      | ⟨.query a, c⟩ => ⟨.query a, fun b => .inl (c b)⟩
  | .inr u =>
      match shape' u with
      | ⟨s, c⟩ => ⟨s, fun b => .inr (c b)⟩

theorem bindStep_inl (k : α → ITree F β) (t : ITree F α) : bindStep k (.inl t) =
      (match shape' t with
        | ⟨.pure r, _⟩ =>
            match shape' (k r) with
            | ⟨s, c⟩ => ⟨s, fun b => .inr (c b)⟩
        | ⟨.step, c⟩ => ⟨.step, fun _ => .inl (c PUnit.unit)⟩
        | ⟨.query a, c⟩ => ⟨.query a, fun b => .inl (c b)⟩) := rfl

theorem bindStep_inr (k : α → ITree F β) (u : ITree F β) : bindStep k (.inr u) =
      (match shape' u with
        | ⟨s, c⟩ => ⟨s, fun b => .inr (c b)⟩) := rfl

/-- Monadic bind on ITrees. `t.bind k` runs `t` until it reaches a `.pure r`
leaf and then continues with `k r`. (Coq `ITree.bind`.) -/
def bind (t : ITree F α) (k : α → ITree F β) : ITree F β :=
  corec (bindStep k) (.inl t)

/-! ### Iteration via `ITree.corec`

The Coq `iter` (`Core/ITreeDefinition.v:192-194`) is

```coq
CoFixpoint iter body i :=
  Tau (body i >>= fun rj => match rj with
                            | inl j => iter body j
                            | inr r => Ret r end).
```

Lean has no native guardedness checker, so the natural recursive form is
rejected by both `structural_recursion` and `partial_fixpoint`. We therefore
push the recursion into `ITree.corec` with state `ITree F (β ⊕ α)`: at each step
we peel off one node and convert leaves of the form `.pure (.inl j)` into a
silent step followed by a fresh `body j` call. -/

/-- Step transformer used by `iter`. -/
def iterStep (body : β → ITree F (β ⊕ α)) :
    ITree F (β ⊕ α) → (ViewPoly F α).Obj (ITree F (β ⊕ α))
  | t =>
      match shape' t with
      | ⟨.pure (.inl j), _⟩ => ⟨.step, fun _ => body j⟩
      | ⟨.pure (.inr r), _⟩ => ⟨.pure r, PEmpty.elim⟩
      | ⟨.step, c⟩ => ⟨.step, fun u => c u⟩
      | ⟨.query a, c⟩ => ⟨.query a, fun b => c b⟩

/-- Iteration combinator. `iter body init` repeatedly invokes
`body : β → ITree F (β ⊕ α)`; intermediate `Sum.inl j` results restart the
loop on `j`, intermediate `Sum.inr r` results terminate with `r`.

Each loop iteration is silent-step-guarded so the corecursive definition is
productive. (Coq `ITree.iter`.) -/
def iter (body : β → ITree F (β ⊕ α)) (init : β) : ITree F α :=
  corec (iterStep body) (body init)

/-! ### Lifting events -/

/-- Lift a single event `a : F.A` into an ITree, returning the answer
unchanged. (Coq `ITree.trigger`.) -/
def lift (a : F.A) : ITree F (F.B a) :=
  query a pure

/-! ### Monad and `MonadIter` instances -/

instance instMonad : Monad (ITree F) where
  pure := pure
  bind := bind

instance instMonadIter : MonadIter (ITree F) where
  iterM := iter

/-! ### Definitional unfoldings

These match Coq's `Core/ITreeDefinition.v:208-217` (`unfold_bind`,
`unfold_iter`) but as one-step `simp` lemmas on `shape'`. The full equational
theory (`bind_pure_left`, `bind_assoc`, `iter_unfold`, …) requires
bisimulation reasoning and lives in `PolyFun.ITree.Bisim.*`. -/

@[simp] theorem shape'_bind (t : ITree F α) (k : α → ITree F β) : shape' (bind t k) =
      shape' (corec (bindStep k) (.inl t)) := rfl

@[simp] theorem shape'_iter (body : β → ITree F (β ⊕ α)) (init : β) : shape' (iter body init) =
      shape' (corec (iterStep body) (body init)) := rfl

@[simp] theorem shape_lift (a : F.A) : shape (lift (F := F) a) = .query a := by
  rw [lift, shape_query]

end ITree
