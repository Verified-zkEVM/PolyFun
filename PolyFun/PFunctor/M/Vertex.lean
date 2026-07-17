/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.M
public import PolyFun.PFunctor.Lens.Basic
import PolyFun.Logic.HEq

/-!
# Finite vertices of polynomial M-types

`M.Vertex t` is a finite rooted path selecting a vertex of the potentially
infinite polynomial tree `t : M P`.  The root is a vertex, and a child
direction followed by a finite vertex in that child subtree is a vertex of the
original tree.

The API exposes the selected rooted subtree, path concatenation, canonical
splitting at a depth, prefix structure, and dependent transport.  These are
the direction-level operations needed by the polynomial cofree comonoid: its
comultiplication sends a tree to all of its rooted subtrees, while its backward
map concatenates finite vertices.

This is the coinductive counterpart of `FreeM.Cursor`: both are finite
prefixes selecting a residual tree.  Here `append`, `depth`, and `subtree`
correspond to the cursor operations `comp`, `length`, and `residual`.
`Vertex` keeps only the source tree as an index because the selected subtree
is computed by `subtree`; this makes vertices the direct direction type of the
cofree polynomial, at the cost of explicit transports when composing paths.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uA₃ uB₃ v

namespace PFunctor
namespace M

variable {P : PFunctor.{uA, uB}}

/-! ## Mapping M-types along lenses -/

variable {Q : PFunctor.{uA₂, uB₂}}

/-- Map a potentially infinite polynomial tree along a lens. Target
directions are pulled back through the lens to select the corresponding source
child. -/
def mapLens (l : Lens P Q) (tree : M P) : M Q :=
  M.corec (fun source => l.mapObj (M.dest source)) tree

/-- One-step unfolding of `mapLens`. -/
theorem dest_mapLens (l : Lens P Q) (tree : M P) :
    M.dest (mapLens l tree) =
      ⟨l.toFunA (M.head tree), fun direction =>
        mapLens l (M.children tree
          (l.toFunB (M.head tree) direction))⟩ := by
  rw [mapLens, M.dest_corec_apply]
  rfl

/-- The root position of a mapped M-type tree. -/
theorem head_mapLens (l : Lens P Q) (tree : M P) :
    M.head (mapLens l tree) = l.toFunA (M.head tree) :=
  congrArg Sigma.fst (dest_mapLens l tree)

/-- Pull a root direction of a mapped tree back to the source root. -/
def pullDirection (l : Lens P Q) (tree : M P)
    (direction : Q.B (M.head (mapLens l tree))) : P.B (M.head tree) :=
  l.toFunB (M.head tree)
    (cast (congrArg Q.B (head_mapLens l tree)) direction)

/-- Selecting a child after mapping agrees with mapping the source child
selected by the pulled-back direction. -/
theorem children_mapLens (l : Lens P Q) (tree : M P)
    (direction : Q.B (M.head (mapLens l tree))) :
    M.children (mapLens l tree) direction =
      mapLens l (M.children tree (pullDirection l tree direction)) := by
  have h := dest_mapLens l tree
  have hA := congrArg Sigma.fst h
  have hB := (Sigma.ext_iff.mp h).2
  cases hA
  exact congrFun (eq_of_heq hB) direction

@[simp]
theorem mapLens_id (tree : M P) : mapLens (Lens.id P) tree = tree := by
  simpa only [mapLens, Lens.mapObj_id] using M.corec_dest tree

/-- Mapping M-type trees respects composition of polynomial lenses. -/
theorem mapLens_comp {R : PFunctor.{uA₃, uB₃}} (g : Lens Q R)
    (f : Lens P Q) (tree : M P) :
    mapLens (g ∘ₗ f) tree = mapLens g (mapLens f tree) := by
  refine M.corec_eq_corec
    (fun source => Lens.mapObj (g ∘ₗ f) (M.dest source))
    (fun source => Lens.mapObj g (M.dest source))
    (fun source mapped => mapped = mapLens f source)
    tree (mapLens f tree) rfl ?_
  rintro source _ rfl
  rcases hsource : M.dest source with ⟨shape, children⟩
  refine ⟨g.toFunA (f.toFunA shape),
    fun direction => children ((g ∘ₗ f).toFunB shape direction),
    fun direction => mapLens f
      (children ((g ∘ₗ f).toFunB shape direction)), ?_, ?_, fun _ => rfl⟩
  · simp only [Lens.mapObj]
    rfl
  · have hmapped : M.dest (mapLens f source) =
        Q.map (mapLens f) (Lens.mapObj f (M.dest source)) := by
      exact M.dest_corec _ _
    rw [hmapped, hsource]
    rfl

/-- Mapping commutes with M-type corecursion by mapping each coalgebra step. -/
theorem mapLens_corec {α : Type v} (l : Lens P Q) (step : α → P α)
    (seed : α) :
    mapLens l (M.corec step seed) =
      M.corec (fun state => Lens.mapObj l (step state)) seed := by
  refine M.corec_eq_corec
    (fun tree => Lens.mapObj l (M.dest tree))
    (fun state => Lens.mapObj l (step state))
    (fun tree state => tree = M.corec step state)
    (M.corec step seed) seed rfl ?_
  rintro tree state rfl
  rcases hstep : step state with ⟨shape, children⟩
  refine ⟨l.toFunA shape,
    fun direction => M.corec step (children (l.toFunB shape direction)),
    fun direction => children (l.toFunB shape direction), ?_, ?_, fun _ => rfl⟩
  · rw [M.dest_corec_apply, hstep]
    rfl
  · rfl

/-! ## Dependent transport along tree equalities -/

/-- Transport a root direction along an equality of its ambient M-type
trees. -/
def castDirection {tree tree' : M P} (h : tree = tree')
    (direction : P.B (M.head tree)) : P.B (M.head tree') :=
  cast (congrArg (fun current => P.B (M.head current)) h) direction

/-- Selecting a transported direction in an equal M-type tree recovers the
same child subtree. -/
theorem children_castDirection {tree tree' : M P} (h : tree = tree')
    (direction : P.B (M.head tree)) :
    M.children tree direction =
      M.children tree' (castDirection h direction) := by
  subst h
  rfl

/-- Pulling a root direction through a composite lens is the same as pulling
it through the two lenses successively. -/
theorem pullDirection_comp {R : PFunctor.{uA₃, uB₃}}
    (g : Lens Q R) (f : Lens P Q) (tree : M P)
    (direction : R.B (M.head (M.mapLens (g ∘ₗ f) tree))) :
    M.pullDirection (g ∘ₗ f) tree direction =
      M.pullDirection f tree
        (M.pullDirection g (M.mapLens f tree)
          (M.castDirection (M.mapLens_comp g f tree) direction)) := by
  unfold M.pullDirection M.castDirection
  apply eq_of_heq
  change f.toFunB (M.head tree)
      (g.toFunB (f.toFunA (M.head tree)) (cast _ direction)) ≍
    f.toFunB (M.head tree)
      (cast _ (g.toFunB (M.head (M.mapLens f tree))
        (cast _ (cast _ direction))))
  apply heq_of_eq
  apply congrArg (f.toFunB (M.head tree))
  apply eq_of_heq
  let leftInput := cast
    (congrArg R.B (M.head_mapLens (g ∘ₗ f) tree)) direction
  let rightInput := cast
    (congrArg R.B (M.head_mapLens g (M.mapLens f tree)))
      (cast
        (congrArg (fun current => R.B (M.head current))
          (M.mapLens_comp g f tree)) direction)
  have hinputs : leftInput ≍ rightInput :=
    (cast_heq _ direction).trans
      ((cast_heq _ (cast _ direction)).trans
        (cast_heq _ direction)).symm
  have houtputs :
      g.toFunB (f.toFunA (M.head tree)) leftInput ≍
        g.toFunB (M.head (M.mapLens f tree)) rightInput :=
    PolyFun.Logic.dependent_apply_heq g.toFunB
      (M.head_mapLens f tree).symm hinputs
  exact houtputs.trans (cast_heq _ _).symm

/-- A finite rooted vertex of an M-type tree. -/
inductive Vertex : (t : M P) → Type (max uA uB) where
  /-- The root vertex. -/
  | root (t : M P) : Vertex t
  /-- Descend through one direction and continue in the selected child. -/
  | child {t : M P} (direction : P.B (M.head t))
      (next : Vertex (M.children t direction)) : Vertex t

namespace Vertex

/-- Transport finite vertices along an equality of their ambient trees. -/
def castEquiv {t t' : M P} (h : t = t') : Vertex t ≃ Vertex t' :=
  _root_.Equiv.cast (congrArg Vertex h)

/-- The rooted subtree selected by a finite vertex. -/
def subtree : {t : M P} → Vertex t → M P
  | _, .root t => t
  | _, .child _ next => subtree next

@[simp]
theorem subtree_root (t : M P) : subtree (.root t) = t :=
  rfl

@[simp]
theorem subtree_child {t : M P} (direction : P.B (M.head t))
    (next : Vertex (M.children t direction)) :
    subtree (.child direction next) = subtree next :=
  rfl

/-- The number of child edges from the root to a vertex. -/
def depth : {t : M P} → Vertex t → Nat
  | _, .root _ => 0
  | _, .child _ next => depth next + 1

@[simp]
theorem depth_root (t : M P) : depth (.root t) = 0 :=
  rfl

@[simp]
theorem depth_child {t : M P} (direction : P.B (M.head t))
    (next : Vertex (M.children t direction)) :
    depth (.child direction next) = depth next + 1 :=
  rfl

/-- Concatenate a vertex from `t` with a vertex in the selected rooted
subtree. -/
def append : {t : M P} → (initial : Vertex t) →
    Vertex (subtree initial) → Vertex t
  | _, .root _, suffix => suffix
  | _, .child direction next, suffix =>
      .child direction (append next suffix)

@[simp]
theorem append_root (t : M P) (suffix : Vertex t) :
    append (.root t) suffix = suffix :=
  rfl

@[simp]
theorem append_child {t : M P} (direction : P.B (M.head t))
    (next : Vertex (M.children t direction))
    (suffix : Vertex (subtree next)) :
    append (.child direction next) suffix =
      .child direction (append next suffix) :=
  rfl

@[simp]
theorem append_root_right {t : M P} (vertex : Vertex t) :
    append vertex (.root (subtree vertex)) = vertex := by
  induction vertex with
  | root => rfl
  | child direction next ih =>
      exact congrArg (Vertex.child direction) ih

@[simp]
theorem subtree_append {t : M P} (initial : Vertex t)
    (suffix : Vertex (subtree initial)) :
    subtree (append initial suffix) = subtree suffix := by
  match initial with
  | .root _ => rfl
  | .child _ next => exact subtree_append next suffix

@[simp]
theorem depth_append {t : M P} (initial : Vertex t)
    (suffix : Vertex (subtree initial)) :
    depth (append initial suffix) = depth initial + depth suffix := by
  match initial with
  | .root _ =>
      simp only [append_root, depth_root, Nat.zero_add]
      rfl
  | .child direction next =>
      simp only [append_child, depth_child]
      rw [depth_append next suffix]
      exact Nat.add_right_comm (depth next) (depth suffix) 1

theorem append_assoc {t : M P} (first : Vertex t)
    (second : Vertex (subtree first))
    (third : Vertex (subtree second)) :
    append (append first second)
        (castEquiv (subtree_append first second).symm third) =
      append first (append second third) := by
  induction first with
  | root => rfl
  | child direction next ih =>
      exact congrArg (Vertex.child direction) (ih second third)

/-- Canonically split a vertex after at most `n` edges.  The first component
is a prefix vertex of the original tree and the second is the residual vertex
inside its selected subtree. -/
def splitAt : (n : Nat) → {t : M P} → (vertex : Vertex t) →
    Σ initial : Vertex t, Vertex (subtree initial)
  | 0, t, vertex => ⟨.root t, vertex⟩
  | _ + 1, t, .root _ => ⟨.root t, .root t⟩
  | n + 1, _, .child direction next =>
      let split := splitAt n next
      ⟨.child direction split.1, split.2⟩

@[simp]
theorem splitAt_zero {t : M P} (vertex : Vertex t) :
    splitAt 0 vertex = ⟨.root t, vertex⟩ :=
  rfl

@[simp]
theorem splitAt_succ_root (n : Nat) (t : M P) :
    splitAt (n + 1) (.root t) = ⟨.root t, .root t⟩ :=
  rfl

@[simp]
theorem splitAt_succ_child (n : Nat) {t : M P}
    (direction : P.B (M.head t))
    (next : Vertex (M.children t direction)) :
    splitAt (n + 1) (.child direction next) =
      ⟨.child direction (splitAt n next).1, (splitAt n next).2⟩ :=
  rfl

/-- Recombining the canonical split recovers the original vertex. -/
@[simp]
theorem append_splitAt (n : Nat) {t : M P} (vertex : Vertex t) :
    append (splitAt n vertex).1 (splitAt n vertex).2 = vertex := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      cases vertex with
      | root => rfl
      | child direction next =>
          exact congrArg (Vertex.child direction) (ih next)

/-- The depth of the canonical prefix is `min n depth`. -/
theorem depth_splitAt_fst (n : Nat) {t : M P} (vertex : Vertex t) :
    depth (splitAt n vertex).1 = min n (depth vertex) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      cases vertex with
      | root => simp
      | child direction next =>
          simp only [splitAt_succ_child, depth_child]
          rw [ih]
          omega

/-- The residual depth is the original depth minus the split depth. -/
theorem depth_splitAt_snd (n : Nat) {t : M P} (vertex : Vertex t) :
    depth (splitAt n vertex).2 = depth vertex - n := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      cases vertex with
      | root => simp
      | child direction next =>
          simp only [splitAt_succ_child, depth_child]
          calc
            depth (splitAt n next).2 = depth next - n := ih next
            _ = depth next + 1 - (n + 1) := by omega

/-- Splitting at the full depth yields the vertex itself followed by the root
of its selected subtree. -/
theorem splitAt_depth {t : M P} (vertex : Vertex t) :
    splitAt (depth vertex) vertex =
      ⟨vertex, .root (subtree vertex)⟩ := by
  induction vertex with
  | root => rfl
  | child direction next ih =>
      exact congrArg
        (fun split : Σ initial : Vertex (M.children _ direction),
            Vertex (subtree initial) =>
          (⟨.child direction split.1, split.2⟩ :
            Σ initial : Vertex _, Vertex (subtree initial))) ih

/-- Descend one additional edge from an already selected vertex. -/
def descend {t : M P} (vertex : Vertex t)
    (direction : P.B (M.head (subtree vertex))) : Vertex t :=
  append vertex (.child direction (.root (M.children (subtree vertex) direction)))

@[simp]
theorem subtree_descend {t : M P} (vertex : Vertex t)
    (direction : P.B (M.head (subtree vertex))) :
    subtree (descend vertex direction) =
      M.children (subtree vertex) direction := by
  simp [descend]

@[simp]
theorem depth_descend {t : M P} (vertex : Vertex t)
    (direction : P.B (M.head (subtree vertex))) :
    depth (descend vertex direction) = depth vertex + 1 := by
  simp [descend]

/-- The position label exposed at a selected vertex. -/
def positionAt {t : M P} (vertex : Vertex t) : P.A :=
  M.head (subtree vertex)

@[simp]
theorem positionAt_root (t : M P) : positionAt (.root t) = M.head t :=
  rfl

@[simp]
theorem positionAt_child {t : M P} (direction : P.B (M.head t))
    (next : Vertex (M.children t direction)) :
    positionAt (.child direction next) = positionAt next :=
  rfl

/-- `initial ≤ vertex` means that `vertex` is obtained by appending a residual
vertex to `initial`. -/
def IsPrefix {t : M P} (initial vertex : Vertex t) : Prop :=
  ∃ suffix : Vertex (subtree initial), append initial suffix = vertex

@[simp]
theorem root_isPrefix {t : M P} (vertex : Vertex t) :
    IsPrefix (.root t) vertex :=
  ⟨vertex, rfl⟩

@[refl]
theorem isPrefix_refl {t : M P} (vertex : Vertex t) :
    IsPrefix vertex vertex :=
  ⟨.root (subtree vertex), append_root_right vertex⟩

@[trans]
theorem IsPrefix.trans {t : M P} {first second third : Vertex t}
    (hFirst : IsPrefix first second) (hSecond : IsPrefix second third) :
    IsPrefix first third := by
  rcases hFirst with ⟨middle, rfl⟩
  rcases hSecond with ⟨last, hlast⟩
  let hsub := subtree_append first middle
  let last' : Vertex (subtree middle) := castEquiv hsub last
  refine ⟨append middle last', ?_⟩
  have hround :
      castEquiv hsub.symm last' = last := by
    simp [last', castEquiv]
  calc
    append first (append middle last') =
        append (append first middle)
          (castEquiv hsub.symm last') :=
      (append_assoc first middle last').symm
    _ = append (append first middle) last := by rw [hround]
    _ = third := hlast

/-- The prefix returned by `splitAt` is a prefix of the original vertex. -/
theorem splitAt_fst_isPrefix (n : Nat) {t : M P} (vertex : Vertex t) :
    IsPrefix (splitAt n vertex).1 vertex :=
  ⟨(splitAt n vertex).2, append_splitAt n vertex⟩

@[simp]
theorem cast_root {t t' : M P} (h : t = t') :
    castEquiv h (.root t) = .root t' := by
  subst h
  rfl

@[simp]
theorem cast_child {t t' : M P} (h : t = t')
    (direction : P.B (M.head t))
    (next : Vertex (M.children t direction)) :
    castEquiv h (.child direction next) =
      .child (M.castDirection h direction)
        (castEquiv (M.children_castDirection h direction) next) := by
  subst h
  rfl

@[simp]
theorem castEquiv_rfl {t : M P} (vertex : Vertex t) :
    castEquiv rfl vertex = vertex :=
  rfl

@[simp]
theorem depth_cast {t t' : M P} (h : t = t') (vertex : Vertex t) :
    depth (castEquiv h vertex) = depth vertex := by
  subst h
  rfl

@[simp]
theorem subtree_cast {t t' : M P} (h : t = t') (vertex : Vertex t) :
    subtree (castEquiv h vertex) = subtree vertex := by
  subst h
  rfl

/-- Structural implementation of vertex pullback.  The equality records that
the current target subtree is the image of the current source subtree, so the
recursive call can follow the vertex constructor directly. -/
def pullMapLensAux (l : Lens P Q) (tree : M P) :
    (target : M Q) → target = M.mapLens l tree → Vertex target → Vertex tree
  | _, _, .root _ => .root tree
  | target, htarget, .child direction next =>
      let mappedDirection := M.castDirection htarget direction
      let sourceDirection := M.pullDirection l tree mappedDirection
      let childEq := (M.children_castDirection htarget direction).trans
        (M.children_mapLens l tree mappedDirection)
      .child sourceDirection
        (pullMapLensAux l (M.children tree sourceDirection)
          (M.children target direction) childEq next)

/-- Pull a finite vertex of a mapped M-type tree back through the generating
lens. -/
def pullMapLens (l : Lens P Q) (tree : M P)
    (vertex : Vertex (M.mapLens l tree)) : Vertex tree :=
  pullMapLensAux l tree (M.mapLens l tree) rfl vertex

private theorem pullMapLensAux_eq_pullMapLens (l : Lens P Q) (tree : M P)
    (target : M Q) (htarget : target = M.mapLens l tree)
    (vertex : Vertex target) :
    pullMapLensAux l tree target htarget vertex =
      pullMapLens l tree (castEquiv htarget vertex) := by
  subst target
  simp only [castEquiv_rfl, pullMapLens]

@[simp]
theorem pullMapLens_root (l : Lens P Q) (tree : M P) :
    pullMapLens l tree (.root (M.mapLens l tree)) = .root tree :=
  rfl

/-- Constructor equation for pulling a non-root vertex through a lens. -/
@[simp]
theorem pullMapLens_child (l : Lens P Q) (tree : M P)
    (direction : Q.B (M.head (M.mapLens l tree)))
    (next : Vertex (M.children (M.mapLens l tree) direction)) :
    pullMapLens l tree (.child direction next) =
      .child (M.pullDirection l tree direction)
        (pullMapLens l
          (M.children tree (M.pullDirection l tree direction))
          (castEquiv (M.children_mapLens l tree direction) next)) := by
  change
    Vertex.child (M.pullDirection l tree direction)
        (pullMapLensAux l
          (M.children tree (M.pullDirection l tree direction))
          (M.children (M.mapLens l tree) direction)
          (M.children_mapLens l tree direction) next) = _
  exact congrArg (Vertex.child (M.pullDirection l tree direction))
    (pullMapLensAux_eq_pullMapLens l
      (M.children tree (M.pullDirection l tree direction))
      (M.children (M.mapLens l tree) direction)
      (M.children_mapLens l tree direction) next)

private theorem depth_pullMapLensAux (l : Lens P Q) (tree : M P)
    (target : M Q) (htarget : target = M.mapLens l tree)
    (vertex : Vertex target) :
    depth (pullMapLensAux l tree target htarget vertex) = depth vertex := by
  induction vertex generalizing tree with
  | root => rfl
  | child direction next ih =>
      simp only [pullMapLensAux, depth_child]
      exact congrArg (fun value => value + 1) (ih _ _)

/-- Pulling a vertex through a lens preserves its finite depth. -/
@[simp]
theorem depth_pullMapLens (l : Lens P Q) (tree : M P)
    (vertex : Vertex (M.mapLens l tree)) :
    depth (pullMapLens l tree vertex) = depth vertex :=
  depth_pullMapLensAux l tree (M.mapLens l tree) rfl vertex

private theorem subtree_pullMapLensAux (l : Lens P Q) (tree : M P)
    (target : M Q) (htarget : target = M.mapLens l tree)
    (vertex : Vertex target) :
    M.mapLens l (subtree (pullMapLensAux l tree target htarget vertex)) =
      subtree vertex := by
  induction vertex generalizing tree with
  | root => exact htarget.symm
  | child direction next ih =>
      simp only [pullMapLensAux, subtree_child]
      exact ih _ _

/-- Pulling a mapped vertex selects exactly the source subtree whose image is
the target subtree. -/
@[simp]
theorem subtree_pullMapLens (l : Lens P Q) (tree : M P)
    (vertex : Vertex (M.mapLens l tree)) :
    M.mapLens l (subtree (pullMapLens l tree vertex)) = subtree vertex :=
  subtree_pullMapLensAux l tree (M.mapLens l tree) rfl vertex

private theorem pullMapLensAux_append (l : Lens P Q) (tree : M P)
    (target : M Q) (htarget : target = M.mapLens l tree)
    (initial : Vertex target) (suffix : Vertex (subtree initial)) :
    pullMapLensAux l tree target htarget (append initial suffix) =
      append (pullMapLensAux l tree target htarget initial)
        (pullMapLensAux l
          (subtree (pullMapLensAux l tree target htarget initial))
          (subtree initial)
          (subtree_pullMapLensAux l tree target htarget initial).symm suffix) := by
  induction initial generalizing tree with
  | root => rfl
  | child direction next ih =>
      simp only [append_child, pullMapLensAux, subtree_child]
      exact congrArg (Vertex.child _) (ih _ _ _)

/-- Pulling a mapped finite path commutes with concatenation. The explicit
transport puts the target suffix in the mapped copy of the selected source
subtree. -/
theorem pullMapLens_append (l : Lens P Q) (tree : M P)
    (initial : Vertex (M.mapLens l tree))
    (suffix : Vertex (subtree initial)) :
    pullMapLens l tree (append initial suffix) =
      append (pullMapLens l tree initial)
        (pullMapLens l (subtree (pullMapLens l tree initial))
          (castEquiv (subtree_pullMapLens l tree initial).symm suffix)) := by
  have happend := pullMapLensAux_append l tree (M.mapLens l tree) rfl
    initial suffix
  unfold pullMapLens
  rw [happend]
  exact congrArg (append (pullMapLens l tree initial))
    (pullMapLensAux_eq_pullMapLens l
      (subtree (pullMapLens l tree initial)) (subtree initial)
      (subtree_pullMapLens l tree initial).symm suffix)

/-- Pulling finite vertices through the identity lens is the dependent
identity transport induced by `M.mapLens_id`. -/
private theorem pullMapLensAux_id (tree : M P) (target : M P)
    (htarget : target = M.mapLens (Lens.id P) tree)
    (vertex : Vertex target) :
    pullMapLensAux (Lens.id P) tree target htarget vertex =
      castEquiv (htarget.trans (M.mapLens_id tree)) vertex := by
  induction vertex generalizing tree with
  | @root target => rw [pullMapLensAux, cast_root]
  | @child target direction next ih =>
      let mappedDirection := M.castDirection htarget direction
      let sourceDirection :=
        M.pullDirection (Lens.id P) tree mappedDirection
      let targetDirection :=
        M.castDirection (htarget.trans (M.mapLens_id tree)) direction
      let childEq := (M.children_castDirection htarget direction).trans
        (M.children_mapLens (Lens.id P) tree mappedDirection)
      have hmapped : mappedDirection ≍ direction := by
        unfold mappedDirection M.castDirection
        exact cast_heq _ direction
      have hsource : sourceDirection ≍ direction := by
        unfold sourceDirection M.pullDirection
        change cast
            (congrArg P.B (M.head_mapLens (Lens.id P) tree))
            mappedDirection ≍ direction
        exact (cast_heq
          (congrArg P.B (M.head_mapLens (Lens.id P) tree))
          mappedDirection).trans hmapped
      have htargetDirection : targetDirection ≍ direction := by
        unfold targetDirection M.castDirection
        exact cast_heq _ direction
      have hdirection : sourceDirection = targetDirection :=
        eq_of_heq (hsource.trans htargetDirection.symm)
      rw [pullMapLensAux, cast_child, Vertex.child.injEq]
      refine ⟨hdirection, ?_⟩
      have hrecursive := ih
        (M.children tree sourceDirection)
        childEq
      exact (heq_of_eq hrecursive).trans
        ((cast_heq _ next).trans (cast_heq _ next).symm)

@[simp]
theorem pullMapLens_id (tree : M P)
    (vertex : Vertex (M.mapLens (Lens.id P) tree)) :
    pullMapLens (Lens.id P) tree vertex =
      castEquiv (M.mapLens_id tree) vertex :=
  pullMapLensAux_id tree (M.mapLens (Lens.id P) tree) rfl vertex

/-- Pulling a finite vertex through a composite lens agrees with pulling it
through the two lenses successively. -/
private theorem pullMapLensAux_comp {R : PFunctor.{uA₃, uB₃}}
    (g : Lens Q R) (f : Lens P Q) (tree : M P) (target : M R)
    (htarget : target = M.mapLens (g ∘ₗ f) tree)
    (vertex : Vertex target) :
    pullMapLensAux (g ∘ₗ f) tree target htarget vertex =
      pullMapLens f tree
        (pullMapLens g (M.mapLens f tree)
          (castEquiv
            (htarget.trans (M.mapLens_comp g f tree)) vertex)) := by
  induction vertex generalizing tree with
  | @root target =>
      rw [pullMapLensAux, cast_root, pullMapLens_root, pullMapLens_root]
  | @child target direction next ih =>
      let mappedDirection := M.castDirection htarget direction
      let compositeDirection :=
        M.pullDirection (g ∘ₗ f) tree mappedDirection
      let combinedEq := htarget.trans (M.mapLens_comp g f tree)
      let transportedDirection := M.castDirection combinedEq direction
      let sequentialDirection := M.castDirection
        (M.mapLens_comp g f tree) mappedDirection
      have hsequential : sequentialDirection = transportedDirection := by
        apply eq_of_heq
        exact (cast_heq _ mappedDirection).trans
          ((cast_heq _ direction).trans
            (cast_heq _ direction).symm)
      let gDirection :=
        M.pullDirection g (M.mapLens f tree) transportedDirection
      let fDirection := M.pullDirection f tree gDirection
      have hdirection : compositeDirection = fDirection := by
        calc
          compositeDirection =
              M.pullDirection f tree
                (M.pullDirection g (M.mapLens f tree)
                  sequentialDirection) :=
            M.pullDirection_comp g f tree mappedDirection
          _ = fDirection := by rw [hsequential]
      rw [pullMapLensAux, cast_child, pullMapLens_child,
        pullMapLens_child, Vertex.child.injEq]
      refine ⟨hdirection, ?_⟩
      let leftChildEq := (M.children_castDirection htarget direction).trans
        (M.children_mapLens (g ∘ₗ f) tree mappedDirection)
      let compositeChild := M.children tree compositeDirection
      let sequentialChild := M.children tree fDirection
      have hchildren : compositeChild = sequentialChild :=
        congrArg (M.children tree) hdirection
      let ambientChildEq := M.children_castDirection combinedEq direction
      let gChildEq :=
        M.children_mapLens g (M.mapLens f tree) transportedDirection
      let fChildEq := M.children_mapLens f tree gDirection
      let canonicalVertex :
          Vertex (M.mapLens g (M.mapLens f compositeChild)) :=
        castEquiv
          (leftChildEq.trans (M.mapLens_comp g f compositeChild)) next
      let actualGChild := M.children (M.mapLens f tree) gDirection
      let actualVertex : Vertex (M.mapLens g actualGChild) :=
        castEquiv gChildEq (castEquiv ambientChildEq next)
      have hgChildren : M.mapLens f compositeChild = actualGChild := by
        calc
          M.mapLens f compositeChild = M.mapLens f sequentialChild :=
            congrArg (M.mapLens f) hchildren
          _ = actualGChild := fChildEq.symm
      have hvertices : canonicalVertex ≍ actualVertex := by
        have hcanonical : canonicalVertex ≍ next := by
          unfold canonicalVertex castEquiv
          exact cast_heq _ next
        have hactual : actualVertex ≍ next := by
          have hinner : castEquiv ambientChildEq next ≍ next := by
            unfold castEquiv
            exact cast_heq (congrArg Vertex ambientChildEq) next
          have houter : actualVertex ≍ castEquiv ambientChildEq next := by
            unfold actualVertex castEquiv
            exact cast_heq (congrArg Vertex gChildEq)
              (cast (congrArg Vertex ambientChildEq) next)
          exact houter.trans hinner
        exact hcanonical.trans hactual.symm
      have hgResults :
          pullMapLens g (M.mapLens f compositeChild) canonicalVertex ≍
            pullMapLens g actualGChild actualVertex :=
        PolyFun.Logic.dependent_apply_heq
          (fun source : M Q => pullMapLens g source)
          hgChildren hvertices
      have hfInputs :
          pullMapLens g (M.mapLens f compositeChild) canonicalVertex ≍
            castEquiv fChildEq
              (pullMapLens g actualGChild actualVertex) :=
        hgResults.trans (by
          unfold castEquiv
          exact (cast_heq (congrArg Vertex fChildEq)
            (pullMapLens g actualGChild actualVertex)).symm)
      have hresults :
          pullMapLens f compositeChild
              (pullMapLens g (M.mapLens f compositeChild) canonicalVertex) ≍
            pullMapLens f sequentialChild
              (castEquiv fChildEq
                (pullMapLens g actualGChild actualVertex)) :=
        PolyFun.Logic.dependent_apply_heq
          (fun source : M P => pullMapLens f source)
          hchildren hfInputs
      have hrecursive := ih compositeChild leftChildEq
      exact (heq_of_eq hrecursive).trans hresults

theorem pullMapLens_comp {R : PFunctor.{uA₃, uB₃}}
    (g : Lens Q R) (f : Lens P Q) (tree : M P)
    (vertex : Vertex (M.mapLens (g ∘ₗ f) tree)) :
    pullMapLens (g ∘ₗ f) tree vertex =
      pullMapLens f tree
        (pullMapLens g (M.mapLens f tree)
          (castEquiv (M.mapLens_comp g f tree) vertex)) :=
  pullMapLensAux_comp g f tree (M.mapLens (g ∘ₗ f) tree) rfl vertex

end Vertex
end M
end PFunctor
