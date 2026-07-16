/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.M
public import PolyFun.PFunctor.Lens.Basic

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
  M.corec (fun source =>
    ⟨l.toFunA (M.head source), fun direction =>
      M.children source (l.toFunB (M.head source) direction)⟩) tree

/-- One-step unfolding of `mapLens`. -/
theorem dest_mapLens (l : Lens P Q) (tree : M P) :
    M.dest (mapLens l tree) =
      ⟨l.toFunA (M.head tree), fun direction =>
        mapLens l (M.children tree
          (l.toFunB (M.head tree) direction))⟩ := by
  simpa only [mapLens] using M.dest_corec_apply
    (fun source : M P =>
      ⟨l.toFunA (M.head source), fun direction =>
        M.children source (l.toFunB (M.head source) direction)⟩) tree

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
  change M.corec M.dest tree = tree
  exact M.corec_dest tree

/-- Mapping M-type trees respects composition of polynomial lenses. -/
theorem mapLens_comp {R : PFunctor.{uA₃, uB₃}} (g : Lens Q R)
    (f : Lens P Q) (tree : M P) :
    mapLens (g ∘ₗ f) tree = mapLens g (mapLens f tree) := by
  change M.corec (fun source => Lens.mapObj (g ∘ₗ f) (M.dest source)) tree =
    M.corec (fun source => Lens.mapObj g (M.dest source)) (mapLens f tree)
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
      change M.dest
          (M.corec (fun source => Lens.mapObj f (M.dest source)) source) = _
      exact M.dest_corec _ _
    rw [hmapped, hsource]
    rfl

/-- Mapping commutes with M-type corecursion by mapping each coalgebra step. -/
theorem mapLens_corec {α : Type v} (l : Lens P Q) (step : α → P α)
    (seed : α) :
    mapLens l (M.corec step seed) =
      M.corec (fun state => Lens.mapObj l (step state)) seed := by
  change M.corec (fun tree => Lens.mapObj l (M.dest tree))
      (M.corec step seed) =
    M.corec (fun state => Lens.mapObj l (step state)) seed
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

private theorem dependent_apply_heq {A : Sort uA}
    {B : A → Sort uB} {C : A → Sort uB₂}
    (function : (a : A) → B a → C a)
    {a a' : A} (ha : a = a') {b : B a} {b' : B a'} (hb : b ≍ b') :
    function a b ≍ function a' b' := by
  subst a'
  cases hb
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
    dependent_apply_heq g.toFunB
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
        (cast (congrArg Vertex (subtree_append first second).symm) third) =
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
  let last' : Vertex (subtree middle) :=
    cast (congrArg Vertex hsub) last
  refine ⟨append middle last', ?_⟩
  have hround :
      cast (congrArg Vertex hsub.symm) last' = last := by
    simp [last']
  calc
    append first (append middle last') =
        append (append first middle)
          (cast (congrArg Vertex hsub.symm) last') :=
      (append_assoc first middle last').symm
    _ = append (append first middle) last := by rw [hround]
    _ = third := hlast

/-- The prefix returned by `splitAt` is a prefix of the original vertex. -/
theorem splitAt_fst_isPrefix (n : Nat) {t : M P} (vertex : Vertex t) :
    IsPrefix (splitAt n vertex).1 vertex :=
  ⟨(splitAt n vertex).2, append_splitAt n vertex⟩

/-- Transport finite vertices along an equality of their ambient trees. -/
def castEquiv {t t' : M P} (h : t = t') : Vertex t ≃ Vertex t' :=
  _root_.Equiv.cast (congrArg Vertex h)

@[simp]
theorem cast_root {t t' : M P} (h : t = t') :
    cast (congrArg Vertex h) (.root t) = .root t' := by
  subst h
  rfl

@[simp]
theorem cast_child {t t' : M P} (h : t = t')
    (direction : P.B (M.head t))
    (next : Vertex (M.children t direction)) :
    cast (congrArg Vertex h) (.child direction next) =
      .child (M.castDirection h direction)
        (cast (congrArg Vertex
          (M.children_castDirection h direction)) next) := by
  subst h
  rfl

@[simp]
theorem castEquiv_rfl {t : M P} (vertex : Vertex t) :
    castEquiv rfl vertex = vertex :=
  rfl

@[simp]
theorem depth_cast {t t' : M P} (h : t = t') (vertex : Vertex t) :
    depth (cast (congrArg Vertex h) vertex) = depth vertex := by
  subst h
  rfl

@[simp]
theorem subtree_cast {t t' : M P} (h : t = t') (vertex : Vertex t) :
    subtree (cast (congrArg Vertex h) vertex) = subtree vertex := by
  subst h
  rfl

/-- Pull a finite vertex of a mapped M-type tree back through the generating
lens. -/
def pullMapLens (l : Lens P Q) (tree : M P) :
    Vertex (M.mapLens l tree) → Vertex tree
  | .root _ => .root tree
  | .child direction next =>
      let sourceDirection := M.pullDirection l tree direction
      let childEq := M.children_mapLens l tree direction
      .child sourceDirection
        (pullMapLens l (M.children tree sourceDirection)
          (cast (congrArg Vertex childEq) next))
termination_by vertex => depth vertex
decreasing_by
  calc
    depth (cast (congrArg Vertex childEq) next) = depth next :=
      depth_cast childEq next
    _ < depth (.child direction next) := Nat.lt_succ_self _

@[simp]
theorem pullMapLens_root (l : Lens P Q) (tree : M P) :
    pullMapLens l tree (.root (M.mapLens l tree)) = .root tree :=
  by rw [pullMapLens.eq_def]

/-- Constructor equation for pulling a non-root vertex through a lens. -/
@[simp]
theorem pullMapLens_child (l : Lens P Q) (tree : M P)
    (direction : Q.B (M.head (M.mapLens l tree)))
    (next : Vertex (M.children (M.mapLens l tree) direction)) :
    pullMapLens l tree (.child direction next) =
      .child (M.pullDirection l tree direction)
        (pullMapLens l
          (M.children tree (M.pullDirection l tree direction))
          (cast (congrArg Vertex (M.children_mapLens l tree direction)) next)) := by
  rw [pullMapLens.eq_def]

/-- Pulling a vertex through a lens preserves its finite depth. -/
@[simp]
theorem depth_pullMapLens (l : Lens P Q) (tree : M P)
    (vertex : Vertex (M.mapLens l tree)) :
    depth (pullMapLens l tree vertex) = depth vertex := by
  induction hdepth : depth vertex using Nat.strong_induction_on generalizing tree with
  | h n ih =>
      rw [pullMapLens.eq_def]
      cases vertex with
      | root => simpa only [depth_root] using hdepth
      | child direction next =>
          let sourceDirection := M.pullDirection l tree direction
          let childEq := M.children_mapLens l tree direction
          simp only [depth_child]
          rw [ih (depth (cast (congrArg Vertex childEq) next))]
          · calc
              depth (cast (congrArg Vertex childEq) next) + 1 =
                  depth next + 1 :=
                congrArg (· + 1) (depth_cast childEq next)
              _ = _ := hdepth
          · calc
              depth (cast (congrArg Vertex childEq) next) = depth next :=
                depth_cast childEq next
              _ < depth next + 1 := Nat.lt_succ_self _
              _ = _ := hdepth
          · rfl

/-- Pulling a mapped vertex selects exactly the source subtree whose image is
the target subtree. -/
@[simp]
theorem subtree_pullMapLens (l : Lens P Q) (tree : M P)
    (vertex : Vertex (M.mapLens l tree)) :
    M.mapLens l (subtree (pullMapLens l tree vertex)) = subtree vertex := by
  induction hdepth : depth vertex using Nat.strong_induction_on generalizing tree with
  | h n ih =>
      rw [pullMapLens.eq_def]
      cases vertex with
      | root => rfl
      | child direction next =>
          let sourceDirection := M.pullDirection l tree direction
          let childEq := M.children_mapLens l tree direction
          simp only [subtree_child]
          calc
            M.mapLens l
                (subtree (pullMapLens l (M.children tree sourceDirection)
                  (cast (congrArg Vertex childEq) next))) =
                subtree (cast (congrArg Vertex childEq) next) := by
              have hlt : depth (cast (congrArg Vertex childEq) next) < n := by
                calc
                  depth (cast (congrArg Vertex childEq) next) = depth next :=
                    depth_cast childEq next
                  _ < depth next + 1 := Nat.lt_succ_self _
                  _ = _ := hdepth
              exact ih (depth (cast (congrArg Vertex childEq) next)) hlt
                (M.children tree sourceDirection)
                (cast (congrArg Vertex childEq) next) rfl
            _ = subtree next := subtree_cast childEq next

/-- Pulling finite vertices through the identity lens is the dependent
identity transport induced by `M.mapLens_id`. -/
@[simp]
theorem pullMapLens_id (tree : M P)
    (vertex : Vertex (M.mapLens (Lens.id P) tree)) :
    pullMapLens (Lens.id P) tree vertex =
      cast (congrArg Vertex (M.mapLens_id tree)) vertex := by
  induction hdepth : depth vertex using Nat.strong_induction_on generalizing tree with
  | h n ih =>
      cases vertex with
      | root =>
          rw [pullMapLens_root]
          exact (cast_root (M.mapLens_id tree)).symm
      | child direction next =>
          let sourceDirection := M.pullDirection (Lens.id P) tree direction
          let targetDirection := M.castDirection (M.mapLens_id tree) direction
          let childEq := M.children_mapLens (Lens.id P) tree direction
          have hsource : sourceDirection ≍ direction := by
            unfold sourceDirection M.pullDirection
            exact cast_heq
              (congrArg P.B (M.head_mapLens (Lens.id P) tree)) direction
          have htarget : targetDirection ≍ direction := by
            unfold targetDirection M.castDirection
            exact cast_heq
              (congrArg (fun current => P.B (M.head current))
                (M.mapLens_id tree)) direction
          have hdirection : sourceDirection = targetDirection :=
            eq_of_heq (hsource.trans htarget.symm)
          rw [pullMapLens_child, cast_child (M.mapLens_id tree)]
          rw [Vertex.child.injEq]
          refine ⟨hdirection, ?_⟩
          have hrecursive := ih
            (depth (cast (congrArg Vertex childEq) next)) (by
              calc
                depth (cast (congrArg Vertex childEq) next) = depth next :=
                  depth_cast childEq next
                _ < depth next + 1 := Nat.lt_succ_self _
                _ = n := hdepth)
            (M.children tree sourceDirection)
            (cast (congrArg Vertex childEq) next) rfl
          exact (heq_of_eq hrecursive).trans
            ((cast_heq _ (cast (congrArg Vertex childEq) next)).trans
              ((cast_heq (congrArg Vertex childEq) next).trans
                (cast_heq _ next).symm))

/-- Pulling a finite vertex through a composite lens agrees with pulling it
through the two lenses successively. -/
theorem pullMapLens_comp {R : PFunctor.{uA₃, uB₃}}
    (g : Lens Q R) (f : Lens P Q) (tree : M P)
    (vertex : Vertex (M.mapLens (g ∘ₗ f) tree)) :
    pullMapLens (g ∘ₗ f) tree vertex =
      pullMapLens f tree
        (pullMapLens g (M.mapLens f tree)
          (cast (congrArg Vertex (M.mapLens_comp g f tree)) vertex)) := by
  induction hdepth : depth vertex using Nat.strong_induction_on generalizing tree with
  | h n ih =>
      cases vertex with
      | root =>
          rw [cast_root (M.mapLens_comp g f tree)]
          rw [pullMapLens_root, pullMapLens_root, pullMapLens_root]
      | child direction next =>
          rw [pullMapLens_child]
          rw [cast_child (M.mapLens_comp g f tree)]
          rw [pullMapLens_child, pullMapLens_child]
          rw [Vertex.child.injEq]
          refine ⟨M.pullDirection_comp g f tree direction, ?_⟩
          let compositeDirection :=
            M.pullDirection (g ∘ₗ f) tree direction
          let transportedDirection :=
            M.castDirection (M.mapLens_comp g f tree) direction
          let gDirection :=
            M.pullDirection g (M.mapLens f tree) transportedDirection
          let fDirection := M.pullDirection f tree gDirection
          have hdirection : compositeDirection = fDirection :=
            M.pullDirection_comp g f tree direction
          let compositeChild := M.children tree compositeDirection
          let sequentialChild := M.children tree fDirection
          have hchildren : compositeChild = sequentialChild :=
            congrArg (M.children tree) hdirection
          let compositeChildEq :=
            M.children_mapLens (g ∘ₗ f) tree direction
          let fChildEq :=
            M.children_mapLens f tree gDirection
          let ambientChildEq :=
            M.children_castDirection (M.mapLens_comp g f tree) direction
          let gChildEq :=
            M.children_mapLens g (M.mapLens f tree) transportedDirection
          let canonicalVertex :
              Vertex (M.mapLens g (M.mapLens f compositeChild)) :=
            cast (congrArg Vertex (M.mapLens_comp g f compositeChild))
              (cast (congrArg Vertex compositeChildEq) next)
          let actualGChild :=
            M.children (M.mapLens f tree) gDirection
          let actualVertex : Vertex (M.mapLens g actualGChild) :=
            cast (congrArg Vertex gChildEq)
              (cast (congrArg Vertex ambientChildEq) next)
          have hgChildren : M.mapLens f compositeChild = actualGChild := by
            calc
              M.mapLens f compositeChild =
                  M.mapLens f sequentialChild := congrArg (M.mapLens f) hchildren
              _ = actualGChild := fChildEq.symm
          have hvertices : canonicalVertex ≍ actualVertex := by
            exact
              ((cast_heq _
                (cast (congrArg Vertex compositeChildEq) next)).trans
                (cast_heq (congrArg Vertex compositeChildEq) next)).trans
              (((cast_heq _
                (cast (congrArg Vertex ambientChildEq) next)).trans
                (cast_heq (congrArg Vertex ambientChildEq) next)).symm)
          have hgResults :
              pullMapLens g (M.mapLens f compositeChild) canonicalVertex ≍
                pullMapLens g actualGChild actualVertex :=
            dependent_apply_heq
              (fun source : M Q => pullMapLens g source)
              hgChildren hvertices
          have hfInputs :
              pullMapLens g (M.mapLens f compositeChild) canonicalVertex ≍
                cast (congrArg Vertex fChildEq)
                  (pullMapLens g actualGChild actualVertex) :=
            hgResults.trans (cast_heq _ _).symm
          have hresults :
              pullMapLens f compositeChild
                  (pullMapLens g (M.mapLens f compositeChild)
                    canonicalVertex) ≍
                pullMapLens f sequentialChild
                  (cast (congrArg Vertex fChildEq)
                    (pullMapLens g actualGChild actualVertex)) :=
            dependent_apply_heq
              (fun source : M P => pullMapLens f source)
              hchildren hfInputs
          have hrecursive := ih
            (depth (cast (congrArg Vertex compositeChildEq) next)) (by
              calc
                depth (cast (congrArg Vertex compositeChildEq) next) =
                    depth next := depth_cast compositeChildEq next
                _ < depth next + 1 := Nat.lt_succ_self _
                _ = n := hdepth)
            compositeChild
            (cast (congrArg Vertex compositeChildEq) next) rfl
          exact (heq_of_eq hrecursive).trans hresults

end Vertex
end M
end PFunctor
