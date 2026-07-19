/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.IPFunctor.Basic
public import PolyFun.PFunctor.M.Vertex

/-!
# Indexed M-types

`IPFunctor.IM P i` is the final coalgebra of an indexed polynomial endofunctor
`P : IPFunctor.Endo I`, at index `i`.  Its implementation representation is an
ordinary M-tree over `P.sigmaPFunctor` together with proof that every child
root has the source index prescribed by `P.src`.

The proof quantifies over every finite vertex.  It is proposition-valued and
therefore carries no proof-relevant tree data; all proof-relevant choices live
in the underlying M-tree.
-/

@[expose] public section

universe uI uA uB uX

namespace IPFunctor

variable {I : Type uI} (P : IPFunctor.Endo.{uI, uA, uB} I)

namespace IM

/-- The root index stored in the sigma-erased representation. -/
def rootIndex (tree : PFunctor.M P.sigmaPFunctor) : I :=
  (PFunctor.M.dest tree).1.1

/-- The source-index law at the root of one sigma-erased tree. -/
def EdgeCoherent (tree : PFunctor.M P.sigmaPFunctor) : Prop :=
  let node := PFunctor.M.dest tree
  ∀ direction : P.B node.1.1 node.1.2,
    rootIndex P (node.2 direction) =
      P.src node.1.1 node.1.2 direction

/-- Every edge of a sigma-erased M-tree carries the source index prescribed
by the indexed polynomial. -/
def WellIndexed (tree : PFunctor.M P.sigmaPFunctor) : Prop :=
  ∀ vertex : PFunctor.M.Vertex tree,
    EdgeCoherent P (PFunctor.M.Vertex.subtree vertex)

end IM

/-- The indexed M-type of `P` at root index `i`.

The representation is implementation-facing so its invariants can be audited;
ordinary clients should use `dest`, `mk`, and `corec`. -/
structure IM (i : I) where
  /-- Build the audit-facing representation from an erased tree and its
  root/all-edge coherence certificates. -/
  ofCore ::
  /-- The underlying ordinary M-tree over the sigma-bundled polynomial. -/
  toM : PFunctor.M P.sigmaPFunctor
  /-- The bundled root index is the advertised indexed-M fiber. -/
  root_eq : IM.rootIndex P toM = i
  /-- Every finite edge carries the source index prescribed by `P.src`. -/
  wellIndexed : IM.WellIndexed P toM

namespace IM

variable {P} {i : I}

/-- The indexed shape exposed at the root. -/
def head (tree : IM P i) : P.A i := by
  rw [← tree.root_eq]
  exact (PFunctor.M.dest tree.toM).1.2

/-- The indexed child selected by one root direction. -/
def child (tree : IM P i) (direction : P.B i tree.head) :
    IM P (P.src i tree.head direction) := by
  rcases tree with ⟨tree, rootEq, wellIndexed⟩
  cases rootEq
  change P.B (PFunctor.M.dest tree).1.1 (PFunctor.M.dest tree).1.2 at direction
  refine {
    toM := (PFunctor.M.dest tree).2 direction
    root_eq := wellIndexed (.root tree) direction
    wellIndexed := fun vertex => ?_
  }
  dsimp only [WellIndexed, PFunctor.M.Vertex.subtree]
  intro nextDirection
  exact wellIndexed (.child direction vertex) nextDirection

/-- Destructor of the indexed final coalgebra. -/
def dest (tree : IM P i) : P.Obj (IM P) i :=
  ⟨tree.head, tree.child⟩

/-- Erase one indexed node by bundling its output index into the ordinary
sigma-polynomial shape and forgetting only the proof fields of its children. -/
def eraseObj (node : P.Obj (IM P) i) :
    P.sigmaPFunctor.Obj (PFunctor.M P.sigmaPFunctor) :=
  ⟨⟨i, node.1⟩, fun direction => (node.2 direction).toM⟩

/-- The sigma-erased destruction of an indexed tree is its indexed
destruction with the root index bundled into the shape. -/
theorem toM_dest (tree : IM P i) :
    PFunctor.M.dest tree.toM = eraseObj (dest tree) := by
  rcases tree with ⟨tree, rootEq, wellIndexed⟩
  cases rootEq
  rfl

/-- Two indexed M-trees are equal when their sigma-erased trees are equal;
the root and edge-coherence fields are propositions. -/
@[ext]
theorem ext (left right : IM P i) (h : left.toM = right.toM) : left = right := by
  rcases left with ⟨left, leftRoot, leftWellIndexed⟩
  rcases right with ⟨right, rightRoot, rightWellIndexed⟩
  cases h
  rfl

/-- Constructor of the indexed final coalgebra. -/
def mk (node : P.Obj (IM P) i) : IM P i := by
  rcases node with ⟨shape, children⟩
  let underlying : P.sigmaPFunctor.Obj (PFunctor.M P.sigmaPFunctor) :=
    ⟨⟨i, shape⟩, fun direction => (children direction).toM⟩
  let tree := PFunctor.M.mk underlying
  refine {
    toM := tree
    root_eq := ?_
    wellIndexed := ?_
  }
  · simp [rootIndex, tree, underlying]
  · intro vertex
    cases vertex with
    | root =>
        simpa [tree, underlying, EdgeCoherent, rootIndex] using
          fun direction => (children direction).root_eq
    | child direction next =>
        dsimp only [PFunctor.M.Vertex.subtree]
        intro nextDirection
        exact (children direction).wellIndexed next nextDirection

@[simp]
theorem head_mk (node : P.Obj (IM P) i) : (mk node).head = node.1 := by
  rcases node with ⟨shape, children⟩
  rfl

@[simp]
theorem dest_mk (node : P.Obj (IM P) i) : dest (mk node) = node := by
  rcases node with ⟨shape, children⟩
  rfl

@[simp]
theorem mk_dest (tree : IM P i) : mk (dest tree) = tree := by
  apply ext
  rcases tree with ⟨tree, rootEq, wellIndexed⟩
  cases rootEq
  simp only [mk, dest, head, child, rootIndex]
  exact PFunctor.M.mk_dest tree

/-- Constructor/destructor equivalence for the indexed final coalgebra. -/
def destEquiv : IM P i ≃ P.Obj (IM P) i where
  toFun := dest
  invFun := mk
  left_inv := mk_dest
  right_inv := dest_mk

/-- Equality of indexed M-trees follows from equality of their one-step
destructions. -/
theorem eq_of_dest_eq {left right : IM P i}
    (h : dest left = dest right) : left = right := by
  rw [← mk_dest left, ← mk_dest right, h]

@[simp]
theorem dest_inj {left right : IM P i} :
    dest left = dest right ↔ left = right :=
  ⟨eq_of_dest_eq, fun h => h ▸ rfl⟩

section Corec

variable {X : I → Type uX}

/-- Sigma-totalized coalgebra step used by the representation of indexed
corecursion as ordinary M-type corecursion. -/
def totalStep (step : (i : I) → X i → P.Obj X i) :
    (Σ i, X i) → P.sigmaPFunctor.Obj (Σ i, X i)
  | ⟨i, state⟩ =>
      let node := step i state
      ⟨⟨i, node.1⟩, fun direction =>
        ⟨P.src i node.1 direction, node.2 direction⟩⟩

theorem corecTree_vertex
    (step : (i : I) → X i → P.Obj X i) (seed : Σ i, X i) :
    ∀ {tree : PFunctor.M P.sigmaPFunctor},
      tree = PFunctor.M.corec (totalStep (P := P) step) seed →
      (vertex : PFunctor.M.Vertex tree) →
      EdgeCoherent P (PFunctor.M.Vertex.subtree vertex) := by
  intro tree hTree vertex
  induction vertex generalizing seed with
  | root treeAt =>
      subst treeAt
      rcases seed with ⟨index, state⟩
      change EdgeCoherent P
        (PFunctor.M.corec (totalStep (P := P) step) ⟨index, state⟩)
      simp only [EdgeCoherent, rootIndex]
      rw [PFunctor.M.dest_corec_apply]
      dsimp only [totalStep]
      intro direction
      rw [PFunctor.M.dest_corec_apply]
      rfl
  | child direction next ih =>
      cases hTree
      rcases seed with ⟨index, state⟩
      have hDest :
          PFunctor.M.dest
              (PFunctor.M.corec (totalStep (P := P) step) ⟨index, state⟩) =
            ⟨⟨index, (step index state).1⟩, fun direction =>
              PFunctor.M.corec (totalStep (P := P) step)
                ⟨P.src index (step index state).1 direction,
                  (step index state).2 direction⟩⟩ := by
        rw [PFunctor.M.dest_corec_apply]
        rfl
      cases hDest
      exact ih
        ⟨P.src index (step index state).1 direction,
          (step index state).2 direction⟩ rfl

theorem corecTree_wellIndexed
    (step : (i : I) → X i → P.Obj X i) (seed : Σ i, X i) :
    WellIndexed P (PFunctor.M.corec (totalStep (P := P) step) seed) :=
  fun vertex => corecTree_vertex (P := P) step seed rfl vertex

/-- Corecursor into the indexed final coalgebra. -/
def corec (step : (i : I) → X i → P.Obj X i) (i : I) (state : X i) :
    IM P i := by
  let tree := PFunctor.M.corec (totalStep (P := P) step) ⟨i, state⟩
  refine {
    toM := tree
    root_eq := ?_
    wellIndexed := corecTree_wellIndexed (P := P) step ⟨i, state⟩
  }
  simp [tree, rootIndex, PFunctor.M.dest_corec_apply, totalStep]

@[simp]
theorem toM_corec (step : (i : I) → X i → P.Obj X i)
    (i : I) (state : X i) :
    (corec (P := P) step i state).toM =
      PFunctor.M.corec (totalStep (P := P) step) ⟨i, state⟩ :=
  rfl

/-- The defining equation of indexed corecursion. -/
@[simp]
theorem dest_corec (step : (i : I) → X i → P.Obj X i)
    (i : I) (state : X i) :
    dest (corec (P := P) step i state) =
      P.map (fun j next => corec (P := P) step j next) (step i state) := by
  let tree := corec (P := P) step i state
  rcases hStep : step i state with ⟨shape, children⟩
  have hUnderlying :
      PFunctor.M.dest tree.toM =
        ⟨⟨i, shape⟩, fun direction =>
          (corec (P := P) step _ (children direction)).toM⟩ := by
    simp only [tree, toM_corec, PFunctor.M.dest_corec_apply]
    change
      (⟨⟨i, (step i state).1⟩, fun direction =>
          PFunctor.M.corec (totalStep (P := P) step)
            ⟨P.src i (step i state).1 direction,
              (step i state).2 direction⟩⟩ :
        P.sigmaPFunctor.Obj (PFunctor.M P.sigmaPFunctor)) = _
    rw [hStep]
  have hDest := (toM_dest (P := P) tree).symm.trans hUnderlying
  have hRoot : (⟨i, tree.head⟩ : Σ j, P.A j) = ⟨i, shape⟩ :=
    congrArg Sigma.fst hDest
  have hShape : tree.head = shape :=
    eq_of_heq (Sigma.mk.inj hRoot).2
  change tree.dest = _
  apply Sigma.ext hShape
  cases hShape
  apply heq_of_eq
  have hChildren :
      (fun direction => (tree.child direction).toM) =
        (fun direction =>
          (corec (P := P) step _ (children direction)).toM) :=
    eq_of_heq (Sigma.mk.inj hDest).2
  funext direction
  apply ext
  exact congrFun hChildren direction

/-- Indexed corecursion is the unique fiberwise map commuting with the
coalgebra destructors. -/
theorem corec_unique (step : (i : I) → X i → P.Obj X i)
    (f : (i : I) → X i → IM P i)
    (commute : ∀ i state,
      dest (f i state) = P.map (fun j next => f j next) (step i state)) :
    f = fun i state => corec (P := P) step i state := by
  let totalF : (Σ i, X i) → PFunctor.M P.sigmaPFunctor :=
    fun seed => (f seed.1 seed.2).toM
  have hTotal :
      totalF = PFunctor.M.corec (totalStep (P := P) step) := by
    apply PFunctor.M.corec_unique
    rintro ⟨i, state⟩
    change PFunctor.M.dest (f i state).toM = _
    rw [toM_dest, commute]
    rcases hStep : step i state with ⟨shape, children⟩
    change
      (⟨⟨i, shape⟩, fun direction =>
          (f _ (children direction)).toM⟩ :
        P.sigmaPFunctor.Obj (PFunctor.M P.sigmaPFunctor)) =
      ⟨⟨i, (step i state).1⟩, fun direction =>
        (f _ ((step i state).2 direction)).toM⟩
    rw [hStep]
  funext i state
  apply ext
  exact congrFun hTotal ⟨i, state⟩

/-- Corecursing from the indexed destructor is the identity. -/
@[simp]
theorem corec_dest (tree : IM P i) :
    corec (P := P) (fun _ next => dest next) i tree = tree := by
  have h := corec_unique (P := P)
    (fun j (next : IM P j) => dest next)
    (fun _ next => next) (by
      intro _ next
      exact (P.map_id next.dest).symm)
  exact congrFun (congrFun h i) tree |>.symm

end Corec

/-! ## Bisimulation -/

/-- A cast-free bisimulation on indexed M-types.  Related trees destruct to a
common indexed shape, and corresponding children are related in the source
fiber selected by that shape and direction. -/
def IsBisimulation
    (R : (i : I) → IM P i → IM P i → Prop) : Prop :=
  ∀ i left right, R i left right →
    ∃ shape,
      ∃ leftChildren rightChildren :
        (direction : P.B i shape) → IM P (P.src i shape direction),
      dest left = ⟨shape, leftChildren⟩ ∧
      dest right = ⟨shape, rightChildren⟩ ∧
      ∀ direction, R (P.src i shape direction)
        (leftChildren direction) (rightChildren direction)

/-- Indexed bisimulation implies equality.  The proof lifts the relation to
the sigma-erased ordinary M-trees and applies `PFunctor.M.bisim`; clients never
need to cross the representation boundary. -/
theorem bisim
    (R : (i : I) → IM P i → IM P i → Prop)
    (hR : IsBisimulation (P := P) R)
    {i : I} {left right : IM P i} (h : R i left right) :
    left = right := by
  apply ext
  let lifted : PFunctor.M P.sigmaPFunctor →
      PFunctor.M P.sigmaPFunctor → Prop :=
    fun erasedLeft erasedRight =>
      ∃ i, ∃ left right : IM P i,
        R i left right ∧ erasedLeft = left.toM ∧ erasedRight = right.toM
  apply PFunctor.M.bisim lifted
  · intro erasedLeft erasedRight hLifted
    rcases hLifted with
      ⟨index, indexedLeft, indexedRight, hRelated, rfl, rfl⟩
    rcases hR index indexedLeft indexedRight hRelated with
      ⟨shape, leftChildren, rightChildren,
        hLeftDest, hRightDest, hChildren⟩
    refine
      ⟨⟨index, shape⟩,
        (fun direction => (leftChildren direction).toM),
        (fun direction => (rightChildren direction).toM), ?_, ?_, ?_⟩
    · rw [toM_dest, hLeftDest]
      rfl
    · rw [toM_dest, hRightDest]
      rfl
    · intro direction
      exact ⟨P.src index shape direction,
        leftChildren direction, rightChildren direction,
        hChildren direction, rfl, rfl⟩
  · exact ⟨i, left, right, h, rfl, rfl⟩

end IM

end IPFunctor
