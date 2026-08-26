/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.M.Vertex

/-!
# Well-founded M-type trees

The canonical map from the initial algebra `P.W` to the final coalgebra
`P.M` regards a well-founded polynomial tree as a possibly infinite one.
Its exact image consists of the M-type trees accessible under the immediate
child relation. This file packages that statement as an equivalence and gives
the lens-naturality laws needed by the higher free/resumption bridges.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uA₃ uB₃

namespace PFunctor

/- Lean 4.33 compares dependent W/M indices at implicit transparency in the
proofs below. These local attributes expose only the thin type aliases and
recursive bridge applications needed by those checks. -/
attribute [local implicit_reducible] PFunctor.Obj PFunctor.W

namespace M

variable {P : PFunctor.{uA, uB}}

/-- The immediate-child relation of an M-type tree, stated through `M.dest`
so clients do not need dependent transports through `M.head`. -/
def Child (child parent : M P) : Prop :=
  ∃ position : P.A, ∃ next : P.B position → M P,
    ∃ direction : P.B position,
      M.dest parent = ⟨position, next⟩ ∧ child = next direction

/-- An M-type tree is well-founded when every chain of immediate children is
finite. Different branches need not share a uniform natural-number bound. -/
abbrev WellFounded (tree : M P) : Prop :=
  Acc (Child (P := P)) tree

theorem child_of_dest (tree : M P) (position : P.A)
    (next : P.B position → M P) (direction : P.B position)
    (h : M.dest tree = ⟨position, next⟩) :
    Child (next direction) tree :=
  ⟨position, next, direction, h, rfl⟩

/-- Accessibility of a polynomial tree is equivalent to accessibility of all
immediate subtrees exposed by one destructor step. -/
theorem wellFounded_iff_of_dest (tree : M P) (position : P.A)
    (next : P.B position → M P) (h : M.dest tree = ⟨position, next⟩) :
    WellFounded tree ↔ ∀ direction, WellFounded (next direction) := by
  constructor
  · intro accessibility direction
    exact accessibility.inv (child_of_dest tree position next direction h)
  · intro children
    constructor
    rintro child ⟨position', next', direction, hdest, rfl⟩
    have hstep : (⟨position', next'⟩ : P.Obj (M P)) = ⟨position, next⟩ :=
      hdest.symm.trans h
    have hposition : position' = position := (Sigma.mk.inj hstep).1
    subst position'
    have hnext : next' = next := eq_of_heq (Sigma.mk.inj hstep).2
    subst next'
    exact children direction

end M

namespace W

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
  {R : PFunctor.{uA₃, uB₃}}

/-- Transport a W-type tree along a polynomial lens. -/
def mapLens (lens : Lens P Q) : P.W → Q.W
  | ⟨position, next⟩ =>
      ⟨lens.toFunA position, fun direction =>
        mapLens lens (next (lens.toFunB position direction))⟩

@[simp] theorem mapLens_mk (lens : Lens P Q) (position : P.A)
    (next : P.B position → P.W) :
    mapLens lens ⟨position, next⟩ =
      ⟨lens.toFunA position, fun direction =>
        mapLens lens (next (lens.toFunB position direction))⟩ :=
  rfl

@[simp] theorem mapLens_id (tree : P.W) :
    mapLens (Lens.id P) tree = tree := by
  induction tree with
  | mk position next ih =>
      exact congrArg (WType.mk position) (funext ih)

@[simp] theorem mapLens_comp (second : Lens Q R) (first : Lens P Q)
    (tree : P.W) :
    mapLens second (mapLens first tree) =
      mapLens (second ∘ₗ first) tree := by
  induction tree with
  | mk position next ih =>
      apply congrArg (WType.mk (second.toFunA (first.toFunA position)))
      funext direction
      exact ih (first.toFunB position (second.toFunB (first.toFunA position) direction))

/-- Regard a well-founded polynomial tree as an M-type tree. -/
def toM : P.W → P.M
  | ⟨position, next⟩ =>
      M.mk ⟨position, fun direction => toM (next direction)⟩

attribute [local implicit_reducible] toM mapLens

@[simp] theorem dest_toM (tree : P.W) :
    M.dest (toM tree) =
      ⟨W.head tree, fun direction => toM (W.children tree direction)⟩ := by
  rcases tree with ⟨position, next⟩
  exact M.dest_mk _

/-- Every embedded W-tree is accessible under the M-type child relation. -/
theorem wellFounded_toM (tree : P.W) : M.WellFounded (toM tree) := by
  induction tree with
  | mk position next ih =>
      constructor
      rintro child ⟨position', next', direction, hdest, rfl⟩
      rw [dest_toM] at hdest
      have hposition : position = position' := (Sigma.mk.inj hdest).1
      subst position'
      have hnext : (fun d => toM (next d)) = next' :=
        eq_of_heq (Sigma.mk.inj hdest).2
      subst next'
      exact ih direction

/-- Mapping a W-tree and then embedding it agrees with mapping its M-tree. -/
theorem toM_mapLens (lens : Lens P Q) (tree : P.W) :
    toM (mapLens lens tree) = M.mapLens lens (toM tree) := by
  induction tree with
  | mk position next ih =>
      apply M.eq_of_dest_eq
      change
        (⟨lens.toFunA position, fun direction =>
          toM (mapLens lens (next (lens.toFunB position direction)))⟩ : Q.Obj (M Q)) =
        ⟨lens.toFunA position, fun direction =>
          M.mapLens lens (toM (next (lens.toFunB position direction)))⟩
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext direction
        exact ih (lens.toFunB position direction)

end W

namespace M

variable {P : PFunctor.{uA, uB}}

/-- Extract the W-type tree represented by an accessible M-type tree. -/
def toW : (tree : M P) → WellFounded tree → P.W :=
  fun _ accessibility =>
    Acc.recC (motive := fun _ _ => P.W)
      (fun current _ recurse =>
        WType.mk (M.dest current).1 fun direction =>
          recurse ((M.dest current).2 direction)
            (child_of_dest current (M.dest current).1 (M.dest current).2
              direction rfl))
      accessibility

attribute [local implicit_reducible] toW

theorem toW_eq (tree : M P) (accessibility : WellFounded tree) :
    toW tree accessibility =
      WType.mk (M.dest tree).1 fun direction =>
        toW ((M.dest tree).2 direction)
          (accessibility.inv
            (child_of_dest tree (M.dest tree).1 (M.dest tree).2 direction rfl)) := by
  unfold toW
  rw [← Acc.rec_eq_recC]
  cases accessibility
  rfl

/-- Extraction is independent of the accessibility witness. -/
theorem toW_proof_irrel (tree : M P) (first second : WellFounded tree) :
    toW tree first = toW tree second := by
  congr

@[simp] theorem toW_toM (tree : P.W) :
    toW (W.toM tree) (W.wellFounded_toM tree) = tree := by
  induction tree with
  | mk position next ih =>
      rw [toW_eq]
      cases (W.dest_toM (P := P) (WType.mk position next)).symm
      apply congrArg (WType.mk position)
      funext direction
      exact (toW_proof_irrel _ _ _).trans (ih direction)

theorem toM_toW (tree : M P) (accessibility : WellFounded tree) :
    W.toM (toW tree accessibility) = tree := by
  induction accessibility with
  | intro current below ih =>
      rw [toW_eq current (Acc.intro current below)]
      apply M.eq_of_dest_eq
      rw [W.dest_toM]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext direction
        exact ih ((M.dest current).2 direction)
          (child_of_dest current (M.dest current).1 (M.dest current).2 direction rfl)

end M

namespace W

variable {P : PFunctor.{uA, uB}}

/-- W-types are exactly the well-founded fragment of M-types. -/
def equivWellFoundedM : P.W ≃ {tree : M P // M.WellFounded tree} where
  toFun tree := ⟨toM tree, wellFounded_toM tree⟩
  invFun tree := M.toW tree.1 tree.2
  left_inv := M.toW_toM
  right_inv tree := Subtype.ext (M.toM_toW tree.1 tree.2)

theorem toM_injective : Function.Injective (toM : P.W → M P) :=
  fun _ _ h => equivWellFoundedM.injective (Subtype.ext h)

end W

end PFunctor
