/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Polynomial
public import PolyFun.PFunctor.SubstMonoid.Extension

/-!
# Universal property of the free polynomial monad

This file constructs the extension of a generator lens `P ⇆ M.carrier` to a
substitution-monoid homomorphism from `FreeP.substMonoid P` to `M`. The
extension evaluates well-founded `P`-trees using the unit and multiplication
of `M`; its backward direction reconstructs the selected source leaf path.
-/

@[expose] public section

universe uA uB

namespace PFunctor
namespace FreeP

variable {P : PFunctor.{uA, uB}}

/-! ## Generators and folds -/

/-- Embed one generator operation as a one-node tree in `FreeP P`. -/
def generator (P : PFunctor.{uA, uB}) : Lens P (FreeP P) where
  toFunA a := .liftBind a fun _ => .pure PUnit.unit
  toFunB _ path := path.1

@[simp]
theorem generator_toFunA (a : P.A) :
    (generator P).toFunA a =
      FreeM.liftBind a (fun _ => FreeM.pure PUnit.unit) :=
  rfl

@[simp]
theorem generator_toFunB (a : P.A)
    (path : (FreeP P).B ((generator P).toFunA a)) :
    (generator P).toFunB a path = path.1 :=
  rfl

variable (M : SubstMonoid.{max uA uB, uB})
  (l : Lens P M.carrier)

/-- Evaluate an unlabelled free `P`-tree as a position of the substitution
monoid `M`. -/
def foldShape : FreeM P PUnit.{uB + 1} → M.carrier.A
  | .pure _ => M.unit.toFunA PUnit.unit
  | .liftBind a rest =>
      M.mult.toFunA
        ⟨l.toFunA a, fun d => foldShape (rest (l.toFunB a d))⟩

/-- Pull a direction through an evaluated free tree back to the selected
complete source path. -/
def foldPath : (s : FreeM P PUnit.{uB + 1}) →
    M.carrier.B (foldShape M l s) → FreeM.Path s
  | .pure _, _ => ⟨⟩
  | .liftBind a rest, direction =>
      let outer : (M.carrier ◃ M.carrier).A :=
        ⟨l.toFunA a, fun d => foldShape M l (rest (l.toFunB a d))⟩
      let split := M.mult.toFunB outer direction
      ⟨l.toFunB a split.1,
        foldPath (rest (l.toFunB a split.1)) split.2⟩

/-- Extend a generator lens to a lens from the free polynomial monad. -/
def foldLens : Lens (FreeP P) M.carrier where
  toFunA := foldShape M l
  toFunB := foldPath M l

/-- Interpret one generator operation in the extension monad of `M`. -/
def extensionHandler (a : P.A) : M.carrier.Obj (P.B a) :=
  ⟨l.toFunA a, l.toFunB a⟩

/-- Interpret a fixed free-tree shape whose leaves carry the supplied
path-indexed labels. -/
def foldObjAt {α : Type uB} (s : FreeM P PUnit.{uB + 1})
    (label : FreeM.Path s → α) : M.carrier.Obj α :=
  FreeM.liftM (extensionHandler M l) (decodeAt s label)

/-- Interpret the path-labelled object represented by an unlabelled free tree.
This is the ordinary `FreeM.liftM` fold into the extension monad of `M`. -/
def foldObj (s : FreeM P PUnit.{uB + 1}) :
    M.carrier.Obj (FreeM.Path s) :=
  foldObjAt M l s id

/-- The extension-level `FreeM` fold is exactly the position-and-path package
used by `foldLens`. -/
theorem foldObjAt_eq {α : Type uB}
    (s : FreeM P PUnit.{uB + 1}) (label : FreeM.Path s → α) :
    foldObjAt M l s label =
      (⟨foldShape M l s, label ∘ foldPath M l s⟩ :
        M.carrier.Obj α) := by
  match s with
  | .pure u =>
      cases u
      rfl
  | .liftBind a rest =>
      change
        extensionHandler M l a >>= (fun d =>
          foldObjAt M l (rest d)
            (fun path => label (FreeM.Path.cons a rest d path))) = _
      have hcont :
          (fun d => foldObjAt M l (rest d)
            (fun path => label (FreeM.Path.cons a rest d path))) =
          (fun d =>
            (⟨foldShape M l (rest d),
              (fun path => label (FreeM.Path.cons a rest d path)) ∘
                foldPath M l (rest d)⟩ : M.carrier.Obj α)) := by
        funext d
        exact foldObjAt_eq (rest d)
          (fun path => label (FreeM.Path.cons a rest d path))
      rw [hcont]
      rfl

/-- The extension-level `FreeM` fold is exactly the position-and-path package
used by `foldLens`. -/
theorem foldObj_eq (s : FreeM P PUnit.{uB + 1}) :
    foldObj M l s =
      (⟨foldShape M l s, foldPath M l s⟩ :
        M.carrier.Obj (FreeM.Path s)) := by
  simpa [foldObj, Function.comp_def] using foldObjAt_eq M l s id

@[simp]
theorem foldLens_toFunA (s : (FreeP P).A) :
    (foldLens M l).toFunA s = foldShape M l s :=
  rfl

@[simp]
theorem foldLens_toFunB (s : (FreeP P).A)
    (direction : M.carrier.B ((foldLens M l).toFunA s)) :
    (foldLens M l).toFunB s direction = foldPath M l s direction :=
  rfl

/-- The fold agrees with the target substitution unit on the one-leaf tree. -/
theorem foldLens_comp_unit :
    foldLens M l ∘ₗ unit (P := P) = M.unit := by
  apply Lens.ext _ _ (fun _ => rfl)
  intro _
  exact Subsingleton.elim _ _

/-- `foldObjAt` sends free-tree grafting to bind in the extension monad. -/
theorem foldObjAt_append_split {α : Type uB}
    (s : FreeM P PUnit.{uB + 1})
    (next : FreeM.Path s → FreeM P PUnit.{uB + 1})
    (label : ((path : FreeM.Path s) × FreeM.Path (next path)) → α) :
    foldObjAt M l (FreeM.append s next)
        (fun path => label (FreeM.Path.split s next path)) =
      foldObjAt M l s id >>= fun path =>
        foldObjAt M l (next path) (fun inner => label ⟨path, inner⟩) := by
  unfold foldObjAt
  rw [decodeAt_append_split, ← FreeM.monad_bind_def, FreeM.liftM_bind]

/-- Pointwise container form of multiplication preservation by `foldLens`.
Both the evaluated position and the reconstructed pair of source paths are
checked at once. -/
theorem foldLens_mult_obj
    (s : FreeM P PUnit.{uB + 1})
    (next : FreeM.Path s → FreeM P PUnit.{uB + 1}) :
    let x : (FreeP P ◃ FreeP P).A := ⟨s, next⟩
    Lens.mapObj (foldLens M l ∘ₗ mult (P := P))
        (⟨x, id⟩ : (FreeP P ◃ FreeP P).Obj
          ((FreeP P ◃ FreeP P).B x)) =
      Lens.mapObj (M.mult ∘ₗ (foldLens M l ◃ₗ foldLens M l))
        (⟨x, id⟩ : (FreeP P ◃ FreeP P).Obj
          ((FreeP P ◃ FreeP P).B x)) := by
  dsimp only
  have h := foldObjAt_append_split M l s next id
  rw [foldObjAt_eq M l (FreeM.append s next)] at h
  have houter : foldObjAt M l s id =
      (⟨foldShape M l s, foldPath M l s⟩ :
        M.carrier.Obj (FreeM.Path s)) := by
    simpa [Function.comp_def] using foldObjAt_eq M l s id
  have hinner :
      (fun path => foldObjAt M l (next path)
        (fun inner =>
          (⟨path, inner⟩ :
            (outer : FreeM.Path s) × FreeM.Path (next outer)))) =
      (fun path =>
        (⟨foldShape M l (next path),
          (fun inner =>
            (⟨path, inner⟩ :
              (outer : FreeM.Path s) × FreeM.Path (next outer))) ∘
            foldPath M l (next path)⟩ :
          M.carrier.Obj
            ((outer : FreeM.Path s) × FreeM.Path (next outer)))) := by
    funext path
    exact foldObjAt_eq M l (next path) (fun inner =>
      (⟨path, inner⟩ :
        (outer : FreeM.Path s) × FreeM.Path (next outer)))
  dsimp only [id] at h
  rw [houter, hinner] at h
  simpa [PFunctor.comp, Lens.mapObj, Lens.comp, Lens.compMap,
    foldLens, mult,
    SubstMonoid.Extension.bind,
    Function.comp_def] using h

/-- The free fold preserves substitution multiplication as a full lens,
including its backward path map. -/
theorem foldLens_comp_mult :
    foldLens M l ∘ₗ mult (P := P) =
      M.mult ∘ₗ (foldLens M l ◃ₗ foldLens M l) := by
  apply Lens.ext_mapObj
  rintro ⟨s, next⟩
  exact foldLens_mult_obj M l s next

/-- Extend a generator lens uniquely to a substitution-monoid homomorphism
out of the free substitution monoid. -/
def extend : SubstMonoid.Hom (substMonoid P) M where
  toLens := foldLens M l
  map_unit := foldLens_comp_unit M l
  map_mult := foldLens_comp_mult M l

/-- Pointwise container form of the fact that extending a lens and then
restricting to one-node generators recovers the original lens. -/
theorem foldLens_comp_generator_obj (a : P.A) :
    Lens.mapObj (foldLens M l ∘ₗ generator P)
        (⟨a, id⟩ : P.Obj (P.B a)) =
      Lens.mapObj l (⟨a, id⟩ : P.Obj (P.B a)) := by
  have hinterp : foldObjAt M l
      (FreeM.liftBind a (fun _ => FreeM.pure PUnit.unit))
      (fun path => path.1) = extensionHandler M l a := by
    change extensionHandler M l a >>= (fun d =>
      (Pure.pure d : SubstMonoid.Extension M (P.B a))) =
        extensionHandler M l a
    exact SubstMonoid.Extension.bind_pure M (extensionHandler M l a)
  rw [foldObjAt_eq] at hinterp
  simpa [Lens.mapObj, Lens.comp, foldLens, generator,
    extensionHandler, Function.comp_def] using hinterp

/-- The free fold extends the supplied generator lens. -/
theorem foldLens_comp_generator :
    foldLens M l ∘ₗ generator P = l := by
  apply Lens.ext_mapObj
  intro a
  exact foldLens_comp_generator_obj M l a

/-- Folding into the free substitution monoid with its own generator is the
identity on every path-labelled free-tree object. -/
theorem foldObjAt_generator_eq {α : Type uB}
    (s : FreeM P PUnit.{uB + 1}) (label : FreeM.Path s → α) :
    foldObjAt (substMonoid P) (generator P) s label =
      (⟨s, label⟩ : (FreeP P).Obj α) := by
  match s with
  | .pure u =>
      cases u
      rfl
  | .liftBind a rest =>
      change extensionHandler (substMonoid P) (generator P) a >>=
        (fun d => foldObjAt (substMonoid P) (generator P) (rest d)
          (fun path => label (FreeM.Path.cons a rest d path))) = _
      have hcont :
          (fun d => foldObjAt (substMonoid P) (generator P) (rest d)
            (fun path => label (FreeM.Path.cons a rest d path))) =
          (fun d =>
            (⟨rest d, fun path =>
              label (FreeM.Path.cons a rest d path)⟩ :
              (FreeP P).Obj α)) := by
        funext d
        exact foldObjAt_generator_eq (rest d)
          (fun path => label (FreeM.Path.cons a rest d path))
      rw [hcont]
      rfl

variable {Q : PFunctor.{uA, uB}}

/-- For signatures in the same universe pair, the universal fold into the
free target substitution monoid is the existing nodewise `FreeP.map`. -/
theorem foldObjAt_generator_comp_eq (lPQ : Lens P Q)
    {α : Type uB} (s : FreeM P PUnit.{uB + 1})
    (label : FreeM.Path s → α) :
    foldObjAt (substMonoid Q) (generator Q ∘ₗ lPQ) s label =
      Lens.mapObj (map lPQ) (⟨s, label⟩ : (FreeP P).Obj α) := by
  match s with
  | .pure u =>
      cases u
      rfl
  | .liftBind a rest =>
      change extensionHandler (substMonoid Q) (generator Q ∘ₗ lPQ) a >>=
        (fun d => foldObjAt (substMonoid Q) (generator Q ∘ₗ lPQ)
          (rest d) (fun path =>
            label (FreeM.Path.cons a rest d path))) = _
      have hcont :
          (fun d => foldObjAt (substMonoid Q) (generator Q ∘ₗ lPQ)
            (rest d) (fun path =>
              label (FreeM.Path.cons a rest d path))) =
          (fun d => Lens.mapObj (map lPQ)
            (⟨rest d, fun path =>
              label (FreeM.Path.cons a rest d path)⟩ :
              (FreeP P).Obj α)) := by
        funext d
        exact foldObjAt_generator_comp_eq lPQ (rest d)
          (fun path => label (FreeM.Path.cons a rest d path))
      rw [hcont]
      rfl

/-- Lens-level form of `foldObjAt_generator_comp_eq`. -/
theorem foldLens_generator_comp (lPQ : Lens P Q) :
    foldLens (substMonoid Q) (generator Q ∘ₗ lPQ) = map lPQ := by
  let hobj : ∀ s,
      (⟨(foldLens (substMonoid Q) (generator Q ∘ₗ lPQ)).toFunA s,
        (foldLens (substMonoid Q) (generator Q ∘ₗ lPQ)).toFunB s⟩ :
        (FreeP Q).Obj ((FreeP P).B s)) =
      ⟨(map lPQ).toFunA s, (map lPQ).toFunB s⟩ := fun s => by
    have h := foldObjAt_generator_comp_eq lPQ s id
    rw [foldObjAt_eq] at h
    change
      (⟨(foldLens (substMonoid Q)
          (generator Q ∘ₗ lPQ)).toFunA s,
        (foldLens (substMonoid Q)
          (generator Q ∘ₗ lPQ)).toFunB s⟩ :
        (FreeP Q).Obj ((FreeP P).B s)) =
      ⟨(map lPQ).toFunA s, (map lPQ).toFunB s⟩ at h
    exact h
  apply Lens.ext_mapObj
  exact hobj

/-- `FreeP.map` packaged as the substitution-monoid homomorphism induced by
a generator lens. -/
def mapHom (lPQ : Lens P Q) :
    SubstMonoid.Hom (substMonoid P) (substMonoid Q) where
  toLens := map lPQ
  map_unit := by
    rw [← foldLens_generator_comp lPQ]
    exact foldLens_comp_unit (substMonoid Q) (generator Q ∘ₗ lPQ)
  map_mult := by
    rw [← foldLens_generator_comp lPQ]
    exact foldLens_comp_mult (substMonoid Q) (generator Q ∘ₗ lPQ)

@[simp]
theorem mapHom_toLens (lPQ : Lens P Q) :
    (mapHom lPQ).toLens = map lPQ :=
  rfl

@[simp]
theorem mapHom_id : mapHom (Lens.id P) =
    SubstMonoid.Hom.id (substMonoid P) :=
  SubstMonoid.Hom.ext _ _ map_id

variable {R : PFunctor.{uA, uB}}

@[simp]
theorem mapHom_comp (lPQ : Lens P Q) (lQR : Lens Q R) :
    (mapHom lPQ).comp (mapHom lQR) = mapHom (lQR ∘ₗ lPQ) :=
  SubstMonoid.Hom.ext _ _ (map_comp lQR lPQ)

/-- Evaluating a grafted free tree agrees on positions with multiplying the
evaluated outer tree by the evaluated inner trees. -/
theorem foldShape_append (s : FreeM P PUnit.{uB + 1})
    (next : FreeM.Path s → FreeM P PUnit.{uB + 1}) :
    foldShape M l (FreeM.append s next) =
      M.mult.toFunA
        ⟨foldShape M l s,
          fun direction =>
            foldShape M l (next (foldPath M l s direction))⟩ := by
  have h := congrArg Sigma.fst (foldLens_mult_obj M l s next)
  simpa [Lens.mapObj, Lens.comp, Lens.compMap, foldLens, mult,
    Function.comp_def] using h

/-! ## Restriction -/

/-- Restrict a substitution-monoid homomorphism from the free monoid to its
one-node generators. -/
def restrict (f : SubstMonoid.Hom (substMonoid P) M) :
    Lens P M.carrier :=
  f.toLens ∘ₗ generator P

@[simp]
theorem restrict_extend : restrict M (extend M l) = l :=
  foldLens_comp_generator M l

/-- Restriction is the extension-level image of the free generator handler. -/
theorem extensionHandler_restrict
    (f : SubstMonoid.Hom (substMonoid P) M) (a : P.A) :
    extensionHandler M (restrict M f) a =
      f.toMonadHom
        (extensionHandler (substMonoid P) (generator P) a) :=
  rfl

/-- Naturality of the ordinary `FreeM.liftM` fold identifies a homomorphism's
action on a free-tree object with folding its restriction to generators. -/
theorem hom_mapObj_eq_foldObjAt
    (f : SubstMonoid.Hom (substMonoid P) M)
    (s : FreeM P PUnit.{uB + 1}) {α : Type uB}
    (label : FreeM.Path s → α) :
    Lens.mapObj f.toLens (⟨s, label⟩ : (FreeP P).Obj α) =
      foldObjAt M (restrict M f) s label := by
  have h := FreeM.liftM_natural
    (extensionHandler (substMonoid P) (generator P))
    f.toMonadHom (decodeAt s label)
  have hhandler :
      (fun a => f.toMonadHom
        (extensionHandler (substMonoid P) (generator P) a)) =
      extensionHandler M (restrict M f) := by
    funext a
    exact (extensionHandler_restrict M f a).symm
  rw [hhandler] at h
  change f.toMonadHom (foldObjAt (substMonoid P) (generator P) s label) =
    foldObjAt M (restrict M f) s label at h
  rw [foldObjAt_generator_eq] at h
  exact h

/-- Extending the restriction of a free substitution-monoid homomorphism
recovers the original homomorphism. -/
@[simp]
theorem extend_restrict
    (f : SubstMonoid.Hom (substMonoid P) M) :
    extend M (restrict M f) = f := by
  apply SubstMonoid.Hom.ext
  let hobj : ∀ s,
      (⟨foldShape M (restrict M f) s,
        foldPath M (restrict M f) s⟩ :
        M.carrier.Obj ((FreeP P).B s)) =
      ⟨f.toLens.toFunA s, f.toLens.toFunB s⟩ := fun s => by
    have h := hom_mapObj_eq_foldObjAt M f s id
    rw [foldObjAt_eq] at h
    change (⟨f.toLens.toFunA s, f.toLens.toFunB s⟩ :
      M.carrier.Obj ((FreeP P).B s)) =
        ⟨foldShape M (restrict M f) s,
          foldPath M (restrict M f) s⟩ at h
    exact h.symm
  apply Lens.ext_mapObj
  exact hobj

/-- A homomorphism out of the free substitution monoid is uniquely determined
by its restriction to the generator polynomial. -/
theorem extend_unique (f : SubstMonoid.Hom (substMonoid P) M)
    (h : f.toLens ∘ₗ generator P = l) : f = extend M l := by
  calc
    f = extend M (restrict M f) := (extend_restrict M f).symm
    _ = extend M l := congrArg (extend M) h

/-- The universal property of the free substitution monoid: homomorphisms
out of `substMonoid P` are equivalent to lenses out of the generator
polynomial `P`. -/
def homEquiv :
    SubstMonoid.Hom (substMonoid P) M ≃ Lens P M.carrier where
  toFun := restrict M
  invFun := extend M
  left_inv := extend_restrict M
  right_inv := restrict_extend M

end FreeP
end PFunctor
