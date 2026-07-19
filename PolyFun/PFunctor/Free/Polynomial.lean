/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Path
public import PolyFun.PFunctor.SubstMonoid

/-!
# The free polynomial monad

For a polynomial `p`, `FreeP p` is the polynomial whose positions are
well-founded `p`-trees with unlabelled leaves and whose directions are complete
root-to-leaf paths. Labelling every direction by `X` recovers the ordinary free
monad `FreeM p X`.

This is the direct W-type presentation of the free polynomial monad in
Libkind–Spivak, *Pattern Runs on Matter*. The paper constructs the same object
through transfinite stages; the inductive `FreeM` presentation records the
resulting well-founded tree directly.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uA₃ uB₃ v w x

namespace PFunctor

/-- The polynomial of well-founded `P`-trees and their complete leaf paths.

This definition is reducible so that its position and direction projections
elaborate as `FreeM` trees and `FreeM.Path` without exposing casts to clients. -/
@[reducible]
def FreeP (P : PFunctor.{uA, uB}) : PFunctor.{max uA uB, uB} :=
  ⟨FreeM P PUnit.{uB + 1}, FreeM.Path⟩

namespace FreeP

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-! ## Polynomial extension and `FreeM` -/

/-- Construct one `FreeP` operation node from its path-labelled children. -/
def node (a : P.A)
    (children : P.B a →
      (Σ s : FreeM P PUnit.{uB + 1}, FreeM.Path s → α)) :
    Σ s : FreeM P PUnit.{uB + 1}, FreeM.Path s → α :=
  let rest := fun b => (children b).1
  ⟨.liftBind a rest, fun path =>
    let b := FreeM.Path.head a rest path
    (children b).2 (FreeM.Path.tail a rest path)⟩

/-- Erase the leaf labels of a free tree while recording each label at its
complete path. -/
def encode : FreeM P α →
    (Σ s : FreeM P PUnit.{uB + 1}, FreeM.Path s → α)
  | .pure x => ⟨.pure PUnit.unit, fun _ => x⟩
  | .liftBind a rest => node a fun b => encode (rest b)

/-- Label the leaves of a fixed unlabelled tree using its path-indexed
payload. -/
def decodeAt : (s : FreeM P PUnit.{uB + 1}) →
    (FreeM.Path s → α) → FreeM P α
  | .pure _, label => .pure (label ⟨⟩)
  | .liftBind a rest, label =>
      .liftBind a fun b =>
        decodeAt (rest b) (fun path => label (FreeM.Path.cons a rest b path))

/-- Label the leaves of an unlabelled free tree using its path-indexed
payload. -/
def decode (x : Σ s : FreeM P PUnit.{uB + 1}, FreeM.Path s → α) :
    FreeM P α :=
  decodeAt x.1 x.2

/-- Decoding a labelled polynomial node is `FreeM.liftBind` of the decoded
children. -/
theorem decode_node (a : P.A)
    (children : P.B a → (FreeP P).Obj α) :
    decode (node a children) =
      FreeM.liftBind a (fun direction => decode (children direction)) :=
  rfl

@[simp]
theorem decode_encode : (s : FreeM P α) → decode (encode s) = s
  | .pure _ => rfl
  | .liftBind a rest => by
      change FreeM.liftBind a (fun b => decode (encode (rest b))) =
        FreeM.liftBind a rest
      apply congrArg (FreeM.liftBind a)
      funext b
      exact decode_encode (rest b)

/-- Constructing a node from the childwise restrictions of a path labelling
recovers the original labelled node. -/
theorem node_paths (a : P.A)
    (rest : P.B a → FreeM P PUnit.{uB + 1})
    (label : FreeM.Path (FreeM.liftBind a rest) → α) :
    node a (fun b =>
      (⟨rest b, fun path => label (FreeM.Path.cons a rest b path)⟩ :
        Σ s : FreeM P PUnit.{uB + 1}, FreeM.Path s → α)) =
      ⟨.liftBind a rest, label⟩ := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext path
  rcases path with ⟨b, path⟩
  rfl

theorem encode_decodeAt (s : FreeM P PUnit.{uB + 1})
    (label : FreeM.Path s → α) :
    encode (decodeAt s label) = ⟨s, label⟩ := by
  match s with
  | .pure u =>
      cases u
      refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext path
      cases path
      rfl
  | .liftBind a rest =>
      change
        node a (fun b => encode (decodeAt (rest b)
          (fun path => label (FreeM.Path.cons a rest b path)))) =
        ⟨.liftBind a rest, label⟩
      have hchildren :
          (fun b => encode (decodeAt (rest b)
            (fun path => label (FreeM.Path.cons a rest b path)))) =
          (fun b => (⟨rest b,
            fun path => label (FreeM.Path.cons a rest b path)⟩ :
            Σ s : FreeM P PUnit.{uB + 1}, FreeM.Path s → α)) := by
        funext b
        exact encode_decodeAt (rest b)
          (fun path => label (FreeM.Path.cons a rest b path))
      rw [hchildren]
      exact node_paths a rest label

@[simp]
theorem encode_decode (x : (FreeP P).Obj α) : encode (decode x) = x := by
  rcases x with ⟨s, label⟩
  exact encode_decodeAt s label

/-- Binding a decoded tree depends on a leaf label only through the
continuation selected by that label. -/
theorem decodeAt_bind {α β : Type uB}
    (s : FreeM P PUnit.{uB + 1}) (label : FreeM.Path s → α)
    (next : α → FreeM P β) :
    FreeM.bind (decodeAt s label) next =
      FreeM.bind (decodeAt s id) (fun path => next (label path)) := by
  match s with
  | .pure u =>
      cases u
      rfl
  | .liftBind a rest =>
      simp only [decodeAt, FreeM.bind]
      apply congrArg (FreeM.liftBind a)
      funext d
      calc
        FreeM.bind
            (decodeAt (rest d)
              (fun path => label (FreeM.Path.cons a rest d path))) next =
            FreeM.bind (decodeAt (rest d) id) (fun path =>
              next (label (FreeM.Path.cons a rest d path))) :=
          decodeAt_bind (rest d)
            (fun path => label (FreeM.Path.cons a rest d path)) next
        _ = FreeM.bind
            (decodeAt (rest d)
              (fun path => FreeM.Path.cons a rest d path))
            (fun path => next (label path)) :=
          (decodeAt_bind (rest d)
            (fun path => FreeM.Path.cons a rest d path)
            (fun path => next (label path))).symm

/-- Decoding a grafted tree with its path split as payload is ordinary
free-monad bind of the separately decoded outer and inner trees. -/
theorem decodeAt_append_split {α : Type uB}
    (s : FreeM P PUnit.{uB + 1})
    (next : FreeM.Path s → FreeM P PUnit.{uB + 1})
    (label : ((path : FreeM.Path s) × FreeM.Path (next path)) → α) :
    decodeAt (FreeM.append s next)
        (fun path => label (FreeM.Path.split s next path)) =
      FreeM.bind (decodeAt s id) (fun path =>
        decodeAt (next path) (fun inner => label ⟨path, inner⟩)) := by
  match s with
  | .pure u =>
      cases u
      rfl
  | .liftBind a rest =>
      simp only [FreeM.append, decodeAt, FreeM.bind]
      apply congrArg (FreeM.liftBind a)
      funext d
      exact (decodeAt_append_split (rest d)
          (fun path => next (FreeM.Path.cons a rest d path))
          (fun pair => label
            ⟨FreeM.Path.cons a rest d pair.1, pair.2⟩)).trans
        (decodeAt_bind (rest d)
          (fun path => FreeM.Path.cons a rest d path)
          (fun path => decodeAt (next path)
            (fun inner => label ⟨path, inner⟩))).symm

/-- Labelling the leaves of an unlabelled `P`-tree is equivalent to an
ordinary free-monad computation. -/
def objEquiv : (FreeP P).Obj α ≃ FreeM P α where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

/-- Relabel the payload stored at every path of a `FreeP` object without
changing its tree shape. -/
def relabel {β : Type w} (f : α → β) (x : (FreeP P).Obj α) :
    (FreeP P).Obj β :=
  ⟨x.1, f ∘ x.2⟩

/-- Decoding after relabelling is ordinary free-monad mapping. -/
@[simp]
theorem decode_relabel {β : Type w} (f : α → β)
    (x : (FreeP P).Obj α) :
    decode (relabel f x) = FreeM.map f (decode x) := by
  rcases x with ⟨shape, labels⟩
  induction shape with
  | pure value =>
      cases value
      rfl
  | liftBind a rest ih =>
      simp only [decode, decodeAt, relabel, Function.comp_apply, FreeM.map]
      apply congrArg (FreeM.liftBind a)
      funext direction
      exact ih direction
        (fun path => labels (FreeM.Path.cons a rest direction path))

@[simp]
theorem relabel_node {β : Type w} (f : α → β) (a : P.A)
    (children : P.B a → (FreeP P).Obj α) :
    relabel f (node a children) =
      node a (fun direction => relabel f (children direction)) :=
  rfl

@[simp]
theorem relabel_relabel {β : Type w} {γ : Type x}
    (g : β → γ) (f : α → β) (x : (FreeP P).Obj α) :
    relabel g (relabel f x) = relabel (g ∘ f) x :=
  rfl

/-! ## Functoriality in the generating polynomial -/

variable {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- Map an unlabelled `P`-tree into the target signature and relabel its unit
leaves into the target direction universe. -/
def mapShape (l : Lens P Q) (s : (FreeP P).A) : (FreeP Q).A :=
  (s.mapLens l).map fun _ => PUnit.unit

/-- A lens between signatures maps well-founded operation trees nodewise and
pulls each resulting leaf path back through the lens. -/
def map (l : Lens P Q) : Lens (FreeP P) (FreeP Q) where
  toFunA := mapShape l
  toFunB s path :=
    FreeM.Path.pullMapLens l s
      (FreeM.Path.pullMap (fun _ => PUnit.unit) (s.mapLens l) path)

@[simp]
theorem map_toFunA (l : Lens P Q) (s : (FreeP P).A) :
    (map l).toFunA s = mapShape l s :=
  rfl

@[simp]
theorem map_toFunB (l : Lens P Q) (s : (FreeP P).A)
    (path : (FreeP Q).B ((map l).toFunA s)) :
    (map l).toFunB s path =
      FreeM.Path.pullMapLens l s
        (FreeM.Path.pullMap (fun _ => PUnit.unit) (s.mapLens l) path) :=
  rfl

/-- Pulling back a complete path through a mapped operation node pulls back
its root direction and then recursively pulls back the child path. -/
theorem map_toFunB_cons (l : Lens P Q) (a : P.A)
    (rest : P.B a → FreeM P PUnit.{uB + 1})
    (direction : Q.B (l.toFunA a))
    (path : FreeM.Path
      (FreeM.map (fun _ => PUnit.unit)
        (FreeM.mapLens l (rest (l.toFunB a direction))))) :
    (map l).toFunB (FreeM.liftBind a rest)
        (FreeM.Path.cons (l.toFunA a)
          (fun d => FreeM.map (fun _ => PUnit.unit)
            (FreeM.mapLens l (rest (l.toFunB a d))))
          direction path) =
      FreeM.Path.cons a rest (l.toFunB a direction)
        ((map l).toFunB (rest (l.toFunB a direction)) path) :=
  rfl

/-- Mapping a labelled free node maps its operation and each child
recursively, pulling the target direction back through the generating lens. -/
@[simp]
theorem mapObj_node (l : Lens P Q) (a : P.A)
    (children : P.B a → (FreeP P).Obj α) :
    Lens.mapObj (map l) (node a children) =
      node (l.toFunA a) (fun direction =>
        Lens.mapObj (map l) (children (l.toFunB a direction))) :=
  rfl

@[simp]
theorem mapObj_relabel {β : Type w} (l : Lens P Q)
    (f : α → β) (x : (FreeP P).Obj α) :
    Lens.mapObj (map l) (relabel f x) =
      relabel f (Lens.mapObj (map l) x) :=
  rfl

/-- Mapping a labelled `FreeP` object along a signature lens corresponds under
`objEquiv` to mapping the decoded free-monad tree along that lens. -/
@[simp]
theorem decode_map (l : Lens P Q) (x : (FreeP P).Obj α) :
    decode (Lens.mapObj (map l) x) = (decode x).mapLens l := by
  rcases x with ⟨s, label⟩
  induction s with
  | pure u =>
      cases u
      rfl
  | liftBind a rest ih =>
      simp only [Lens.mapObj, map, mapShape, decode, decodeAt, FreeM.mapLens,
        FreeM.map, Function.comp_apply]
      apply congrArg (FreeM.liftBind (l.toFunA a))
      funext d
      exact ih (l.toFunB a d) (fun path ↦ label ⟨l.toFunB a d, path⟩)

/-- Pointwise container form of the identity law for `FreeP.map`. Packaging
the mapped shape together with its pulled-back path avoids exposing a cast in
the public functor law. -/
theorem map_obj_id (s : (FreeP P).A) :
    (⟨mapShape (Lens.id P) s, (map (Lens.id P)).toFunB s⟩ :
      (FreeP P).Obj (FreeM.Path s)) =
    ⟨s, id⟩ := by
  match s with
  | .pure u =>
      cases u
      refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext path
      cases path
      rfl
  | .liftBind a rest =>
      change
        node a (fun b => relabel (FreeM.Path.cons a rest b)
          (⟨mapShape (Lens.id P) (rest b),
            (map (Lens.id P)).toFunB (rest b)⟩ :
              (FreeP P).Obj (FreeM.Path (rest b)))) =
        ⟨.liftBind a rest, id⟩
      have hchildren :
          (fun b => relabel (FreeM.Path.cons a rest b)
            (⟨mapShape (Lens.id P) (rest b),
              (map (Lens.id P)).toFunB (rest b)⟩ :
                (FreeP P).Obj (FreeM.Path (rest b)))) =
          (fun b => (⟨rest b, FreeM.Path.cons a rest b⟩ :
            (FreeP P).Obj (FreeM.Path (FreeM.liftBind a rest)))) := by
        funext b
        exact congrArg (relabel (FreeM.Path.cons a rest b))
          (map_obj_id (rest b))
      rw [hchildren]
      exact node_paths a rest id

@[simp]
theorem map_id : map (Lens.id P) = Lens.id (FreeP P) := by
  let hA : ∀ s, (map (Lens.id P)).toFunA s =
      (Lens.id (FreeP P)).toFunA s :=
    fun s => congrArg Sigma.fst (map_obj_id s)
  refine Lens.ext _ _ hA ?_
  intro s
  apply eq_of_heq
  have hraw : (map (Lens.id P)).toFunB s ≍
      (Lens.id (FreeP P)).toFunB s :=
    (Sigma.ext_iff.mp (map_obj_id s)).2
  have hcast : (hA s ▸ (Lens.id (FreeP P)).toFunB s) ≍
      (Lens.id (FreeP P)).toFunB s :=
    eqRec_heq_self _ _
  exact hraw.trans hcast.symm

/-- Pointwise container form of composition preservation for `FreeP.map`. -/
theorem map_obj_comp (l₂ : Lens Q R) (l₁ : Lens P Q)
    (s : (FreeP P).A) :
    (⟨(map l₂ ∘ₗ map l₁).toFunA s,
        (map l₂ ∘ₗ map l₁).toFunB s⟩ :
      (FreeP R).Obj (FreeM.Path s)) =
    ⟨(map (l₂ ∘ₗ l₁)).toFunA s,
      (map (l₂ ∘ₗ l₁)).toFunB s⟩ := by
  match s with
  | .pure u =>
      cases u
      refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext path
      cases path
      rfl
  | .liftBind a rest =>
      change
        node (l₂.toFunA (l₁.toFunA a)) (fun d =>
          relabel
            (FreeM.Path.cons a rest
              (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d)))
            (⟨(map l₂ ∘ₗ map l₁).toFunA
                (rest (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d))),
              (map l₂ ∘ₗ map l₁).toFunB
                (rest (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d)))⟩ :
              (FreeP R).Obj
                (FreeM.Path
                  (rest (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d)))))) =
        node (l₂.toFunA (l₁.toFunA a)) (fun d =>
          relabel
            (FreeM.Path.cons a rest
              (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d)))
            (⟨(map (l₂ ∘ₗ l₁)).toFunA
                (rest (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d))),
              (map (l₂ ∘ₗ l₁)).toFunB
                (rest (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d)))⟩ :
              (FreeP R).Obj
                (FreeM.Path
                  (rest (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d))))))
      congr 1
      funext d
      exact congrArg
        (relabel (FreeM.Path.cons a rest
          (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d))))
        (map_obj_comp l₂ l₁
          (rest (l₁.toFunB a (l₂.toFunB (l₁.toFunA a) d))))

/-- Mapping preserves lens composition. This is intentionally not a simp
lemma: `Lens.mapObj_comp` already selects the canonical normal form for
composition acting on polynomial extensions. -/
theorem map_comp (l₂ : Lens Q R) (l₁ : Lens P Q) :
    map l₂ ∘ₗ map l₁ = map (l₂ ∘ₗ l₁) := by
  let hA : ∀ s, (map l₂ ∘ₗ map l₁).toFunA s =
      (map (l₂ ∘ₗ l₁)).toFunA s :=
    fun s => congrArg Sigma.fst (map_obj_comp l₂ l₁ s)
  refine Lens.ext _ _ hA ?_
  intro s
  apply eq_of_heq
  have hraw : (map l₂ ∘ₗ map l₁).toFunB s ≍
      (map (l₂ ∘ₗ l₁)).toFunB s :=
    (Sigma.ext_iff.mp (map_obj_comp l₂ l₁ s)).2
  have hcast : (hA s ▸ (map (l₂ ∘ₗ l₁)).toFunB s) ≍
      (map (l₂ ∘ₗ l₁)).toFunB s :=
    eqRec_heq_self _ _
  exact hraw.trans hcast.symm

/-! ## Substitution-monoid structure -/

/-- The unit of the free substitution monoid: the single unlabelled leaf. -/
def unit : Lens X.{max uA uB, uB} (FreeP P) where
  toFunA _ := .pure PUnit.unit
  toFunB _ _ := PUnit.unit

/-- Multiplication of the free substitution monoid grafts the inner tree at
each path of the outer tree. A direction through the grafted tree splits into
its outer and inner path components. -/
def mult : Lens (FreeP P ◃ FreeP P) (FreeP P) where
  toFunA x := FreeM.append x.1 x.2
  toFunB x path := FreeM.Path.split x.1 x.2 path

@[simp]
theorem unit_toFunA (u : X.{max uA uB, uB}.A) :
    (unit (P := P)).toFunA u = FreeM.pure PUnit.unit :=
  rfl

@[simp]
theorem mult_toFunA (x : (FreeP P ◃ FreeP P).A) :
    (mult (P := P)).toFunA x = FreeM.append x.1 x.2 :=
  rfl

@[simp]
theorem mult_toFunB (x : (FreeP P ◃ FreeP P).A)
    (path : (FreeP P).B ((mult (P := P)).toFunA x)) :
    (mult (P := P)).toFunB x path = FreeM.Path.split x.1 x.2 path :=
  rfl

/-- Decode each inner tree of a two-layer `FreeP` object, leaving the outer
tree labelled by free-monad computations. -/
def nest (x : (FreeP P ◃ FreeP P).Obj α) : (FreeP P).Obj (FreeM P α) :=
  ⟨x.1.1, fun path₁ ↦
    decodeAt (x.1.2 path₁) (fun path₂ ↦ x.2 ⟨path₁, path₂⟩)⟩

/-- Multiplication of labelled free polynomials corresponds under `objEquiv`
to joining the nested decoded free-monad computation. -/
theorem decode_mult (x : (FreeP P ◃ FreeP P).Obj α) :
    decode (Lens.mapObj (mult (P := P)) x) =
      FreeM.bind (decode (nest x)) id := by
  rcases x with ⟨⟨s, middle⟩, label⟩
  induction s with
  | pure u =>
      cases u
      rfl
  | liftBind a rest ih =>
      simp only [Lens.mapObj, mult, nest, decode, decodeAt, FreeM.append,
        FreeM.bind, Function.comp_apply]
      apply congrArg (FreeM.liftBind a)
      funext b
      exact ih b (fun path ↦ middle ⟨b, path⟩)
        (fun pair ↦ label ⟨⟨b, pair.1⟩, pair.2⟩)

theorem mult_unit_left :
    Lens.comp
      (Lens.comp (mult (P := P))
        (Lens.compMap (unit (P := P)) (Lens.id (FreeP P))))
      Lens.Equiv.XComp.invLens = Lens.id (FreeP P) :=
  rfl

/-- Pointwise container form of right unitality for free-tree grafting. -/
theorem mult_unit_right_obj (s : (FreeP P).A) :
    let composite :=
      Lens.comp
        (Lens.comp (mult (P := P))
          (Lens.compMap (Lens.id (FreeP P)) (unit (P := P))))
        Lens.Equiv.compX.invLens
    (⟨composite.toFunA s, composite.toFunB s⟩ :
      (FreeP P).Obj (FreeM.Path s)) = ⟨s, id⟩ := by
  dsimp only
  match s with
  | .pure u =>
      cases u
      refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext path
      cases path
      rfl
  | .liftBind a rest =>
      change
        node a (fun b => relabel (FreeM.Path.cons a rest b)
          (let composite :=
            Lens.comp
              (Lens.comp (mult (P := P))
                (Lens.compMap (Lens.id (FreeP P)) (unit (P := P))))
              Lens.Equiv.compX.invLens
           (⟨composite.toFunA (rest b), composite.toFunB (rest b)⟩ :
             (FreeP P).Obj (FreeM.Path (rest b))))) =
        ⟨.liftBind a rest, id⟩
      have hchildren :
          (fun b => relabel (FreeM.Path.cons a rest b)
            (let composite :=
              Lens.comp
                (Lens.comp (mult (P := P))
                  (Lens.compMap (Lens.id (FreeP P)) (unit (P := P))))
                Lens.Equiv.compX.invLens
             (⟨composite.toFunA (rest b), composite.toFunB (rest b)⟩ :
               (FreeP P).Obj (FreeM.Path (rest b))))) =
          (fun b => (⟨rest b, FreeM.Path.cons a rest b⟩ :
            (FreeP P).Obj (FreeM.Path (FreeM.liftBind a rest)))) := by
        funext b
        exact congrArg (relabel (FreeM.Path.cons a rest b))
          (mult_unit_right_obj (rest b))
      rw [hchildren]
      exact node_paths a rest id

theorem mult_unit_right :
    Lens.comp
      (Lens.comp (mult (P := P))
        (Lens.compMap (Lens.id (FreeP P)) (unit (P := P))))
      Lens.Equiv.compX.invLens = Lens.id (FreeP P) := by
  let composite :=
    Lens.comp
      (Lens.comp (mult (P := P))
        (Lens.compMap (Lens.id (FreeP P)) (unit (P := P))))
      Lens.Equiv.compX.invLens
  let hA : ∀ s, composite.toFunA s = (Lens.id (FreeP P)).toFunA s :=
    fun s => congrArg Sigma.fst (mult_unit_right_obj s)
  refine Lens.ext _ _ hA ?_
  intro s
  apply eq_of_heq
  have hraw : composite.toFunB s ≍ (Lens.id (FreeP P)).toFunB s :=
    (Sigma.ext_iff.mp (mult_unit_right_obj s)).2
  have hcast : (hA s ▸ (Lens.id (FreeP P)).toFunB s) ≍
      (Lens.id (FreeP P)).toFunB s :=
    eqRec_heq_self _ _
  exact hraw.trans hcast.symm

/-- The left-associated composite of free-tree multiplication. -/
def multAssocLeft : Lens ((FreeP P ◃ FreeP P) ◃ FreeP P) (FreeP P) :=
  Lens.comp (mult (P := P))
    (Lens.compMap (mult (P := P)) (Lens.id (FreeP P)))

/-- The right-associated composite of free-tree multiplication, with the
composition associator inserted on the source. -/
def multAssocRight : Lens ((FreeP P ◃ FreeP P) ◃ FreeP P) (FreeP P) :=
  Lens.comp
    (Lens.comp (mult (P := P))
      (Lens.compMap (Lens.id (FreeP P)) (mult (P := P))))
    Lens.Equiv.compAssoc.toLens

/-- Pointwise container form of associativity for free-tree grafting. -/
theorem mult_assoc_obj
    (s : (FreeP P).A)
    (middle : FreeM.Path s → (FreeP P).A)
    (inner : ((path₁ : FreeM.Path s) × FreeM.Path (middle path₁)) →
      (FreeP P).A) :
    let x : ((FreeP P ◃ FreeP P) ◃ FreeP P).A :=
      ⟨⟨s, middle⟩, inner⟩
    (⟨(multAssocLeft (P := P)).toFunA x,
        (multAssocLeft (P := P)).toFunB x⟩ :
      (FreeP P).Obj (((FreeP P ◃ FreeP P) ◃ FreeP P).B x)) =
    ⟨(multAssocRight (P := P)).toFunA x,
      (multAssocRight (P := P)).toFunB x⟩ := by
  dsimp only
  match s with
  | .pure u =>
      cases u
      rfl
  | .liftBind a rest =>
      let child (b : P.B a) : ((FreeP P ◃ FreeP P) ◃ FreeP P).A :=
        ⟨⟨rest b, fun path => middle (FreeM.Path.cons a rest b path)⟩,
          fun pair => inner
            ⟨FreeM.Path.cons a rest b pair.1, pair.2⟩⟩
      let embed (b : P.B a) :
          ((FreeP P ◃ FreeP P) ◃ FreeP P).B (child b) →
          ((FreeP P ◃ FreeP P) ◃ FreeP P).B
            ⟨⟨FreeM.liftBind a rest, middle⟩, inner⟩ :=
        fun direction =>
          ⟨⟨FreeM.Path.cons a rest b direction.1.1,
            direction.1.2⟩, direction.2⟩
      change
        node a (fun b => relabel (embed b)
          (⟨(multAssocLeft (P := P)).toFunA (child b),
            (multAssocLeft (P := P)).toFunB (child b)⟩ :
            (FreeP P).Obj
              (((FreeP P ◃ FreeP P) ◃ FreeP P).B (child b)))) =
        node a (fun b => relabel (embed b)
          (⟨(multAssocRight (P := P)).toFunA (child b),
            (multAssocRight (P := P)).toFunB (child b)⟩ :
            (FreeP P).Obj
              (((FreeP P ◃ FreeP P) ◃ FreeP P).B (child b))))
      congr 1
      funext b
      exact congrArg (relabel (embed b))
        (mult_assoc_obj (rest b)
          (fun path => middle (FreeM.Path.cons a rest b path))
          (fun pair => inner
            ⟨FreeM.Path.cons a rest b pair.1, pair.2⟩))

theorem mult_assoc : multAssocLeft (P := P) = multAssocRight (P := P) := by
  let hA : ∀ x, (multAssocLeft (P := P)).toFunA x =
      (multAssocRight (P := P)).toFunA x := fun x => by
    rcases x with ⟨⟨s, middle⟩, inner⟩
    exact congrArg Sigma.fst (mult_assoc_obj s middle inner)
  refine Lens.ext _ _ hA ?_
  intro x
  rcases x with ⟨⟨s, middle⟩, inner⟩
  apply eq_of_heq
  have hraw : (multAssocLeft (P := P)).toFunB ⟨⟨s, middle⟩, inner⟩ ≍
      (multAssocRight (P := P)).toFunB ⟨⟨s, middle⟩, inner⟩ :=
    (Sigma.ext_iff.mp (mult_assoc_obj s middle inner)).2
  have hcast :
      (hA ⟨⟨s, middle⟩, inner⟩ ▸
        (multAssocRight (P := P)).toFunB ⟨⟨s, middle⟩, inner⟩) ≍
      (multAssocRight (P := P)).toFunB ⟨⟨s, middle⟩, inner⟩ :=
    eqRec_heq_self _ _
  exact hraw.trans hcast.symm

/-- The free substitution monoid generated by `P`. Its carrier is the
polynomial of well-founded `P`-trees, its unit is the one-leaf tree, and its
multiplication is path-indexed grafting. -/
def substMonoid (P : PFunctor.{uA, uB}) : SubstMonoid.{max uA uB, uB} where
  carrier := FreeP P
  unit := unit
  mult := mult
  unit_left := mult_unit_left
  unit_right := mult_unit_right
  assoc := mult_assoc

@[simp]
theorem substMonoid_carrier (P : PFunctor.{uA, uB}) :
    (substMonoid P).carrier = FreeP P :=
  rfl

@[simp]
theorem substMonoid_unit (P : PFunctor.{uA, uB}) :
    (substMonoid P).unit = unit :=
  rfl

@[simp]
theorem substMonoid_mult (P : PFunctor.{uA, uB}) :
    (substMonoid P).mult = mult :=
  rfl

end FreeP

end PFunctor
