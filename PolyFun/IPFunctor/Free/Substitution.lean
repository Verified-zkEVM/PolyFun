/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.IPFunctor.Free.Lens

/-!
# Substituting indexed commands by free trees

`CommandSubstitution P Q` assigns a tree over `Q` to each shape of `P`. Each leaf
returns a response together with its source-state equality. `IFreeM.substitute`
extends this assignment using `IFreeM.fold` and `IFreeM.bind`, keeping the original
leaves and attaching the translated continuation at each returned response.
-/

public section

universe uI uA uB uC uD uX uY

namespace IPFunctor

variable {I : Type uI} {P : Endo.{uI, uA, uB} I} {Q : Endo.{uI, uC, uD} I}

/-- A tree for each source shape, returning a response at exactly its source state. -/
abbrev CommandSubstitution (P : Endo.{uI, uA, uB} I) (Q : Endo.{uI, uC, uD} I) :=
  ∀ s (a : P.A s), IFreeM Q (fun t => {b : P.B s a // P.src s a b = t}) s

/-- The single-node substitution associated to an indexed lens. -/
@[expose] def Lens.toSubstitution (l : Lens P Q) : CommandSubstitution P Q :=
  fun s a => .liftBind (l.toFunA s a) (fun b => .pure ⟨l.toFunB s a b, l.src_eq s a b⟩)

namespace IFreeM

variable {X : I → Type uX} {Y : I → Type uY}

/-- Replace each command by its assigned tree and bind its responses to the translated
continuations. This is the algebra fold into the target free trees. -/
@[expose] def substitute (h : CommandSubstitution P Q) {s : I} (x : IFreeM P X s) :
    IFreeM Q X s :=
  x.fold (fun _ value => .pure value)
    (fun s a next => (h s a).bind (fun _ answer => answer.2 ▸ next answer.1))

@[simp] theorem substitute_pure (h : CommandSubstitution P Q) {s : I} (x : X s) :
    (IFreeM.pure (P := P) x).substitute h = .pure x := rfl

@[simp] theorem substitute_liftBind (h : CommandSubstitution P Q) {s : I} (a : P.A s)
    (next : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.liftBind a next).substitute h =
      (h s a).bind (fun _ answer => answer.2 ▸ (next answer.1).substitute h) := rfl

/-- Command substitution preserves sequencing, even across different leaf universes. -/
theorem substitute_bind (h : CommandSubstitution P Q) {s : I} (x : IFreeM P X s)
    (g : ∀ t, X t → IFreeM P Y t) :
    (x.bind g).substitute h = (x.substitute h).bind (fun t y => (g t y).substitute h) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => simp only [pure_bind, substitute_pure]
  | liftBind s a next ih =>
      simp only [bind_liftBind, substitute_liftBind, bind_assoc]
      congr 1
      funext t ⟨b, e⟩
      cases e
      exact ih b

/-- Substituting the single-node trees of a lens is transport along that lens. -/
@[simp] theorem substitute_toSubstitution (l : Lens P Q) {s : I} (x : IFreeM P X s) :
    x.substitute l.toSubstitution = x.mapLens l := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind s a next ih =>
      simp only [substitute_liftBind, Lens.toSubstitution, bind_liftBind, pure_bind,
        mapLens_liftBind, ih]

end IFreeM
end IPFunctor
