/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Stateful.Combinators

/-!
# Sequential and parallel composition of stateful packages

A stateful handler `Stateful (FreeM M) S E` is a *package*: it exports the interface `E`,
keeps private state `S`, and answers each request with a free program over the imported
interface `M`. This module composes packages and proves the algebraic laws used by
state-separating proofs (Haselwarter et al., *SSProve*, `HARM+23` in REFERENCES.md).

* `link outer inner` composes sequentially. Each request of `outer` produces a program over
  `M`, which `inner : Stateful m T M` then runs in any monad `m`. The combined state is
  `S × T`, with the outer state first. For stateless handlers this is `Handler.comp` in
  diagrammatic order.
* `sumMap f g` composes in parallel over disjoint interfaces. It answers `E₁ + E₂` by
  routing each request to `f` or `g`, relabelling the imports into `I₁ + I₂` with
  `mapLens`, on a product state.
* `stateCongr e` transports a handler along an equivalence of states. Composition laws hold
  up to the canonical reassociation of product states.

The laws are:
* associativity of `link`, up to `Equiv.prodAssoc` (`link_assoc`);
* the identity package on both sides, up to the unit equivalences (`link_lift_id`,
  `lift_id_link`);
* interchange of `link` with parallel composition, up to `Equiv.prodProdProdComm`. This
  holds both into a sum of inner handlers in any monad (`sumMap_link_sum`) and into another
  parallel package (`sumMap_link_sumMap`).
-/

@[expose] public section

universe u v uE uE₁ uE₂ uM uM₁ uM₂ uI uI₁ uI₂ uJ

namespace PFunctor
namespace Handler
namespace Stateful

variable {m : Type u → Type v} {S T U S₁ S₂ T₁ T₂ : Type u}
variable {E : PFunctor.{uE, u}} {M : PFunctor.{uM, u}} {I : PFunctor.{uI, u}}
variable {J : PFunctor.{uJ, u}}
variable {E₁ : PFunctor.{uE₁, u}} {E₂ : PFunctor.{uE₂, u}}
variable {M₁ : PFunctor.{uM₁, u}} {M₂ : PFunctor.{uM₂, u}}
variable {I₁ : PFunctor.{uI₁, u}} {I₂ : PFunctor.{uI₂, u}}

/-! ### Transport along state equivalences -/

/-- Transport a stateful handler along an equivalence of states. -/
def stateCongr [Functor m] (e : S ≃ T) (h : Stateful m S E) : Stateful m T E :=
  fun a => StateT.mk fun t => Prod.map _root_.id e <$> (h a).run (e.symm t)

@[simp] theorem stateCongr_apply_run [Functor m] (e : S ≃ T) (h : Stateful m S E) (a : E.A)
    (t : T) : (stateCongr e h a).run t = Prod.map _root_.id e <$> (h a).run (e.symm t) := rfl

/-- Running a program whose results are mapped runs the program and maps the result. -/
theorem run_map [Monad m] [LawfulMonad m] (h : Stateful m S E) {α β : Type u} (f : α → β)
    (x : FreeM E α) (s : S) :
    h.run (f <$> x) s = (fun r : α × S => (f r.1, r.2)) <$> h.run x s := by
  simp [run, StateT.run_map]

/-- Running a program through a lifted stateless handler leaves the state unchanged. -/
private theorem run_lift_handler [Monad m] [LawfulMonad m] (h : Handler m E) {α : Type u} :
    ∀ (x : FreeM E α) (s : S), (lift h : Stateful m S E).run x s = (·, s) <$> x.liftM h
  | .pure a, s => by simp
  | .liftBind a k, s => by
    rw [run_liftBind]
    change _ = (·, s) <$> (h a >>= fun d => (k d).liftM h)
    simp only [lift, StateT.run_lift, bind_assoc, pure_bind, map_bind]
    exact bind_congr fun d => run_lift_handler h (k d) s

/-! ### Sequential composition -/

/-- Sequential composition of stateful packages. `outer` exports `E` and imports `M`, and
`inner` implements `M` in the monad `m`. The outer state comes first. -/
def link [Monad m] (outer : Stateful (FreeM M) S E) (inner : Stateful m T M) :
    Stateful m (S × T) E :=
  flatten (mapBase inner outer)

/-- Answering a request through a linked package runs the outer step from the outer state and
then runs the resulting program through the inner handler from the inner state. -/
@[simp] theorem link_apply_run [Monad m] (outer : Stateful (FreeM M) S E)
    (inner : Stateful m T M) (a : E.A) (s : S) (t : T) :
    (outer.link inner a).run (s, t) =
      (fun r : (E.B a × S) × T => (r.1.1, (r.1.2, r.2))) <$> inner.run ((outer a).run s) t :=
  rfl

/-- Running a program through a linked package runs it through the outer package and runs the
resulting program through the inner handler. -/
theorem run_link [Monad m] [LawfulMonad m] (outer : Stateful (FreeM M) S E)
    (inner : Stateful m T M) {α : Type u} (x : FreeM E α) (s : S) (t : T) :
    (outer.link inner).run x (s, t) =
      (fun r : (α × S) × T => (r.1.1, (r.1.2, r.2))) <$> inner.run (outer.run x s) t := by
  rw [link, run_flatten]
  simp only
  rw [← run_mapBase]
  rfl

/-- Linking is associative, up to the reassociation of the product state. -/
theorem link_assoc [Monad m] [LawfulMonad m] (a : Stateful (FreeM M) S E)
    (b : Stateful (FreeM I) T M) (c : Stateful m U I) :
    (a.link b).link c = stateCongr (_root_.Equiv.prodAssoc S T U).symm (a.link (b.link c)) := by
  funext q
  refine StateT.ext fun ⟨⟨s, t⟩, u⟩ => ?_
  simp only [link_apply_run, stateCongr_apply_run, _root_.Equiv.symm_symm,
    _root_.Equiv.prodAssoc_apply, run_link, run_map, Functor.map_map]
  rfl

/-- Linking with the identity package on the imports changes nothing but the state, which
gains a trivial component. -/
theorem link_lift_id (a : Stateful (FreeM M) S E) :
    a.link (lift (S := PUnit.{u + 1}) (Handler.id M)) =
      stateCongr (_root_.Equiv.prodPUnit S).symm a := by
  funext q
  refine StateT.ext fun ⟨s, ⟨⟩⟩ => ?_
  have hid : ((a q).run s).liftM (Handler.id M) = (a q).run s := FreeM.liftM_lift_eq_self _
  simp only [link_apply_run, stateCongr_apply_run, run_lift_handler, hid, Functor.map_map,
    _root_.Equiv.symm_symm, _root_.Equiv.prodPUnit_apply]
  rfl

/-- Linking the identity package on the exports in front changes nothing but the state, which
gains a trivial component. -/
theorem lift_id_link [Monad m] [LawfulMonad m] (a : Stateful m S E) :
    (lift (S := PUnit.{u + 1}) (Handler.id E)).link a =
      stateCongr (_root_.Equiv.punitProd S).symm a := by
  funext q
  refine StateT.ext fun ⟨⟨⟩, s⟩ => ?_
  change (fun r : (E.B q × PUnit) × S => (r.1.1, (r.1.2, r.2))) <$>
      a.run (FreeM.lift q >>= fun d => pure (d, PUnit.unit)) s = _
  rw [run_bind, run_lift]
  simp only [run_pure, stateCongr_apply_run, _root_.Equiv.symm_symm,
    _root_.Equiv.punitProd_apply, bind_pure_comp, Functor.map_map]
  rfl

/-! ### Relabelling imports -/

/-- Relabel the imports of a package along a lens: each answer program is transported by
`FreeM.mapLens`. -/
def mapLens (l : Lens I J) (h : Stateful (FreeM I) S E) : Stateful (FreeM J) S E :=
  fun a => StateT.mk fun s => ((h a).run s).mapLens l

@[simp] theorem mapLens_apply_run (l : Lens I J) (h : Stateful (FreeM I) S E) (a : E.A)
    (s : S) : (h.mapLens l a).run s = ((h a).run s).mapLens l := rfl

/-- Running a program through a relabelled package relabels the resulting program. -/
theorem run_mapLens (l : Lens I J) (h : Stateful (FreeM I) S E) {α : Type u} :
    ∀ (x : FreeM E α) (s : S), (h.mapLens l).run x s = (h.run x s).mapLens l
  | .pure _, _ => rfl
  | .liftBind a k, s => by
    rw [run_liftBind, run_liftBind, FreeM.mapLens_bind']
    exact bind_congr fun r => run_mapLens l h (k r.1) r.2

/-- Relabelling the imports of a linked package relabels the imports of its inner package. -/
theorem mapLens_link (l : Lens I J) (outer : Stateful (FreeM M) S E)
    (inner : Stateful (FreeM I) T M) :
    (outer.link inner).mapLens l = outer.link (inner.mapLens l) := by
  funext q
  refine StateT.ext fun ⟨s, t⟩ => ?_
  simp only [mapLens_apply_run, link_apply_run, run_mapLens, FreeM.mapLens_map]

/-! ### Parallel composition -/

/-- Parallel composition of packages over disjoint interfaces. A request of `E₁ + E₂` is
answered by `f` or `g` on its component of the product state, with the answer program
relabelled into the sum of the imports. -/
def sumMap (f : Stateful (FreeM I₁) S₁ E₁) (g : Stateful (FreeM I₂) S₂ E₂) :
    Stateful (FreeM (I₁ + I₂ : PFunctor.{max uI₁ uI₂, u})) (S₁ × S₂)
      (E₁ + E₂ : PFunctor.{max uE₁ uE₂, u}) :=
  sum (f.mapLens Lens.inl) (g.mapLens Lens.inr)

@[simp] theorem sumMap_inl_run (f : Stateful (FreeM I₁) S₁ E₁)
    (g : Stateful (FreeM I₂) S₂ E₂) (a : E₁.A) (st : S₁ × S₂) :
    (sumMap f g (.inl a)).run st =
      Prod.map _root_.id (·, st.2) <$> ((f a).run st.1).mapLens Lens.inl := rfl

@[simp] theorem sumMap_inr_run (f : Stateful (FreeM I₁) S₁ E₁)
    (g : Stateful (FreeM I₂) S₂ E₂) (b : E₂.A) (st : S₁ × S₂) :
    (sumMap f g (.inr b)).run st =
      Prod.map _root_.id (st.1, ·) <$> ((g b).run st.2).mapLens Lens.inr := rfl

/-- Running a program relabelled into the left summand through a sum handler runs the left
handler on the first state component and keeps the second. -/
theorem run_sum_mapLens_inl [Monad m] [LawfulMonad m] (f : Stateful m T₁ M₁)
    (g : Stateful m T₂ M₂) {α : Type u} (x : FreeM M₁ α) (t₁ : T₁) (t₂ : T₂) :
    (sum f g).run (x.mapLens Lens.inl) (t₁, t₂) = Prod.map _root_.id (·, t₂) <$> f.run x t₁ := by
  rw [run, FreeM.liftM_mapLens]
  refine (run_map_eq_of_apply_map_eq f _ (·, t₂) (fun a s => ?_) x t₁).symm
  rw [StateT.run_map]
  change _ = (fun p => (p.1, p.2)) <$> (Prod.map _root_.id (·, t₂) <$> (f a).run s)
  simp

/-- Running a program relabelled into the right summand through a sum handler runs the right
handler on the second state component and keeps the first. -/
theorem run_sum_mapLens_inr [Monad m] [LawfulMonad m] (f : Stateful m T₁ M₁)
    (g : Stateful m T₂ M₂) {α : Type u} (x : FreeM M₂ α) (t₁ : T₁) (t₂ : T₂) :
    (sum f g).run (x.mapLens Lens.inr) (t₁, t₂) = Prod.map _root_.id (t₁, ·) <$> g.run x t₂ := by
  rw [run, FreeM.liftM_mapLens]
  refine (run_map_eq_of_apply_map_eq g _ (t₁, ·) (fun a s => ?_) x t₂).symm
  rw [StateT.run_map]
  change _ = (fun p => (p.1, p.2)) <$> (Prod.map _root_.id (t₁, ·) <$> (g a).run s)
  simp

/-- **Interchange.** Linking a parallel package into a sum of inner handlers is the sum of the
two linked packages, up to the exchange of the middle state components. -/
theorem sumMap_link_sum [Monad m] [LawfulMonad m]
    (o₁ : Stateful (FreeM M₁) S₁ E₁) (o₂ : Stateful (FreeM M₂) S₂ E₂)
    (i₁ : Stateful m T₁ M₁) (i₂ : Stateful m T₂ M₂) :
    (sumMap o₁ o₂).link (sum i₁ i₂) =
      stateCongr (_root_.Equiv.prodProdProdComm S₁ T₁ S₂ T₂) (sum (o₁.link i₁) (o₂.link i₂)) := by
  funext q
  rcases q with q | q <;> refine StateT.ext fun ⟨⟨s₁, s₂⟩, ⟨t₁, t₂⟩⟩ => ?_
  · simp only [link_apply_run, sumMap_inl_run, sum_inl_run, stateCongr_apply_run, run_map,
      run_sum_mapLens_inl, Functor.map_map, _root_.Equiv.prodProdProdComm_symm,
      _root_.Equiv.prodProdProdComm_apply]
    rfl
  · simp only [link_apply_run, sumMap_inr_run, sum_inr_run, stateCongr_apply_run, run_map,
      run_sum_mapLens_inr, Functor.map_map, _root_.Equiv.prodProdProdComm_symm,
      _root_.Equiv.prodProdProdComm_apply]
    rfl

/-- **Interchange for packages.** Linking two parallel packages is the parallel composite of
the two linked packages, up to the exchange of the middle state components. -/
theorem sumMap_link_sumMap
    (o₁ : Stateful (FreeM M₁) S₁ E₁) (o₂ : Stateful (FreeM M₂) S₂ E₂)
    (i₁ : Stateful (FreeM I₁) T₁ M₁) (i₂ : Stateful (FreeM I₂) T₂ M₂) :
    (sumMap o₁ o₂).link (sumMap i₁ i₂) =
      stateCongr (_root_.Equiv.prodProdProdComm S₁ T₁ S₂ T₂)
        (sumMap (o₁.link i₁) (o₂.link i₂)) := by
  rw [show sumMap i₁ i₂ = sum (i₁.mapLens Lens.inl) (i₂.mapLens Lens.inr) from rfl,
    sumMap_link_sum, ← mapLens_link, ← mapLens_link]
  rfl

end Stateful
end Handler
end PFunctor
