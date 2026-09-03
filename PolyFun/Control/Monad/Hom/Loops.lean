/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Hom
public import ToCslib.Control.Monad.HomTransport

/-!
# Monad Morphisms Commute with Loops

The bundled corollaries of `ToCslib.Control.Monad.HomTransport` for `MonadHom`: a monad
morphism commutes with `forIn'`, `forIn`, `forM`, `foldlM`, and `mapM` over lists, and with
`forIn` over any container whose loop is the loop over `ForIn.toList`. Each is an equation
whose left-hand side is the morphism applied to the loop, so `simp` pushes morphisms into loop
bodies the way `mmap_bind` pushes them into binds, and `grind` can index the list forms.
-/

@[expose] public section

universe u v w x y

namespace MonadHom

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n] (F : m →ᵐ n)

@[simp, grind =]
theorem mmap_forIn' {ι : Type x} {β : Type u} (l : List ι) (init : β)
    (f : (a : ι) → a ∈ l → β → m (ForInStep β)) :
    F (forIn' l init f) = forIn' l init fun a h b => F (f a h b) :=
  Cslib.map_listForIn' (fun x => F x) F.mmap_pure F.mmap_bind l init f

/-- Not a `simp` lemma: `simp` already derives it from `mmap_forIn'` through core's
`List.forIn'_eq_forIn`. -/
@[grind =]
theorem mmap_forIn {ι : Type x} {β : Type u} (l : List ι) (init : β)
    (f : ι → β → m (ForInStep β)) :
    F (forIn l init f) = forIn l init fun a b => F (f a b) :=
  Cslib.map_listForIn (fun x => F x) F.mmap_pure F.mmap_bind l init f

/-- Stated with the class method `forM`, the simp normal form of `List.forM`. -/
@[simp, grind =]
theorem mmap_forM {ι : Type x} (l : List ι) (f : ι → m PUnit) :
    F (forM l f) = forM l fun a => F (f a) := by
  simpa only [List.forM_eq_forM, Function.comp_def] using
    Cslib.map_listForM (fun x => F x) F.mmap_pure F.mmap_bind l f

@[simp, grind =]
theorem mmap_foldlM {σ : Type u} {ι : Type x} (f : σ → ι → m σ) (init : σ) (l : List ι) :
    F (l.foldlM f init) = l.foldlM (fun s a => F (f s a)) init :=
  Cslib.map_listFoldlM (fun x => F x) F.mmap_pure F.mmap_bind f init l

@[simp, grind =]
theorem mmap_mapM [LawfulMonad m] [LawfulMonad n] {ι : Type x} {β : Type u} (f : ι → m β)
    (l : List ι) :
    F (l.mapM f) = l.mapM fun a => F (f a) :=
  Cslib.map_listMapM (fun x => F x) F.mmap_pure F.mmap_bind f l

@[simp]
theorem mmap_forIn_of_pureForIn {ρ : Type y} {ι : Type x} {β : Type u}
    [ForIn m ρ ι] [ForIn n ρ ι] [ForIn Id ρ ι]
    [Std.Internal.PureForIn m ρ ι] [Std.Internal.PureForIn n ρ ι]
    (xs : ρ) (init : β) (f : ι → β → m (ForInStep β)) :
    F (forIn xs init f) = forIn xs init fun a b => F (f a b) :=
  Cslib.map_forIn_of_pureForIn (fun x => F x) F.mmap_pure F.mmap_bind xs init f

end MonadHom
