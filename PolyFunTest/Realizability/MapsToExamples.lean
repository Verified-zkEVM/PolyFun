/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.Realizability
public import PolyFun.Realizability.Instances
public import Mathlib.Data.Set.Function

/-!
# A non-vacuous step class: set-preserving maps

`StepClass.unconstrained` admits every function, so the canary instance of
`OpenProcess.IsRealizabilityClosed` cannot show that the framework restricts
anything.  This file builds the step class whose representations are sets and
whose admissible maps are exactly the set-preserving functions
(`Set.MapsTo`), checks by a negative example that admissibility genuinely
fails for some maps, and instantiates the UC closure contract at the
permissive all-sets boundary family.

The class is honest but its chosen boundary family here is the permissive
one; a restrictive boundary family would constrain which processes are
realizable, exactly as a complexity class would.
-/

@[expose] public section

universe u v w

namespace PFunctor.StepClass.MapsToExamples

open PFunctor

/-- The step class of set-preserving maps: a representation of `A` is a
subset of `A`, and `f : A → B` is admissible when it maps the chosen subset
into the chosen subset. -/
def mapsTo : StepClass.{u, u} where
  Str A := Set A
  Hom a b f := Set.MapsTo f a b
  id_mem a := Set.mapsTo_id a
  comp_mem hf hg := hg.comp hf

instance : (mapsTo.{u}).HasProd where
  prod {A B} a b := Set.prod a b
  fst_mem a b := fun _ hx => hx.1
  snd_mem a b := fun _ hx => hx.2
  pair_mem hf hg := fun x hx => ⟨hf hx, hg hx⟩

instance : (mapsTo.{u}).HasSum where
  sum {A B} a b :=
    Set.union (Set.image Sum.inl a) (Set.image Sum.inr b)
  inl_mem a b := fun x hx => Or.inl ⟨x, hx, rfl⟩
  inr_mem a b := fun x hx => Or.inr ⟨x, hx, rfl⟩
  elim_mem {A B D} {a b d} {f g} hf hg := by
    rintro x (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact hf hy
    · exact hg hy

instance : (mapsTo.{u}).HasOption where
  option {A} a := Set.insert none (Set.image Option.some a)
  omap_mem {A B} {a b} {f} hf := by
    rintro x (rfl | ⟨y, hy, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨f y, hf hy, rfl⟩
  none_mem a b := fun _ _ => Or.inl rfl
  obindCtx_mem {A B E} {a b e} {k} hk := by
    rintro ⟨o, v⟩ ⟨(rfl | ⟨y, hy, rfl⟩), hv⟩
    · exact Or.inl rfl
    · exact hk ⟨hy, hv⟩
  some_mem a := fun x hx => Or.inr ⟨x, hx, rfl⟩

instance : (mapsTo.{u}).IsDistributive where
  distrib_mem {A B I} a b i := by
    rintro ⟨x, v⟩ ⟨(⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩), hv⟩
    · exact Or.inl ⟨(y, v), ⟨hy, hv⟩, rfl⟩
    · exact Or.inr ⟨(y, v), ⟨hy, hv⟩, rfl⟩

/-- The class genuinely restricts: the successor does not preserve `{0}`. -/
example : ¬ (mapsTo.{0}).Hom ({0} : Set ℕ) ({0} : Set ℕ) (· + 1) := by
  intro h
  simpa using h (Set.mem_singleton 0)

/-- Constant maps into a nonempty representation are admissible, so the
class is not empty either. -/
example : (mapsTo.{0}).Hom (Set.univ : Set ℕ) ({0} : Set ℕ) (fun _ => 0) :=
  fun _ _ => rfl

end PFunctor.StepClass.MapsToExamples
