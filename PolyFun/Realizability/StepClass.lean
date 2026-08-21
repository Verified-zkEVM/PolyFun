/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Basic

/-!
# Classes of admissible functions

A `PFunctor.StepClass` is a class of allowed data representations and functions
between them — a wide subcategory of `Type u`, presented pointwise by

* `Str A`, the structure a type must carry to be representable (a bit encoding,
  a finiteness witness, a `Primcodable` instance, …), and
* `Hom a b f`, the proposition that `f : A → B` is admissible between chosen
  representations,

closed under identities and composition.

`Str` is *data* rather than a proposition because a resource bound only makes
sense relative to a chosen representation: "`f` runs in polynomial time" is a
statement about encoded inputs, not about the bare function. `Hom` is a
proposition because the realizability layer only ever asks *whether* a step map
is admissible; a cost-bearing refinement, in which witnesses carry running-time
and description-size measures, would replace it by a `Type`-valued field.

The mixin classes `StepClass.HasProd` and `StepClass.HasSum` record that a class
represents binary products and sums with admissible projections, injections,
pairing, and case analysis. They are kept separate from `StepClass` so that each
downstream definition requires exactly the structure it consumes.

`StepClass.Refines C D` translates `C`-representations into `D`-representations
compatibly with admissibility, so a statement proved for a small class
specializes to every larger one.

This file is deliberately free of polynomial-functor content beyond its
namespace: the interface between a step class and the machine layer lives in
`PolyFun.Realizability.Basic`.

Taking the resource bound as a predicate on the implementation, rather than as a
measure on runs, follows Petcher and Morrisett's Foundational Cryptography
Framework (2015), where security definitions are parameterized by an
*admissibility predicate* naming the class of allowed adversaries; the
`admissible` / `_mem` vocabulary here is theirs. See `REFERENCES.md`.
-/

@[expose] public section

universe u v v₂ v₃

namespace PFunctor

set_option linter.checkUnivs false in
/-- A class of admissible data representations and functions between them: a wide
subcategory of `Type u` presented by a structure on objects and a predicate on
morphisms.

`Str A` is the representation structure carried by an admissible type, and
`Hom a b f` says that `f` is admissible from representation `a` to
representation `b`. The two closure fields make the admissible functions a
category containing every identity. -/
-- The representation universe `v` is independent of the represented universe `u`:
-- a `Type`-valued encoding structure must be usable on types in any universe.
structure StepClass where
  /-- The representation structure an admissible type must carry. -/
  Str : Type u → Type v
  /-- Admissibility of a function between represented types. -/
  Hom : {A B : Type u} → Str A → Str B → (A → B) → Prop
  /-- Identities are admissible. -/
  id_mem : ∀ {A : Type u} (a : Str A), Hom a a id
  /-- Admissible functions compose. -/
  comp_mem : ∀ {A B D : Type u} {a : Str A} {b : Str B} {d : Str D}
    {f : A → B} {g : B → D}, Hom a b f → Hom b d g → Hom a d (g ∘ f)

namespace StepClass

variable {C : StepClass.{u, v}}

/-- Admissibility depends on a function only through its values: a class
constrains functions, not their syntactic presentation.

This is the workhorse of the realizability closure theory, where a step map of a
composite machine is almost never *syntactically* the admissible combination one
builds by hand. -/
theorem Hom.congr {A B : Type u} {a : C.Str A} {b : C.Str B} {f g : A → B}
    (h : C.Hom a b f) (hfg : ∀ x, f x = g x) : C.Hom a b g := by
  rwa [← funext hfg]

/-! ## Products -/

/-- A step class with admissible binary products.

The realizability layer requires this of every class it uses: the flattened
transition map of a machine is a function out of the product of the state with
the interface's index space. -/
class HasProd (C : StepClass.{u, v}) where
  /-- The representation of a binary product. -/
  prod : {A B : Type u} → C.Str A → C.Str B → C.Str (A × B)
  /-- The first projection is admissible. -/
  fst_mem : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B), C.Hom (prod a b) a Prod.fst
  /-- The second projection is admissible. -/
  snd_mem : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B), C.Hom (prod a b) b Prod.snd
  /-- Admissible functions out of a common source pair. -/
  pair_mem : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : A → D}, C.Hom a b f → C.Hom a d g →
      C.Hom a (prod b d) fun x => (f x, g x)

/-- Admissible functions act on products componentwise. -/
theorem HasProd.map_mem [P : C.HasProd] {A B A' B' : Type u} {a : C.Str A}
    {b : C.Str B} {a' : C.Str A'} {b' : C.Str B'} {f : A → A'} {g : B → B'}
    (hf : C.Hom a a' f) (hg : C.Hom b b' g) :
    C.Hom (P.prod a b) (P.prod a' b') (Prod.map f g) := by
  refine (P.pair_mem (C.comp_mem (P.fst_mem a b) hf)
    (C.comp_mem (P.snd_mem a b) hg)).congr ?_
  intro x
  cases x
  rfl

/-- Pairing an admissible function with a fixed second component. -/
theorem HasProd.pairRight_mem [P : C.HasProd] {A B D : Type u} {a : C.Str A}
    {b : C.Str B} {d : C.Str D} {f : A → B} (hf : C.Hom a b f) :
    C.Hom (P.prod a d) (P.prod b d) fun x => (f x.1, x.2) :=
  P.pair_mem (C.comp_mem (P.fst_mem a d) hf) (P.snd_mem a d)

/-- Pairing an admissible function with a fixed first component. -/
theorem HasProd.pairLeft_mem [P : C.HasProd] {A B D : Type u} {a : C.Str A}
    {b : C.Str B} {d : C.Str D} {f : A → B} (hf : C.Hom a b f) :
    C.Hom (P.prod d a) (P.prod d b) fun x => (x.1, f x.2) :=
  P.pair_mem (P.fst_mem d a) (C.comp_mem (P.snd_mem d a) hf)

/-- Duplicating a value is admissible. This is what lets a closure proof retain
an input while dispatching on some function of it. -/
theorem HasProd.diag_mem [P : C.HasProd] {A : Type u} (a : C.Str A) :
    C.Hom a (P.prod a a) fun x => (x, x) :=
  P.pair_mem (C.id_mem a) (C.id_mem a)

/-- Retaining an input alongside an admissible readout of it. -/
theorem HasProd.withInput_mem [P : C.HasProd] {A B : Type u} {a : C.Str A}
    {b : C.Str B} {f : A → B} (hf : C.Hom a b f) :
    C.Hom a (P.prod b a) fun x => (f x, x) :=
  P.pair_mem hf (C.id_mem a)

/-- Swapping the components of a product is admissible. -/
theorem HasProd.swap_mem [P : C.HasProd] {A B : Type u} (a : C.Str A)
    (b : C.Str B) : C.Hom (P.prod a b) (P.prod b a) Prod.swap := by
  refine (P.pair_mem (P.snd_mem a b) (P.fst_mem a b)).congr ?_
  intro x
  cases x
  rfl

/-- Reassociating a product is admissible. -/
theorem HasProd.assoc_mem [P : C.HasProd] {A B D : Type u} (a : C.Str A)
    (b : C.Str B) (d : C.Str D) :
    C.Hom (P.prod (P.prod a b) d) (P.prod a (P.prod b d))
      fun x => (x.1.1, (x.1.2, x.2)) :=
  P.pair_mem (C.comp_mem (P.fst_mem (P.prod a b) d) (P.fst_mem a b))
    (P.pair_mem (C.comp_mem (P.fst_mem (P.prod a b) d) (P.snd_mem a b))
      (P.snd_mem (P.prod a b) d))

/-! ## Sums -/

/-- A step class with admissible binary sums.

The realizability layer requires this of every class it uses: a machine's
one-step readout lands in `β ⊕ p.A`, a returned value or an exposed query
position. -/
class HasSum (C : StepClass.{u, v}) where
  /-- The representation of a binary sum. -/
  sum : {A B : Type u} → C.Str A → C.Str B → C.Str (A ⊕ B)
  /-- The left injection is admissible. -/
  inl_mem : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B), C.Hom a (sum a b) Sum.inl
  /-- The right injection is admissible. -/
  inr_mem : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B), C.Hom b (sum a b) Sum.inr
  /-- Case analysis on admissible branches is admissible. -/
  elim_mem : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → D} {g : B → D}, C.Hom a d f → C.Hom b d g →
      C.Hom (sum a b) d (Sum.elim f g)

/-- Admissible functions act on sums summandwise. -/
theorem HasSum.map_mem [S : C.HasSum] {A B A' B' : Type u} {a : C.Str A}
    {b : C.Str B} {a' : C.Str A'} {b' : C.Str B'} {f : A → A'} {g : B → B'}
    (hf : C.Hom a a' f) (hg : C.Hom b b' g) :
    C.Hom (S.sum a b) (S.sum a' b') (Sum.map f g) := by
  refine (S.elim_mem (C.comp_mem hf (S.inl_mem a' b'))
    (C.comp_mem hg (S.inr_mem a' b'))).congr ?_
  intro x
  cases x <;> rfl

/-! ## Optional values -/

/-- A step class with admissible optional values.

The realizability layer requires this of every class it uses: a machine's
flattened transition is *partial*, and `none` records that an answer is not one
the machine is waiting for. Partiality is what makes the flattening
compositional — see `PolyFun.Realizability.Machine`.

Up to the equivalence `Option A ≃ A ⊕ PUnit` this is `HasSum` together with a
terminal representation, but it is taken as primitive: factoring it would force
a terminal representation on every instance, and nothing else needs one. For the
same reason `omap_mem` and `obindCtx_mem` are both primitive — each is derivable
from the other only through a unit representation. -/
class HasOption (C : StepClass.{u, v}) [P : C.HasProd] where
  /-- The representation of an optional value. -/
  option : {A : Type u} → C.Str A → C.Str (Option A)
  /-- Admissible functions act on optional values. -/
  omap_mem : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B},
    C.Hom a b f → C.Hom (option a) (option b) (Option.map f)
  /-- The absent value is admissible as a constant. This is the one constant map
  the layer assumes: a machine that has already returned takes no step, so its
  transition is constantly `none`. -/
  none_mem : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    C.Hom a (option b) fun _ => none
  /-- Sequencing a partial value against an admissible continuation that also
  reads a retained context. Needed to transport a realization along a lens,
  where the pulled-back answer index is partial and the continuation still needs
  the machine's state. -/
  obindCtx_mem : ∀ {A B E : Type u} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    {k : A × E → Option B}, C.Hom (P.prod a e) (option b) k →
      C.Hom (P.prod (option a) e) (option b) fun y => y.1.bind fun j => k (j, y.2)

/-! ## Distributivity -/

/-- A step class whose product and sum representations distribute.

Equivalently — and this is the form the closure theory actually uses, available as
`IsDistributive.elimCtx_mem` — *case analysis in a context* is admissible.

The field is the **inverse** of the map a category theorist calls canonical: the
canonical (cogap) direction is `codistrib_mem` below, which needs no axiom at all.
Both directions being admissible is exactly "the canonical map is an isomorphism
in the subcategory", so this is Cockett's distributivity verbatim rather than a
one-sided weakening. Only the binary case is required; no terminal or initial
representation is assumed, so this is weaker than
`CategoryTheory.IsCartesianDistributive`.

Note that distributivity genuinely does not come for free: every bicartesian
*closed* category is automatically distributive because `X × (-)` is a left
adjoint, but the motivating classes here have no exponentials. -/
class IsDistributive (C : StepClass.{u, v}) [P : C.HasProd] [S : C.HasSum] :
    Prop where
  distrib_mem : ∀ {A B I : Type u} (a : C.Str A) (b : C.Str B) (i : C.Str I),
    C.Hom (P.prod (S.sum a b) i) (S.sum (P.prod a i) (P.prod b i))
      fun x => Sum.elim (fun l => Sum.inl (l, x.2)) (fun r => Sum.inr (r, x.2)) x.1

/-- The canonical direction of the distributivity map, which needs only products
and sums. Together with `IsDistributive.distrib_mem` it exhibits the canonical map
as an isomorphism in the subcategory. -/
theorem codistrib_mem [P : C.HasProd] [S : C.HasSum] {A B I : Type u}
    (a : C.Str A) (b : C.Str B) (i : C.Str I) :
    C.Hom (S.sum (P.prod a i) (P.prod b i)) (P.prod (S.sum a b) i)
      (Sum.elim (Prod.map Sum.inl id) (Prod.map Sum.inr id)) :=
  S.elim_mem (P.map_mem (S.inl_mem a b) (C.id_mem i))
    (P.map_mem (S.inr_mem a b) (C.id_mem i))

/-- Case analysis in a context: dispatching on a sum-valued component while
retaining the rest of the input.

This is the workhorse of the closure theory. Distributivity is equivalent to it;
in the presence of `HasProd.diag_mem` it even implies the unparameterized
`HasSum.elim_mem`, by taking the context to be the sum itself — so the axioms are
not independent. `elim_mem` is nonetheless kept primitive, since deriving it would
churn every instance for no gain. -/
theorem IsDistributive.elimCtx_mem [P : C.HasProd] [S : C.HasSum]
    [D : C.IsDistributive] {A B E Z : Type u} {a : C.Str A} {b : C.Str B}
    {e : C.Str E} {z : C.Str Z} {f : A × E → Z} {g : B × E → Z}
    (hf : C.Hom (P.prod a e) z f) (hg : C.Hom (P.prod b e) z g) :
    C.Hom (P.prod (S.sum a b) e) z
      fun x => Sum.elim (fun l => f (l, x.2)) (fun r => g (r, x.2)) x.1 := by
  refine (C.comp_mem (D.distrib_mem a b e) (S.elim_mem hf hg)).congr ?_
  intro x
  cases x with
  | mk s v => cases s <;> rfl

/-- A distributive step class: a distributive category (Cockett 1993) presented
concretely over `Type u`, together with admissible optional values.

This bundles the structure the closure theory consumes. It is a convenience only;
each individual theorem asks for exactly the mixins it uses. -/
class Distributive (C : StepClass.{u, v}) where
  /-- The class has admissible binary products. -/
  [toHasProd : C.HasProd]
  /-- The class has admissible binary sums. -/
  [toHasSum : C.HasSum]
  /-- The class has admissible optional values. -/
  [toHasOption : C.HasOption]
  /-- The class's products and sums distribute. -/
  [toIsDistributive : C.IsDistributive]

attribute [implicit_reducible, instance] Distributive.toHasProd
  Distributive.toHasSum Distributive.toHasOption

attribute [instance] Distributive.toIsDistributive

/-! ## Refinement between classes -/

set_option linter.checkUnivs false in
/-- A refinement of step classes: a translation of representations carrying
`C`-admissibility to `D`-admissibility, compatibly with the product and sum
representations. Realizability transports forward along a refinement, so a
realization in a small class is a realization in every larger one.

Compatibility with products and sums is not automatic and is not implied by
`hom`, but it is needed for the transport: the realizability layer's derived
representations are built from the boundary with `HasProd.prod` and
`HasSum.sum`, and a refinement that translated those to unrelated
representations would not carry a realization anywhere. -/
-- The two representation universes are independent of each other and of the
-- represented universe: refining a `Type`-valued encoding into a `Prop`-valued
-- one is a typical use.
structure Refines (C : StepClass.{u, v}) (D : StepClass.{u, v₂})
    [C.HasProd] [C.HasSum] [C.HasOption] [D.HasProd] [D.HasSum] [D.HasOption] where
  /-- Translate a `C`-representation into a `D`-representation. -/
  str : {A : Type u} → C.Str A → D.Str A
  /-- Every `C`-admissible function is `D`-admissible between the translations. -/
  hom : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B},
    C.Hom a b f → D.Hom (str a) (str b) f
  /-- The translation preserves product representations. -/
  str_prod : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    str (HasProd.prod a b) = HasProd.prod (str a) (str b)
  /-- The translation preserves sum representations. -/
  str_sum : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    str (HasSum.sum a b) = HasSum.sum (str a) (str b)
  /-- The translation preserves optional representations. -/
  str_option : ∀ {A : Type u} (a : C.Str A),
    str (HasOption.option a) = HasOption.option (str a)

/-- Refinement is reflexive. -/
def Refines.refl (C : StepClass.{u, v}) [C.HasProd] [C.HasSum] [C.HasOption] :
    C.Refines C where
  str a := a
  hom h := h
  str_prod _ _ := rfl
  str_sum _ _ := rfl
  str_option _ := rfl

set_option linter.checkUnivs false in
/-- Refinements compose. -/
-- Three independent representation universes, for the same reason as `Refines`.
def Refines.trans {C : StepClass.{u, v}} {D : StepClass.{u, v₂}}
    {E : StepClass.{u, v₃}} [C.HasProd] [C.HasSum] [C.HasOption] [D.HasProd]
    [D.HasSum] [D.HasOption] [E.HasProd] [E.HasSum] [E.HasOption]
    (R : C.Refines D) (S : D.Refines E) : C.Refines E where
  str a := S.str (R.str a)
  hom h := S.hom (R.hom h)
  str_prod a b := by rw [R.str_prod, S.str_prod]
  str_sum a b := by rw [R.str_sum, S.str_sum]
  str_option a := by rw [R.str_option, S.str_option]

end StepClass

end PFunctor
