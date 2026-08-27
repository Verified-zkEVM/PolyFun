/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Realizability.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

/-!
# Concrete step classes

Four instantiations of `PFunctor.StepClass`, in increasing order of content.

* `StepClass.unconstrained` — every type is representable and every function
  admissible. Realizability collapses to plain implementability, which the two
  non-vacuity checks confirm is never a real restriction:
  `DynSystem.isRealizableBy_unconstrained` for arbitrary dynamical systems and
  `DynSystem.DynComputation.isRealizableBy_unconstrained` for returning program
  families.
* `StepClass.finite` — a type is representable when it is finite. Realizability in
  this class is *finite-state realizability*, the notion Church's synthesis
  problem asks about and which Pnueli and Rosner (1989) made precise; see
  `REFERENCES.md`.
* `StepClass.computable` — Mathlib's `Primcodable` representations and
  `Computable` functions: machines whose transition functions are computable.
* `StepClass.ofWordClass` — the bridge from an externally defined class of *word*
  functions `W → W`. Complexity classes in the wild are almost always presented
  this way, on one concrete function type such as `List Bool → List Bool`, with no
  encoding-generic predicate.

Each class carries all four mixins: `HasProd`, `HasSum`, `HasOption`, and
`IsDistributive`. For `unconstrained` and `finite` every obligation is trivial.
For `computable` they are short, because Mathlib's `Computable.sumCasesOn` and
`Computable.option_map` are already stated in *contextual* form — branches
`α → β → σ` with `α` the ambient context — which is exactly distributivity.

## What a word class has to supply

None of the four mixins is automatic for a monomorphic word class. Bundle the
required data as a `WordClass`: identity and composition closure, a `WordPairing`
codec, a `WordTagging` scheme with a distinguished word, and a `WordDistrib`
rearrangement moving a tag past a pairing. `WordClass.toStepClass` then carries all
four mixins as instances, so a client never names them.

`WordDistrib` is forced by the mathematics rather than by this presentation:
`WordTagging.elim` hands each branch only the untagged payload, so its branches
cannot see the surrounding context and a tag cannot be moved past a pairing using
`elim` alone.

What this costs a real client: `Complexity.FP` (complexitylib) and
`Cslib.Turing.PolyTimeComputable` (cslib) both supply the identity and composition
closure, and complexitylib has the pairing ingredients (`Complexity.pair`,
`unpair?`, `delimit`) — but neither exposes them as class-level closure results,
and cslib has no pairing or projection machines at all. cslib's
`PolyTimeComputable` is additionally `Type`-valued with a `Monotone` side condition
on `comp` whose removal is still a `TODO` upstream, so `Mem f :=
Nonempty (PolyTimeComputable f)` needs a monotonisation lemma that does not exist
yet.
-/

@[expose] public section

universe u v s t

namespace PFunctor

namespace StepClass

/-! ## The unconstrained class -/

/-- The step class that constrains nothing: every type is representable, by no
data, and every function is admissible. -/
def unconstrained : StepClass.{u, v} where
  Str _ := PUnit.{v + 1}
  Hom _ _ _ := True
  id_mem _ := True.intro
  comp_mem _ _ := True.intro

instance : (unconstrained.{u, v}).HasProd where
  prod _ _ := PUnit.unit
  fst_mem _ _ := True.intro
  snd_mem _ _ := True.intro
  pair_mem _ _ := True.intro

instance : (unconstrained.{u, v}).HasSum where
  sum _ _ := PUnit.unit
  inl_mem _ _ := True.intro
  inr_mem _ _ := True.intro
  elim_mem _ _ := True.intro

instance : (unconstrained.{u, v}).HasOption where
  option _ := PUnit.unit
  omap_mem _ := True.intro
  none_mem _ _ := True.intro
  obindCtx_mem _ := True.intro
  some_mem _ := True.intro

instance : (unconstrained.{u, v}).IsDistributive where
  distrib_mem _ _ _ := True.intro

-- Independent universes, as in `StepClass.HasULiftProd` itself.
set_option linter.checkUnivs false in
instance : (unconstrained.{max s t, v}).HasULiftProd.{s, t} where
  uliftProd _ _ := PUnit.unit
  up_mem _ _ := True.intro
  down_mem _ _ := True.intro

/-! ## The finite class -/

/-- The step class of finite representations: a type is representable exactly when
it is finite, and every function between finite types is admissible. -/
def finite : StepClass.{u, u} where
  Str := Fintype
  Hom _ _ _ := True
  id_mem _ := True.intro
  comp_mem _ _ := True.intro

instance : (finite.{u}).HasProd where
  prod {A B} a b := @instFintypeProd A B a b
  fst_mem _ _ := True.intro
  snd_mem _ _ := True.intro
  pair_mem _ _ := True.intro

instance : (finite.{u}).HasSum where
  sum {A B} a b := @instFintypeSum A B a b
  inl_mem _ _ := True.intro
  inr_mem _ _ := True.intro
  elim_mem _ _ := True.intro

instance : (finite.{u}).HasOption where
  option {A} a := by
    let : Fintype A := a
    exact (inferInstance : Fintype (Option A))
  omap_mem _ := True.intro
  none_mem _ _ := True.intro
  obindCtx_mem _ := True.intro
  some_mem _ := True.intro

instance : (finite.{u}).IsDistributive where
  distrib_mem _ _ _ := True.intro

-- Independent universes, as in `StepClass.HasULiftProd` itself.
set_option linter.checkUnivs false in
instance : (finite.{max s t}).HasULiftProd.{s, t} where
  uliftProd {A B} a b := by
    let : Fintype (ULift.{t} A) := a
    let : Fintype (ULift.{t} B) := b
    exact Fintype.ofEquiv (ULift.{t} A × ULift.{t} B)
      ((_root_.Equiv.prodCongr _root_.Equiv.ulift _root_.Equiv.ulift).trans
        _root_.Equiv.ulift.symm)
  up_mem _ _ := True.intro
  down_mem _ _ := True.intro

/-! ## The computable class -/

/-- The step class of computable functions between `Primcodable` types.

The representation carried by a type is its `Primcodable` structure, which is
genuine data: `Computable f` is a statement about the encodings, so the class
cannot be phrased without them. -/
def computable : StepClass.{u, u} where
  Str := Primcodable
  Hom {A B} a b f := @Computable A B a b f
  id_mem {A} a := by
    let : Primcodable A := a
    exact Computable.id
  comp_mem {A B D} {a b d} {f g} hf hg := by
    let : Primcodable A := a
    let : Primcodable B := b
    let : Primcodable D := d
    have hf' : Computable f := hf
    have hg' : Computable g := hg
    exact hg'.comp hf'

instance : (computable.{u}).HasProd where
  prod {A B} a b := @Primcodable.prod A B a b
  fst_mem {A B} a b := by
    let : Primcodable A := a
    let : Primcodable B := b
    exact Computable.fst
  snd_mem {A B} a b := by
    let : Primcodable A := a
    let : Primcodable B := b
    exact Computable.snd
  pair_mem {A B D} {a b d} {f g} hf hg := by
    let : Primcodable A := a
    let : Primcodable B := b
    let : Primcodable D := d
    have hf' : Computable f := hf
    have hg' : Computable g := hg
    exact hf'.pair hg'

instance : (computable.{u}).HasSum where
  sum {A B} a b := @Primcodable.sum A B a b
  inl_mem {A B} a b := by
    let : Primcodable A := a
    let : Primcodable B := b
    exact Primrec.sumInl.to_comp
  inr_mem {A B} a b := by
    let : Primcodable A := a
    let : Primcodable B := b
    exact Primrec.sumInr.to_comp
  elim_mem {A B D} {a b d} {f g} hf hg := by
    let : Primcodable A := a
    let : Primcodable B := b
    let : Primcodable D := d
    have hf' : Computable f := hf
    have hg' : Computable g := hg
    refine Computable.of_eq (Computable.sumCasesOn Computable.id
      (hf'.comp Computable.snd).to₂ (hg'.comp Computable.snd).to₂) ?_
    intro x
    cases x <;> rfl

instance : (computable.{u}).HasOption where
  option {A} a := @Primcodable.option A a
  omap_mem {A B} {a b} {f} hf := by
    let : Primcodable A := a
    let : Primcodable B := b
    have hf' : Computable f := hf
    refine Computable.of_eq
      (Computable.option_map Computable.id (hf'.comp Computable.snd).to₂) ?_
    intro x
    cases x <;> rfl
  none_mem {A B} a b := by
    let : Primcodable A := a
    let : Primcodable B := b
    exact Computable.const none
  obindCtx_mem {A B E} {a b e} {k} hk := by
    let : Primcodable A := a
    let : Primcodable B := b
    let : Primcodable E := e
    have hk' : Computable k := hk
    refine Computable.of_eq
      (Computable.option_bind Computable.fst
        (hk'.comp (Computable.pair Computable.snd
          (Computable.snd.comp Computable.fst))).to₂) ?_
    intro y
    cases y.1 <;> rfl
  some_mem {A} a := by
    let : Primcodable A := a
    exact Computable.option_some

-- Independent universes, as in `StepClass.HasULiftProd` itself.
set_option linter.checkUnivs false in
instance : (computable.{max s t}).HasULiftProd.{s, t} where
  uliftProd {A B} a b := by
    let : Primcodable (ULift.{t} A) := a
    let : Primcodable (ULift.{t} B) := b
    exact Primcodable.ofEquiv (ULift.{t} A × ULift.{t} B)
      (_root_.Equiv.ulift.trans
        (_root_.Equiv.prodCongr _root_.Equiv.ulift _root_.Equiv.ulift).symm)
  up_mem {A B} a b := by
    let : Primcodable (ULift.{t} A) := a
    let : Primcodable (ULift.{t} B) := b
    let e : ULift.{t} (A × B) ≃ ULift.{t} A × ULift.{t} B :=
      _root_.Equiv.ulift.trans
        (_root_.Equiv.prodCongr _root_.Equiv.ulift _root_.Equiv.ulift).symm
    let : Primcodable (ULift.{t} (A × B)) := Primcodable.ofEquiv _ e
    exact (Primrec.of_equiv_symm (e := e)).to_comp
  down_mem {A B} a b := by
    let : Primcodable (ULift.{t} A) := a
    let : Primcodable (ULift.{t} B) := b
    let e : ULift.{t} (A × B) ≃ ULift.{t} A × ULift.{t} B :=
      _root_.Equiv.ulift.trans
        (_root_.Equiv.prodCongr _root_.Equiv.ulift _root_.Equiv.ulift).symm
    let : Primcodable (ULift.{t} (A × B)) := Primcodable.ofEquiv _ e
    exact (Primrec.of_equiv (e := e)).to_comp

/-- Mathlib's sum eliminator is already stated in *contextual* form — its branches
are `α → β → σ` with `α` the ambient context — which is exactly distributivity. -/
instance : (computable.{u}).IsDistributive where
  distrib_mem {A B I} a b i := by
    let : Primcodable A := a
    let : Primcodable B := b
    let : Primcodable I := i
    refine Computable.of_eq (Computable.sumCasesOn Computable.fst
      (Primrec.sumInl.to_comp.comp (Computable.pair Computable.snd
        (Computable.snd.comp Computable.fst))).to₂
      (Primrec.sumInr.to_comp.comp (Computable.pair Computable.snd
        (Computable.snd.comp Computable.fst))).to₂) ?_
    rintro ⟨x | x, j⟩ <;> rfl

/-! ## The bridge from a class of word functions -/

/-- A pairing codec on `W` whose operations the word class `Q` admits. This is the
data a monomorphic word class needs in order to represent binary products. -/
structure WordPairing {W : Type u} (Q : (W → W) → Prop) where
  /-- Pair two words. -/
  pair : W → W → W
  /-- Pairing is injective in both arguments jointly. -/
  pair_inj : ∀ w₁ w₂ w₁' w₂', pair w₁ w₂ = pair w₁' w₂' → w₁ = w₁' ∧ w₂ = w₂'
  /-- Recover the first component. -/
  fst : W → W
  /-- Recover the second component. -/
  snd : W → W
  /-- The first projection is admissible. -/
  fst_mem : Q fst
  /-- The second projection is admissible. -/
  snd_mem : Q snd
  /-- `fst` is a left inverse of pairing. -/
  fst_pair : ∀ w₁ w₂, fst (pair w₁ w₂) = w₁
  /-- `snd` is a right inverse of pairing. -/
  snd_pair : ∀ w₁ w₂, snd (pair w₁ w₂) = w₂
  /-- Admissible functions can be paired. -/
  pair_mem : ∀ {f g : W → W}, Q f → Q g → Q fun w => pair (f w) (g w)

/-- A tagging scheme on `W` whose operations the word class `Q` admits. This is the
data a monomorphic word class needs in order to represent binary sums. -/
structure WordTagging {W : Type u} (Q : (W → W) → Prop) where
  /-- Tag a word as coming from the left summand. -/
  inl : W → W
  /-- Tag a word as coming from the right summand. -/
  inr : W → W
  /-- Left tagging is admissible. -/
  inl_mem : Q inl
  /-- Right tagging is admissible. -/
  inr_mem : Q inr
  /-- Left tagging is injective. -/
  inl_inj : Function.Injective inl
  /-- Right tagging is injective. -/
  inr_inj : Function.Injective inr
  /-- The two tags are distinguishable. -/
  inl_ne_inr : ∀ w₁ w₂, inl w₁ ≠ inr w₂
  /-- Dispatch on the tag. -/
  elim : (W → W) → (W → W) → W → W
  /-- Dispatch on admissible branches is admissible. -/
  elim_mem : ∀ {f g : W → W}, Q f → Q g → Q (elim f g)
  /-- Dispatch takes the left branch on a left tag. -/
  elim_inl : ∀ (f g : W → W) (w : W), elim f g (inl w) = f w
  /-- Dispatch takes the right branch on a right tag. -/
  elim_inr : ∀ (f g : W → W) (w : W), elim f g (inr w) = g w
  /-- A distinguished word, used as the payload of the absent optional value. -/
  pt : W
  /-- The constant map at the distinguished word is admissible. -/
  const_mem : Q fun _ => pt

/-- Moving a tag past a pairing: the word-level content of distributivity.

This datum is forced by the mathematics rather than by the presentation.
`WordTagging.elim` hands each branch only the *untagged* payload, so its branches
cannot see the surrounding context, and a tag therefore cannot be moved past a
pairing using `elim` alone. -/
structure WordDistrib {W : Type u} (Q : (W → W) → Prop) (P : WordPairing Q)
    (T : WordTagging Q) where
  /-- Move the tag of a paired word's first component outwards. -/
  distrib : W → W
  /-- The rearrangement is admissible. -/
  distrib_mem : Q distrib
  /-- On a left tag. -/
  distrib_inl : ∀ w v, distrib (P.pair (T.inl w) v) = T.inl (P.pair w v)
  /-- On a right tag. -/
  distrib_inr : ∀ w v, distrib (P.pair (T.inr w) v) = T.inr (P.pair w v)

/-- The step class built from a class `Q` of word functions on `W` that contains
the identity and is closed under composition.

A type is representable by an injective encoding into `W` and a function is
admissible when some `Q`-function intertwines the encodings. This is intentionally
the raw bridge: security-sensitive boundaries need a separately pinned
admissible encode/decode retraction, since injectivity alone does not make the
representation complexity-invariant. -/
def ofWordClass (W : Type u) (Q : (W → W) → Prop) (hid : Q id)
    (hcomp : ∀ {f g : W → W}, Q f → Q g → Q (g ∘ f)) : StepClass.{u, u} where
  Str A := { encode : A → W // Function.Injective encode }
  Hom eA eB f := ∃ q : W → W, Q q ∧ ∀ x, q (eA.1 x) = eB.1 (f x)
  id_mem _ := ⟨id, hid, fun _ => rfl⟩
  comp_mem := by
    rintro A B D a b d f g ⟨qf, hqf, hfEq⟩ ⟨qg, hqg, hgEq⟩
    refine ⟨qg ∘ qf, hcomp hqf hqg, fun x => ?_⟩
    simp only [Function.comp_apply, hfEq, hgEq]

/-- All the word-level data a monomorphic class needs in order to be a
distributive step class: identity and composition closure, a pairing codec, a
tagging scheme, and the tag-past-pairing rearrangement.

Supplying one of these is what an external complexity library has to do. The four
`StepClass` mixins are then instances on `toStepClass`, so a client never has to
name them. -/
structure WordClass (W : Type u) where
  /-- Which word functions the class admits. -/
  Mem : (W → W) → Prop
  /-- The identity is admissible. -/
  id_mem : Mem id
  /-- Admissible word functions compose. -/
  comp_mem : ∀ {f g : W → W}, Mem f → Mem g → Mem (g ∘ f)
  /-- A pairing codec. -/
  pairing : WordPairing Mem
  /-- A tagging scheme. -/
  tagging : WordTagging Mem
  /-- The tag-past-pairing rearrangement. -/
  distributor : WordDistrib Mem pairing tagging

/-- The step class presented by a bundle of word-level data. -/
@[reducible] def WordClass.toStepClass {W : Type u} (V : WordClass W) :
    StepClass.{u, u} :=
  ofWordClass W V.Mem V.id_mem V.comp_mem

/-- Products for a word class, from a pairing codec. -/
@[reducible] def ofWordClass.hasProd {W : Type u} {Q : (W → W) → Prop} {hid : Q id}
    {hcomp : ∀ {f g : W → W}, Q f → Q g → Q (g ∘ f)}
    (P : WordPairing Q) : (ofWordClass W Q hid hcomp).HasProd where
  prod a b :=
    ⟨fun x => P.pair (a.1 x.1) (b.1 x.2), by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
      obtain ⟨h₁, h₂⟩ := P.pair_inj _ _ _ _ h
      exact Prod.ext (a.2 h₁) (b.2 h₂)⟩
  fst_mem _ _ := ⟨P.fst, P.fst_mem, fun _ => P.fst_pair _ _⟩
  snd_mem _ _ := ⟨P.snd, P.snd_mem, fun _ => P.snd_pair _ _⟩
  pair_mem := by
    rintro A B D a b d f g ⟨qf, hqf, hfEq⟩ ⟨qg, hqg, hgEq⟩
    refine ⟨fun w => P.pair (qf w) (qg w), P.pair_mem hqf hqg, fun x => ?_⟩
    change P.pair (qf (a.1 x)) (qg (a.1 x)) = P.pair (b.1 (f x)) (d.1 (g x))
    rw [hfEq, hgEq]

/-- Sums for a word class, from a tagging scheme. -/
@[reducible] def ofWordClass.hasSum {W : Type u} {Q : (W → W) → Prop} {hid : Q id}
    {hcomp : ∀ {f g : W → W}, Q f → Q g → Q (g ∘ f)}
    (T : WordTagging Q) : (ofWordClass W Q hid hcomp).HasSum where
  sum a b :=
    ⟨Sum.elim (fun x => T.inl (a.1 x)) fun y => T.inr (b.1 y), by
      rintro (x | x) (y | y) h
      · exact congrArg Sum.inl (a.2 (T.inl_inj h))
      · exact absurd h (T.inl_ne_inr _ _)
      · exact absurd h.symm (T.inl_ne_inr _ _)
      · exact congrArg Sum.inr (b.2 (T.inr_inj h))⟩
  inl_mem _ _ := ⟨T.inl, T.inl_mem, fun _ => rfl⟩
  inr_mem _ _ := ⟨T.inr, T.inr_mem, fun _ => rfl⟩
  elim_mem := by
    rintro A B D a b d f g ⟨qf, hqf, hfEq⟩ ⟨qg, hqg, hgEq⟩
    refine ⟨T.elim qf qg, T.elim_mem hqf hqg, fun x => ?_⟩
    cases x with
    | inl x =>
        change T.elim qf qg (T.inl (a.1 x)) = d.1 (f x)
        rw [T.elim_inl, hfEq]
    | inr y =>
        change T.elim qf qg (T.inr (b.1 y)) = d.1 (g y)
        rw [T.elim_inr, hgEq]

section WordClassInstances

variable {W : Type u} (V : WordClass W)

instance WordClass.instHasProd : V.toStepClass.HasProd :=
  ofWordClass.hasProd V.pairing

instance WordClass.instHasSum : V.toStepClass.HasSum :=
  ofWordClass.hasSum V.tagging

/-- Optional values for a word class: the absent value is the right tag carrying
the distinguished word.

`obindCtx_mem` needs the tag-past-pairing rearrangement, because sequencing must
inspect the tag of the first component while retaining the second. -/
instance WordClass.instHasOption : V.toStepClass.HasOption where
  option a :=
    ⟨fun o => o.elim (V.tagging.inr V.tagging.pt) fun x => V.tagging.inl (a.1 x), by
      rintro (_ | x) (_ | y) h
      · rfl
      · exact absurd h.symm (V.tagging.inl_ne_inr _ _)
      · exact absurd h (V.tagging.inl_ne_inr _ _)
      · exact congrArg some (a.2 (V.tagging.inl_inj h))⟩
  omap_mem := by
    rintro A B a b f ⟨qf, hqf, hfEq⟩
    refine ⟨V.tagging.elim (fun w => V.tagging.inl (qf w)) V.tagging.inr,
      V.tagging.elim_mem (V.comp_mem hqf V.tagging.inl_mem) V.tagging.inr_mem, fun o => ?_⟩
    cases o with
    | none =>
        change V.tagging.elim _ _ (V.tagging.inr V.tagging.pt) = V.tagging.inr V.tagging.pt
        rw [V.tagging.elim_inr]
    | some x =>
        change V.tagging.elim _ _ (V.tagging.inl (a.1 x)) = V.tagging.inl (b.1 (f x))
        rw [V.tagging.elim_inl, hfEq]
  none_mem a b :=
    ⟨fun _ => V.tagging.inr V.tagging.pt,
      V.comp_mem V.tagging.const_mem V.tagging.inr_mem, fun _ => rfl⟩
  some_mem a := ⟨V.tagging.inl, V.tagging.inl_mem, fun _ => rfl⟩
  obindCtx_mem := by
    rintro A B E a b e k ⟨qk, hqk, hkEq⟩
    refine ⟨V.tagging.elim qk (fun _ => V.tagging.inr V.tagging.pt) ∘
        V.distributor.distrib,
      V.comp_mem V.distributor.distrib_mem
        (V.tagging.elim_mem hqk (V.comp_mem V.tagging.const_mem V.tagging.inr_mem)),
      fun y => ?_⟩
    obtain ⟨o, v⟩ := y
    cases o with
    | none =>
        change V.tagging.elim _ _
          (V.distributor.distrib (V.pairing.pair (V.tagging.inr V.tagging.pt)
            (e.1 v))) = V.tagging.inr V.tagging.pt
        rw [V.distributor.distrib_inr, V.tagging.elim_inr]
    | some j =>
        change V.tagging.elim _ _
          (V.distributor.distrib (V.pairing.pair (V.tagging.inl (a.1 j))
            (e.1 v))) = _
        rw [V.distributor.distrib_inl, V.tagging.elim_inl]
        exact hkEq (j, v)

/-- Distributivity for a word class: exactly the tag-past-pairing
rearrangement. -/
instance WordClass.instIsDistributive : V.toStepClass.IsDistributive where
  distrib_mem a b i := by
    refine ⟨V.distributor.distrib, V.distributor.distrib_mem, fun x => ?_⟩
    obtain ⟨s, v⟩ := x
    cases s with
    | inl l =>
        change V.distributor.distrib
            (V.pairing.pair (V.tagging.inl (a.1 l)) (i.1 v)) =
          V.tagging.inl (V.pairing.pair (a.1 l) (i.1 v))
        rw [V.distributor.distrib_inl]
    | inr r =>
        change V.distributor.distrib
            (V.pairing.pair (V.tagging.inr (b.1 r)) (i.1 v)) =
          V.tagging.inr (V.pairing.pair (b.1 r) (i.1 v))
        rw [V.distributor.distrib_inr]

end WordClassInstances

end StepClass

namespace DynSystem

variable {p : PFunctor.{u, u}} {State : Type u}

/-! ## Unconstrained dynamical systems

This section mirrors the `DynSystem.DynComputation` non-vacuity block below for
the non-returning realizability track; keep the two in sync. -/

/-- The interface boundary carrying no representation information for an
arbitrary dynamical system. -/
def Boundary.unconstrained (p : PFunctor.{u, u}) :
    Boundary StepClass.unconstrained.{u, v} p :=
  ⟨PUnit.unit, PUnit.unit⟩

/-- Every polynomial lens is admissible between unconstrained dynamical-system
boundaries. Classical equality is used only to define the partial pullback on
mismatched target-position tags. -/
noncomputable def _root_.PFunctor.Lens.IsDynAdmissible.unconstrained
    {p q : PFunctor.{u, u}} (lens : Lens p q) :
    lens.IsDynAdmissible StepClass.unconstrained
      (Boundary.unconstrained p) (Boundary.unconstrained q) := by
  classical
  refine ⟨True.intro, lens.pullPosIdx, True.intro, ?_⟩
  intro position direction
  simp [Lens.pullPosIdx]

/-- Every dynamical system is structurally realizable in the unconstrained
class.  Classical equality is used only to choose a partial extension on junk
position tags; the class admits every function, and enabled transitions agree
with the original system by construction. -/
theorem isRealizableBy_unconstrained (system : DynSystem State p) :
    IsRealizableBy StepClass.unconstrained.{u, v}
      (Boundary.unconstrained p) system := by
  classical
  exact ⟨⟨PUnit.unit, True.intro, system.update?, True.intro,
    system.update?_of_eq⟩⟩

/-- Every choice-product lens is admissible between unconstrained boundaries.
Classical equality is used only to define the partial routed pullback on
mismatched target-position tags. -/
noncomputable def _root_.PFunctor.Lens.IsChoiceAdmissible.unconstrained
    {p q r : PFunctor.{u, u}} (lens : Lens (PFunctor.prod p q) r) :
    lens.IsChoiceAdmissible StepClass.unconstrained.{u, v}
      (Boundary.unconstrained p) (Boundary.unconstrained q)
      (Boundary.unconstrained r) := by
  classical
  exact ⟨True.intro, lens.pullChoicePosIdx, True.intro,
    lens.pullChoicePosIdx_enabled⟩

end DynSystem

namespace DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {α β : Type u}

/-! ## Non-vacuity

This section mirrors the `DynSystem` unconstrained block above for the
returning realizability track; keep the two in sync. -/

/-- The boundary carrying no information, over the unconstrained class. -/
def Boundary.unconstrained (p : PFunctor.{u, u}) (α β : Type u) :
    Boundary StepClass.unconstrained.{u, v} p α β :=
  ⟨PUnit.unit, PUnit.unit, PUnit.unit, PUnit.unit⟩

/-- Non-vacuity of the whole layer: with no constraint on the step maps,
realizability is exactly plain implementability, and every well-founded program
family is realized — by the canonical machine whose states are the residual
programs.

Any *failure* of realizability is therefore attributable to the step class, never
to the shape of the definition. -/
theorem isRealizableBy_unconstrained [DecidableEq p.A] (program : α → FreeM p β) :
    IsRealizableBy StepClass.unconstrained.{u, v}
      (Boundary.unconstrained p α β) program :=
  ⟨⟨ofFreeM program, PUnit.unit, True.intro, True.intro, True.intro⟩,
    implements_ofFreeM program⟩

/-! ## Finite-state realizability -/

/-- Finite-state realizability: the program family is implemented by a machine
with a finite state set. This is the notion Church's synthesis problem asks about,
and the specialization of `IsRealizableBy` at `StepClass.finite`. -/
abbrev IsFiniteStateRealizable [DecidableEq p.A]
    (bd : Boundary StepClass.finite.{u} p α β) (program : α → FreeM p β) : Prop :=
  IsRealizableBy StepClass.finite bd program

/-- Finite-state realizability within a budget bounds the program's query depth.
The machine's finiteness plays no part: the bound is carried by the budget. -/
theorem IsFiniteStateRealizable.isTotalRollBound [DecidableEq p.A]
    {bd : Boundary StepClass.finite.{u} p α β} {program : α → FreeM p β} {k : ℕ}
    (h : IsRealizableWithin StepClass.finite bd program k) (input : α) :
    (program input).IsTotalRollBound k :=
  h.isTotalRollBound input

end DynSystem.DynComputation

end PFunctor
