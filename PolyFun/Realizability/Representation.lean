/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Realizability.Basic

/-!
# Translation and coding of admissible representations

`StepClass.Str A` is deliberately data: admissibility depends on a chosen
representation of `A`. This module records the two certificates needed to use
that freedom without making a complexity statement representation-dependent.

* `StepClass.PolyTranslatable a b` says that the identity on the represented
  type is admissible in both directions between `a` and `b`. It induces an
  invariance theorem for `StepClass.Hom`, componentwise translation of
  realizability boundaries, and equivalences for bounded and unbounded
  realizability.
* `StepClass.PolyCodable word rep` gives an admissible encoding into a pinned
  word representation and an admissible partial decoder which retracts it.
  Injectivity follows from the retraction; it is not the only hypothesis.

The unqualified prefix `Poly` names the PolyFun-side structural certificate.
Whether admissibility means polynomial time, computability, finiteness, or
something else is determined by the ambient `StepClass`.

`CodeRetract` separates the semantic retraction from admissibility, and has
constructors for products, sums, optional values, and dependent families.
Their codecs are explicit because a bare word type carries no canonical
pairing or tagging discipline.
-/

@[expose] public section

universe u v

namespace PFunctor
namespace StepClass

variable {C : StepClass.{u, v}}

/-! ## Mutually admissible representations -/

/-- Two representations of the same type are polynomially translatable relative
to `C` when the identity function is admissible in both directions.

The name does not assert polynomial time on its own: that interpretation comes
from the chosen step class. -/
structure PolyTranslatable {A : Type u} (a b : C.Str A) : Prop where
  /-- Translate from `a` to `b` without changing the represented value. -/
  forward : C.Hom a b id
  /-- Translate from `b` to `a` without changing the represented value. -/
  backward : C.Hom b a id

namespace PolyTranslatable

/-- Every representation translates to itself. -/
@[refl]
theorem refl {A : Type u} (a : C.Str A) : PolyTranslatable a a :=
  ⟨C.id_mem a, C.id_mem a⟩

/-- Representation translation is symmetric. -/
@[symm]
theorem symm {A : Type u} {a b : C.Str A} (h : PolyTranslatable a b) :
    PolyTranslatable b a :=
  ⟨h.backward, h.forward⟩

/-- Representation translations compose. -/
@[trans]
theorem trans {A : Type u} {a b d : C.Str A} (hab : PolyTranslatable a b)
    (hbd : PolyTranslatable b d) : PolyTranslatable a d where
  forward := hab.forward.postcomp_id hbd.forward
  backward := hbd.backward.postcomp_id hab.backward

/-- Admissibility is invariant under polynomially translatable source and target
representations. -/
theorem hom_iff {A B : Type u} {a a' : C.Str A} {b b' : C.Str B}
    (ha : PolyTranslatable a a') (hb : PolyTranslatable b b') (f : A → B) :
    C.Hom a b f ↔ C.Hom a' b' f := by
  constructor
  · intro hf
    exact (hf.precomp_id ha.backward).postcomp_id hb.forward
  · intro hf
    exact (hf.precomp_id ha.forward).postcomp_id hb.backward

/-- Product representations translate componentwise. -/
theorem prod [P : C.HasProd] {A B : Type u} {a a' : C.Str A} {b b' : C.Str B}
    (ha : PolyTranslatable a a') (hb : PolyTranslatable b b') :
    PolyTranslatable (P.prod a b) (P.prod a' b') where
  forward := P.map_id_mem ha.forward hb.forward
  backward := P.map_id_mem ha.backward hb.backward

/-- Sum representations translate componentwise. -/
theorem sum [S : C.HasSum] {A B : Type u} {a a' : C.Str A} {b b' : C.Str B}
    (ha : PolyTranslatable a a') (hb : PolyTranslatable b b') :
    PolyTranslatable (S.sum a b) (S.sum a' b') where
  forward := S.map_id_mem ha.forward hb.forward
  backward := S.map_id_mem ha.backward hb.backward

/-- Optional-value representations translate with their payloads. -/
theorem option [C.HasProd] [O : C.HasOption] {A : Type u} {a a' : C.Str A}
    (ha : PolyTranslatable a a') :
    PolyTranslatable (O.option a) (O.option a') where
  forward := O.map_id_mem ha.forward
  backward := O.map_id_mem ha.backward

end PolyTranslatable

/-! ## Semantic word retractions -/

/-- An encoding of `A` into words `W` with a partial decoder that is a left
inverse on every encoded value. -/
structure CodeRetract (W A : Type u) where
  /-- Encode a value as a word. -/
  encode : A → W
  /-- Decode a word when it is a valid code. -/
  decode : W → Option A
  /-- Every encoded value decodes to itself. -/
  decode_encode : ∀ value, decode (encode value) = some value

/-- Pairing and projections used to combine two codes in one word. -/
structure CodePairing (W : Type u) where
  /-- Combine two words. -/
  pair : W → W → W
  /-- Read the first component of a paired word. -/
  fst : W → W
  /-- Read the second component of a paired word. -/
  snd : W → W
  /-- First projection after pairing. -/
  fst_pair : ∀ left right, fst (pair left right) = left
  /-- Second projection after pairing. -/
  snd_pair : ∀ left right, snd (pair left right) = right

/-- Tags and a partial tag decoder used to combine two code spaces. -/
structure CodeSum (W : Type u) where
  /-- Encode a left payload. -/
  inl : W → W
  /-- Encode a right payload. -/
  inr : W → W
  /-- Recover a tagged payload. -/
  split : W → Option (W ⊕ W)
  /-- Decode a left tag. -/
  split_inl : ∀ word, split (inl word) = some (Sum.inl word)
  /-- Decode a right tag. -/
  split_inr : ∀ word, split (inr word) = some (Sum.inr word)

/-- Tags and a partial tag decoder for optional codes. -/
structure CodeOption (W : Type u) where
  /-- The absent-value code. -/
  noneCode : W
  /-- Tag a present payload. -/
  someCode : W → W
  /-- Recover the optional payload represented by a word. -/
  split : W → Option (Option W)
  /-- Decode the absent-value code. -/
  split_none : split noneCode = Option.some Option.none
  /-- Decode a present-value code. -/
  split_some : ∀ word, split (someCode word) = Option.some (Option.some word)

namespace CodeRetract

/-- The identity word code. -/
def id (W : Type u) : CodeRetract W W where
  encode := _root_.id
  decode := some
  decode_encode _ := rfl

/-- Compose two semantic coding retractions. -/
def trans {W A B : Type u} (outer : CodeRetract W A)
    (inner : CodeRetract A B) : CodeRetract W B where
  encode value := outer.encode (inner.encode value)
  decode word := (outer.decode word).bind inner.decode
  decode_encode value := by
    rw [outer.decode_encode, Option.bind_some, inner.decode_encode]

/-- Product codes from a word pairing. -/
def prod {W A B : Type u} (pairing : CodePairing W)
    (left : CodeRetract W A) (right : CodeRetract W B) :
    CodeRetract W (A × B) where
  encode value := pairing.pair (left.encode value.1) (right.encode value.2)
  decode word := (left.decode (pairing.fst word)).bind fun leftValue =>
    (right.decode (pairing.snd word)).map fun rightValue => (leftValue, rightValue)
  decode_encode value := by
    rcases value with ⟨leftValue, rightValue⟩
    rw [pairing.fst_pair, pairing.snd_pair, left.decode_encode,
      Option.bind_some, right.decode_encode, Option.map_some]

/-- Sum codes from a partial tag decoder. -/
def sum {W A B : Type u} (codec : CodeSum W) (left : CodeRetract W A)
    (right : CodeRetract W B) : CodeRetract W (A ⊕ B) where
  encode
    | Sum.inl value => codec.inl (left.encode value)
    | Sum.inr value => codec.inr (right.encode value)
  decode word := (codec.split word).bind fun
    | Sum.inl payload => (left.decode payload).map Sum.inl
    | Sum.inr payload => (right.decode payload).map Sum.inr
  decode_encode value := by
    cases value with
    | inl value => simp [codec.split_inl, left.decode_encode]
    | inr value => simp [codec.split_inr, right.decode_encode]

/-- Optional codes from an absent code and a present-value tag. -/
def option {W A : Type u} (codec : CodeOption W) (payload : CodeRetract W A) :
    CodeRetract W (Option A) where
  encode
    | none => codec.noneCode
    | some value => codec.someCode (payload.encode value)
  decode word := (codec.split word).bind fun
    | none => some none
    | some encoded => (payload.decode encoded).map some
  decode_encode value := by
    cases value with
    | none => simp [codec.split_none]
    | some value => simp [codec.split_some, payload.decode_encode]

/-- Codes for a dependent family, represented as a sigma type. The index and
the selected fiber value are paired after being encoded separately. -/
def sigma {W I : Type u} {A : I → Type u} (pairing : CodePairing W)
    (index : CodeRetract W I) (value : ∀ i, CodeRetract W (A i)) :
    CodeRetract W (Σ i, A i) where
  encode entry := pairing.pair (index.encode entry.1) ((value entry.1).encode entry.2)
  decode word := (index.decode (pairing.fst word)).bind fun i =>
    ((value i).decode (pairing.snd word)).map (Sigma.mk i)
  decode_encode entry := by
    rcases entry with ⟨i, entry⟩
    simp [pairing.fst_pair, pairing.snd_pair, index.decode_encode,
      (value i).decode_encode]

/-- A semantic coding retraction has an injective encoder. -/
theorem encode_injective {W A : Type u} (coding : CodeRetract W A) :
    Function.Injective coding.encode := by
  intro left right hencode
  apply Option.some.inj
  calc
    some left = coding.decode (coding.encode left) := (coding.decode_encode left).symm
    _ = coding.decode (coding.encode right) := congrArg coding.decode hencode
    _ = some right := coding.decode_encode right

end CodeRetract

/-! ## Admissible word coding -/

/-- An admissible word encoding and decoding retraction.

Unlike a raw injective encoding, this structure exposes a decoder in the ambient
step class and proves that decoding retracts encoding. For a polynomial-time
step class this is the word-level codability certificate needed to rule out
encodings that hide non-computable advice. -/
structure PolyCodable [C.HasProd] [O : C.HasOption] {W A : Type u}
    (word : C.Str W) (rep : C.Str A) where
  /-- The semantic coding retraction. -/
  toCodeRetract : CodeRetract W A
  /-- Encoding is admissible from the represented value to words. -/
  encode_mem : C.Hom rep word toCodeRetract.encode
  /-- Partial decoding is admissible from words to represented optional values. -/
  decode_mem : C.Hom word (O.option rep) toCodeRetract.decode

namespace PolyCodable

variable [C.HasProd] [O : C.HasOption] {W A : Type u} {word : C.Str W}
  {rep : C.Str A}

/-- The encoder of an admissible coding. -/
abbrev encode (coding : PolyCodable word rep) : A → W :=
  coding.toCodeRetract.encode

/-- The decoder of an admissible coding. -/
abbrev decode (coding : PolyCodable word rep) : W → Option A :=
  coding.toCodeRetract.decode

/-- Decoding retracts encoding. -/
theorem decode_encode (coding : PolyCodable word rep) (value : A) :
    coding.decode (coding.encode value) = some value :=
  coding.toCodeRetract.decode_encode value

/-- A polynomially codable representation has an injective word encoder. -/
theorem encode_injective (coding : PolyCodable word rep) :
    Function.Injective coding.encode :=
  coding.toCodeRetract.encode_injective

/-- Forget admissible decoding and retain the raw injective encoder expected by
word-class representations. -/
def toEncoding (coding : PolyCodable word rep) :
    { encode : A → W // Function.Injective encode } :=
  ⟨coding.encode, coding.encode_injective⟩

/-- Attach admissibility proofs to a semantic coding retraction. -/
def ofCodeRetract (coding : CodeRetract W A)
    (encode_mem : C.Hom rep word coding.encode)
    (decode_mem : C.Hom word (O.option rep) coding.decode) :
    PolyCodable word rep :=
  ⟨coding, encode_mem, decode_mem⟩

end PolyCodable

end StepClass

/-! ## Boundary translation and realizability invariance -/

namespace DynSystem.DynComputation
namespace Boundary

variable {C : StepClass.{u, v}} {p : PFunctor.{u, u}} {A B : Type u}

/-- Componentwise polynomial translatability of two realizability boundaries. -/
structure PolyTranslatable (left right : Boundary C p A B) : Prop where
  /-- Input representations translate in both directions. -/
  input : StepClass.PolyTranslatable left.input right.input
  /-- Result representations translate in both directions. -/
  out : StepClass.PolyTranslatable left.out right.out
  /-- Query-position representations translate in both directions. -/
  pos : StepClass.PolyTranslatable left.pos right.pos
  /-- Tagged-answer representations translate in both directions. -/
  idx : StepClass.PolyTranslatable left.idx right.idx

namespace PolyTranslatable

/-- Boundary translation is reflexive. -/
@[refl]
theorem refl (bd : Boundary C p A B) : PolyTranslatable bd bd :=
  ⟨StepClass.PolyTranslatable.refl bd.input,
    StepClass.PolyTranslatable.refl bd.out,
    StepClass.PolyTranslatable.refl bd.pos,
    StepClass.PolyTranslatable.refl bd.idx⟩

/-- Boundary translation is symmetric. -/
@[symm]
theorem symm {left right : Boundary C p A B}
    (h : PolyTranslatable left right) : PolyTranslatable right left :=
  ⟨h.input.symm, h.out.symm, h.pos.symm, h.idx.symm⟩

/-- Boundary translations compose. -/
@[trans]
theorem trans {left middle right : Boundary C p A B}
    (hlm : PolyTranslatable left middle) (hmr : PolyTranslatable middle right) :
    PolyTranslatable left right :=
  ⟨hlm.input.trans hmr.input, hlm.out.trans hmr.out,
    hlm.pos.trans hmr.pos, hlm.idx.trans hmr.idx⟩

/-- Derived one-step-readout representations translate componentwise. -/
theorem head [S : C.HasSum] {left right : Boundary C p A B}
    (h : PolyTranslatable left right) :
    StepClass.PolyTranslatable left.head right.head :=
  h.out.sum h.pos

/-- Derived state-and-answer representations translate componentwise while the
chosen hidden-state representation stays fixed. -/
theorem stateIdx [P : C.HasProd] {left right : Boundary C p A B}
    (h : PolyTranslatable left right) {State : Type u} (state : C.Str State) :
    StepClass.PolyTranslatable (left.stateIdx state) (right.stateIdx state) :=
  (StepClass.PolyTranslatable.refl state).prod h.idx

end PolyTranslatable

end Boundary

variable {C : StepClass.{u, v}} [P : C.HasProd] [S : C.HasSum]
  [O : C.HasOption] {p : PFunctor.{u, u}} [DecidableEq p.A]
  {A B : Type u} {left right : Boundary C p A B}
  {program : A → FreeM p B}

/-- Transport a realization across componentwise polynomially translatable
boundary representations without changing its machine or hidden-state layout. -/
def Realization.translateBoundary (h : left.PolyTranslatable right)
    (R : Realization C left) : Realization C right where
  machine := R.machine
  state := R.state
  init_mem := (h.input.hom_iff (StepClass.PolyTranslatable.refl R.state)
    R.machine.init).mp R.init_mem
  head_mem := ((StepClass.PolyTranslatable.refl R.state).hom_iff h.head
    R.machine.head).mp R.head_mem
  update_mem := ((h.stateIdx R.state).hom_iff
    (StepClass.PolyTranslatable.refl (O.option R.state))
    R.machine.update?).mp R.update_mem

/-- Unbounded realizability is invariant under componentwise polynomial
translation of every pinned boundary representation. -/
theorem isRealizableBy_iff_of_boundary_polyTranslatable
    (h : left.PolyTranslatable right) :
    IsRealizableBy C left program ↔ IsRealizableBy C right program := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R.translateBoundary h, hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨R.translateBoundary h.symm, hR⟩

/-- Bounded realizability is invariant under componentwise polynomial
translation of every pinned boundary representation, at the same query budget. -/
theorem isRealizableWithin_iff_of_boundary_polyTranslatable
    (h : left.PolyTranslatable right) (k : ℕ) :
    IsRealizableWithin C left program k ↔ IsRealizableWithin C right program k := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R.translateBoundary h, hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨R.translateBoundary h.symm, hR⟩

end DynSystem.DynComputation
end PFunctor
