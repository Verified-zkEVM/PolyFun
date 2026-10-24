/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.Representation
public import PolyFunCryptol.Model.ResolvedNative

/-!
# Certified Cryptol meanings

A certificate states that a Cryptol function meaning, applied to every fully defined
data input, returns the fully defined image of a total native function. `DataCertificate`,
`DataContract` and `CorrespondsOn` are `Control.Semantics.CertifiedMeaning`,
`DataContract` and `CorrespondsOn` at Cryptol's data embedding, so composition,
restricted admissibility profiles and contract transfer are the generic theorems.

Two producers construct certificates:
* `Resolved.dataCertificate` evaluates resolved source natively; `simp` usually discharges
  its evaluation obligation for every input at once;
* `Finite.Term.dataCertificate` certifies the compact source translation of a finite
  description.
-/

public section

open OmegaCompletePartialOrder IPFunctor.ScopedSignature
open Cryptol.Finite (DataShape encodeData dataEmbedding)

namespace Cryptol

variable {a b : Finite.Ty}

/-- Total correctness of a Cryptol function meaning on fully defined data. -/
abbrev DataContract (ha : DataShape a) (hb : DataShape b)
    (f : Computation (.arrow a.core b.core))
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) : Prop :=
  Control.Semantics.DataContract (dataEmbedding ha) (dataEmbedding hb)
    (DomainResult.applyContinuous f) pre post

/-- A Cryptol function meaning agrees with a native function on admissible data.
Outside `valid`, source errors and divergence remain possible. -/
abbrev CorrespondsOn (ha : DataShape a) (hb : DataShape b) (valid : a.Native → Prop)
    (f : Computation (.arrow a.core b.core)) (g : a.Native → b.Native) : Prop :=
  Control.Semantics.CorrespondsOn (dataEmbedding ha) (dataEmbedding hb) valid
    (DomainResult.applyContinuous f) g

/-- A meaning on Cryptol data, certified against a total native function. -/
abbrev DataCertificate (ha : DataShape a) (hb : DataShape b) :=
  Control.Semantics.CertifiedMeaning (dataEmbedding ha) (dataEmbedding hb)

/-! ## Native data -/

namespace Finite.DataShape

/-- The native evaluation result of fully defined data. -/
@[expose] def native : {a : Finite.Ty} → DataShape a → a.Native → Native.Result a.core
  | _, .bit, x => some x
  | _, .word _, x => Native.wordResult x
  | _, .prod ha hb, x => some (native ha x.1, native hb x.2)
  | _, .seq _ ha, xs => some fun i => native ha (xs i)

@[simp] theorem native_bit (x : Bool) : DataShape.bit.native x = some x := rfl

@[simp] theorem native_word {n : Nat} (x : BitVec n) :
    (DataShape.word n).native x = Native.wordResult x := rfl

@[simp] theorem native_prod {a b : Finite.Ty} (ha : DataShape a) (hb : DataShape b)
    (x : a.Native × b.Native) :
    (DataShape.prod ha hb).native x = some (ha.native x.1, hb.native x.2) := rfl

/-- Canonical lazy data represents its native evaluation result. -/
theorem agrees_native (ha : DataShape a) (x : a.Native) :
    Native.Agrees a.core (encodeData ha x) (ha.native x) := by
  induction ha with
  | bit => rintro _ ⟨⟩; rfl
  | word n => rintro _ ⟨⟩; exact Native.represents_word x
  | prod ha hb iha ihb => rintro _ ⟨⟩; exact ⟨_, _, rfl, iha x.1, ihb x.2⟩
  | seq n ha ih => rintro _ ⟨⟩; exact ⟨_, rfl, fun i => ih (x i)⟩

/-- A lazy computation that agrees with fully defined native data is its canonical image. -/
theorem eq_encodeData_of_agrees (hb : DataShape b) {d : Computation b.core} {y : b.Native}
    (h : Native.Agrees b.core d (hb.native y)) : d = encodeData hb y := by
  induction hb with
  | bit => exact h y rfl
  | word n => exact Native.eq_wordValue_of_bits? (h _ rfl) (Native.bits?_word y)
  | prod ha hb iha ihb =>
      obtain ⟨u, v, rfl, hu, hv⟩ := h _ rfl
      rw [iha hu, ihb hv]
      rfl
  | seq n ha ih =>
      obtain ⟨ds, rfl, hds⟩ := h _ rfl
      apply congrArg DomainResult.value
      funext i
      exact ih (hds i)

end Finite.DataShape

/-! ## Producers -/

namespace Resolved

/-- A closed function whose native evaluation returns fully defined data at an input
has that canonical result as its lazy meaning there. -/
theorem apply_data_of_native (ha : DataShape a) (hb : DataShape b)
    (t : Term [] (.arrow a.core b.core)) {x : a.Native} {y : b.Native}
    (h : (t.denote native Env.empty).bind (fun f => f (ha.native x)) = hb.native y) :
    DomainResult.applyContinuous (denote t Environment.empty) (encodeData ha x) =
      encodeData hb y := by
  obtain ⟨v, hv⟩ : ∃ v, hb.native y = some v := by cases hb <;> exact ⟨_, rfl⟩
  obtain ⟨f, hf, hfx⟩ := Option.bind_eq_some_iff.mp (h.trans hv)
  obtain ⟨g, hg, hfg⟩ := denote_agrees t f hf
  have step : DomainResult.applyContinuous (denote t Environment.empty) (encodeData ha x) =
      g (encodeData ha x) := by
    rw [hg]
    rfl
  rw [step]
  apply Finite.DataShape.eq_encodeData_of_agrees hb
  intro w hw
  exact hfg _ _ (Finite.DataShape.agrees_native ha x) w ((hfx.trans hv.symm).trans hw)

/-- Native evaluation certifies a closed source function against a total native function. -/
@[expose] noncomputable def dataCertificate (ha : DataShape a) (hb : DataShape b)
    (t : Term [] (.arrow a.core b.core)) (g : a.Native → b.Native)
    (h : ∀ x, (t.denote native Env.empty).bind (fun f => f (ha.native x)) = hb.native (g x)) :
    DataCertificate ha hb where
  meaning := DomainResult.applyContinuous (denote t Environment.empty)
  implementation := g
  correct x := apply_data_of_native ha hb t (h x)

/-! The projection equations are for `rw`: simp indexes the implicit carrier types of
`CertifiedMeaning.meaning` without reducing them, so they would not match concrete goals. -/

theorem dataCertificate_meaning (ha : DataShape a) (hb : DataShape b)
    (t : Term [] (.arrow a.core b.core)) (g : a.Native → b.Native)
    (h : ∀ x, (t.denote native Env.empty).bind (fun f => f (ha.native x)) = hb.native (g x)) :
    (dataCertificate ha hb t g h).meaning =
      DomainResult.applyContinuous (denote t Environment.empty) := rfl

theorem dataCertificate_implementation (ha : DataShape a) (hb : DataShape b)
    (t : Term [] (.arrow a.core b.core)) (g : a.Native → b.Native)
    (h : ∀ x, (t.denote native Env.empty).bind (fun f => f (ha.native x)) = hb.native (g x)) :
    (dataCertificate ha hb t g h).implementation = g := rfl

end Resolved

/-- A finite description certifies its own compact source translation. -/
@[expose] noncomputable def Finite.Term.dataCertificate (ha : DataShape a) (hb : DataShape b)
    (f : Finite.Term [] (.arrow a b)) : DataCertificate ha hb where
  meaning := DomainResult.applyContinuous (Resolved.denote f.source Environment.empty)
  implementation := f.denote Finite.Env.empty
  correct x := by
    obtain ⟨fn, hf, hfn⟩ :=
      f.source_correct Finite.Env.empty Environment.empty Finite.envRepresents_empty
    change DomainResult.applyContinuous _ _ = _
    rw [hf, DomainResult.applyContinuous_value]
    exact Finite.Represents.eq_encodeData hb (hfn x _ (Finite.represents_encodeData ha x))

theorem Finite.Term.dataCertificate_meaning (ha : DataShape a) (hb : DataShape b)
    (f : Finite.Term [] (.arrow a b)) :
    (f.dataCertificate ha hb).meaning =
      DomainResult.applyContinuous (Resolved.denote f.source Environment.empty) := rfl

theorem Finite.Term.dataCertificate_implementation (ha : DataShape a)
    (hb : DataShape b) (f : Finite.Term [] (.arrow a b)) :
    (f.dataCertificate ha hb).implementation = f.denote Finite.Env.empty := rfl

end Cryptol
