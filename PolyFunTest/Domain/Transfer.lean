/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Result

/-!
# Transfer along decoders whose fibres are up-sets

Above a returned value lie only values above it, and above an error only that error. Over a
discrete type, a value has only itself above it, so reading a discrete result back decodes above
the values.

`decodePair` reads a pair of discrete results back as a pair of numbers. It decodes above
`encodePair`: a pair decodes to `(a, b)` exactly when it lies above the pair of values `⟨a⟩` and
`⟨b⟩`. So decoding is stable upward, and a monotone map, here `Prod.swap`, acts on every pair that
decodes to `(a, b)` as it acts on the encoding of `(a, b)`.
-/

public section

namespace PolyFunTest.DomainTransfer

/-- Results over natural numbers in their usual order. -/
abbrev Res := DomainResult String ℕ

/-- Results over discrete natural numbers. -/
abbrev Disc := DomainResult String (DiscreteOrder ℕ)

/-! ## What lies above a value or an error -/

/-- Above a value lie larger values, in the order of `ℕ`. -/
example : (DomainResult.value 2 : Res) ≤ .value 5 :=
  DomainResult.value_le_iff.mpr ⟨5, rfl, by decide⟩

/-- Neither bottom nor an error lies above a value. -/
example : ¬(DomainResult.value 2 : Res) ≤ ⊥ ∧ ¬(DomainResult.value 2 : Res) ≤ .error "e" :=
  ⟨fun h => by
    obtain ⟨_, h, _⟩ := DomainResult.value_le_iff.mp h
    exact DomainResult.value_ne_bot _ h.symm,
   fun h => by
    obtain ⟨_, h, _⟩ := DomainResult.value_le_iff.mp h
    exact DomainResult.value_ne_error _ _ h.symm⟩

/-- An error has only itself above it. -/
example {r : Res} (h : DomainResult.error "e" ≤ r) : r = .error "e" :=
  DomainResult.error_le_iff.mp h

/-- Over a discrete type, a value has only itself above it. -/
example {r : Disc} (h : DomainResult.value ⟨2⟩ ≤ r) : r = .value ⟨2⟩ :=
  DomainResult.value_le_iff_eq.mp h

/-! ## Inversion -/

example {d : Res} (h : DomainResult.map (· + 1) d = .value 3) : d = .value 2 := by
  obtain ⟨x, rfl, hx⟩ := DomainResult.map_eq_value_iff.mp h
  rw [show x = 2 by omega]

example {d : Res} {f : ℕ → Res} (h : DomainResult.bindPlain d f = .value 3) :
    ∃ x, d = .value x ∧ f x = .value 3 :=
  DomainResult.bindPlain_eq_value_iff.mp h

/-! ## A decoder of pairs -/

/-- Read a pair of discrete results back as a pair of numbers, the first component first. -/
def decodePair (p : Disc × Disc) : DomainResult String (ℕ × ℕ) :=
  DomainResult.bindPlain (DomainResult.map DiscreteOrder.value p.1) fun a =>
    DomainResult.map (fun b => (a, b)) (DomainResult.map DiscreteOrder.value p.2)

/-- A pair of numbers as a pair of values. -/
def encodePair (x : ℕ × ℕ) : Disc × Disc :=
  (.value ⟨x.1⟩, .value ⟨x.2⟩)

/-- A pair decodes to `(a, b)` exactly when it lies above the encoding of `(a, b)`. -/
theorem decodesAbove_pair : DomainResult.DecodesAbove encodePair decodePair := by
  intro p x
  rw [decodePair, DomainResult.bindPlain_eq_value_iff, Prod.le_def]
  constructor
  · rintro ⟨a, ha, hab⟩
    obtain ⟨b, hb, rfl⟩ := DomainResult.map_eq_value_iff.mp hab
    exact ⟨DomainResult.map_value_eq_value_iff.mp ha, DomainResult.map_value_eq_value_iff.mp hb⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨x.1, DomainResult.map_value_eq_value_iff.mpr h₁, by
      rw [DomainResult.map_value_eq_value_iff.mpr h₂, DomainResult.map_value]⟩

/-- The decoder reads an encoding back. -/
example : decodePair (encodePair (2, 3)) = .value (2, 3) :=
  decodesAbove_pair.dec_enc (2, 3)

/-- A pair with a bottom component lies below an encoding, and decodes to no value. -/
example : ((⊥, .value ⟨3⟩) : Disc × Disc) ≤ encodePair (2, 3) ∧
    decodePair (⊥, .value ⟨3⟩) = ⊥ :=
  ⟨Prod.le_def.mpr ⟨bot_le, le_rfl⟩, rfl⟩

/-- Swapping a pair that decodes to `(a, b)` gives a pair that decodes to `(b, a)`: by transfer
from the encoding, where it holds by computation. -/
example {p : Disc × Disc} {a b : ℕ} (hp : decodePair p = .value (a, b)) :
    decodePair p.swap = .value (b, a) :=
  decodesAbove_pair.dec_apply_eq_of_monotone decodesAbove_pair (F := Prod.swap)
    (fun _ _ h => Prod.le_def.mpr ⟨h.2, h.1⟩) rfl hp

/-- The discrete decoder decodes above the values. -/
example {d d' : Disc} (hle : d ≤ d')
    (hd : DomainResult.map DiscreteOrder.value d = .value 4) :
    DomainResult.map DiscreteOrder.value d' = .value 4 :=
  DomainResult.decodesAbove_map_value.dec_eq_of_le hle hd

end PolyFunTest.DomainTransfer
