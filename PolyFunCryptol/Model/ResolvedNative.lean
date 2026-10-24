/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.Native
public import PolyFunCryptol.Model.SequenceLaws

/-!
# Native evaluation of resolved terms

`Resolved.native` interprets resolved syntax in native values. Fixed points, errors
and unsupported primitives have no answer. `native_related` checks the native
interpretation against the lazy algebra one constructor at a time, and the generic
fundamental lemma lifts it to every term: whatever native evaluation returns, the lazy
meaning represents (`denote_agrees`). A closed word function that evaluates natively
therefore certifies its lazy meaning on every input (`word_function`), with no proof
about the lazy semantics.
-/

public section

open OmegaCompletePartialOrder IPFunctor IPFunctor.ScopedSignature

namespace Cryptol.Resolved

/-- Native evaluation of each constructor. -/
@[expose] def native : Interpretation syntaxSignature Native.Result
  | _, .sequence _, k => some fun i => k i Env.empty
  | _, .primitive p, _ => Native.primitive p
  | _, .bit b, _ => some b
  | _, .integer i, _ => some i
  | _, .unit, _ => some ()
  | _, .error _, _ => none
  | _, .lam, k => some fun v => k 0 (Env.cons (V := Native.Result) v Env.empty)
  | _, .app, k => (k 0 Env.empty).bind fun f => f (k 1 Env.empty)
  | _, .letE, k => k 1 (Env.cons (V := Native.Result) (k 0 Env.empty) Env.empty)
  | _, .pair, k => some (k 0 Env.empty, k 1 Env.empty)
  | _, .fst, k => (k 0 Env.empty).bind Prod.fst
  | _, .snd, k => (k 0 Env.empty).bind Prod.snd
  | _, .generate _, k => some fun i =>
      k 0 (Env.cons (V := Native.Result) (some (Length.indexNat i : Int)) Env.empty)
  | _, @Op.index _ l, k => (k 0 Env.empty).bind fun xs =>
      (k 1 Env.empty).bind fun i => (l.checkIndex i).bind xs
  | _, .ite, k => (k 0 Env.empty).bind fun b : Bool => if b then k 1 Env.empty else k 2 Env.empty
  | _, .fix, _ => none
  | _, .bitNot, k => (k 0 Env.empty).map fun b : Bool => !b
  | _, .bitOp op, k => (k 0 Env.empty).bind fun a : Bool =>
      (k 1 Env.empty).map fun b : Bool => op.eval a b
  | _, .intOp op, k => (k 0 Env.empty).bind fun a : Int =>
      (k 1 Env.empty).bind fun b : Int => (op.eval a b).toOption
  | _, .intEq, k => (k 0 Env.empty).bind fun a : Int =>
      (k 1 Env.empty).map fun b : Int => a == b
  | _, .intLt, k => (k 0 Env.empty).bind fun a : Int =>
      (k 1 Env.empty).map fun b : Int => decide (a < b)

theorem envRelated_empty :
    EnvRelated Native.Agrees (Environment.empty : Environment [])
      (Env.empty (V := Native.Result)) :=
  fun _ x => nomatch x

theorem envRelated_single {a : ClosedTy} {e : Computation a} {v : Native.Result a}
    (h : Native.Agrees a e v) :
    EnvRelated Native.Agrees (Environment.cons e Environment.empty : Environment [a])
      (Env.cons (V := Native.Result) v Env.empty) := by
  intro b x
  cases x with
  | zero => exact h
  | succ x => exact nomatch x

theorem agrees_value_of_ofExcept {α : Type} {f : Except EvalError α} {x : α}
    (h : f.toOption = some x) : ofExcept f = DomainResult.value ⟨x⟩ := by
  cases f with
  | error e => exact nomatch h
  | ok y => cases h; rfl

/-- The only constructor-local proof: each constructor preserves agreement. -/
theorem native_related : DomainInterpretation.Related Native.Agrees algebra native := by
  intro a op k k' hk
  cases op with
  | sequence n =>
      rintro _ ⟨⟩
      exact ⟨_, rfl, fun i x hx => hk i _ _ envRelated_empty x hx⟩
  | primitive p => exact Native.primitive_agrees p
  | bit b => rintro _ ⟨⟩; rfl
  | integer i => rintro _ ⟨⟩; rfl
  | unit => rintro _ ⟨⟩; rfl
  | error e => exact Native.agrees_none _ _
  | lam =>
      rintro _ ⟨⟩
      exact ⟨_, rfl, fun e v hv y hy => hk 0 _ _ (envRelated_single hv) y hy⟩
  | app =>
      intro y hy
      obtain ⟨f, hf, hy⟩ := Option.bind_eq_some_iff.mp hy
      obtain ⟨g, hg, hfg⟩ := hk 0 _ _ envRelated_empty f hf
      have step : DomainResult.applyContinuous (k 0 Environment.empty) (k 1 Environment.empty) =
          g (k 1 Environment.empty) := by
        rw [hg]
        rfl
      change Native.Represents _ (DomainResult.applyContinuous (k 0 _) (k 1 _)) y
      rw [step]
      exact hfg _ _ (hk 1 _ _ envRelated_empty) y hy
  | letE => exact hk 1 _ _ (envRelated_single (hk 0 _ _ envRelated_empty))
  | pair =>
      rintro _ ⟨⟩
      exact ⟨_, _, rfl, hk 0 _ _ envRelated_empty, hk 1 _ _ envRelated_empty⟩
  | fst =>
      intro v hv
      obtain ⟨p, hp, hv⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨x, y, hxy, h1, _⟩ := hk 0 _ _ envRelated_empty p hp
      have step : DomainResult.bind (.ofFun Prod.fst) (k 0 Environment.empty) = x := by
        rw [hxy]
        rfl
      change Native.Represents _ (DomainResult.bind _ (k 0 _)) v
      rw [step]
      exact h1 v hv
  | snd =>
      intro v hv
      obtain ⟨p, hp, hv⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨x, y, hxy, _, h2⟩ := hk 0 _ _ envRelated_empty p hp
      have step : DomainResult.bind (.ofFun Prod.snd) (k 0 Environment.empty) = y := by
        rw [hxy]
        rfl
      change Native.Represents _ (DomainResult.bind _ (k 0 _)) v
      rw [step]
      exact h2 v hv
  | generate l =>
      rintro _ ⟨⟩
      exact ⟨_, rfl, fun i x hx =>
        hk 0 _ _ (envRelated_single (fun _ h => by cases h; rfl)) x hx⟩
  | @index _ len =>
      intro x hx
      obtain ⟨xs, hxs, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨i, hi, hx⟩ := Option.bind_eq_some_iff.mp hx
      change ℤ at i
      obtain ⟨j, hj, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨ds, hds, hdsx⟩ := hk 0 _ _ envRelated_empty xs hxs
      have hk1 : k 1 Environment.empty = DomainResult.value ⟨i⟩ := hk 1 _ _ envRelated_empty i hi
      have values : Semantics.index (l := len) (a := a) (DomainResult.value ds)
          (DomainResult.value ⟨i⟩) = ds j := by
        rw [Semantics.index_values, hj]
      have step : Semantics.index (k 0 Environment.empty) (k 1 Environment.empty) = ds j := by
        rw [hds, hk1]
        exact values
      change Native.Represents _ (Semantics.index (k 0 _) (k 1 _)) x
      rw [step]
      exact hdsx j x hx
  | ite =>
      intro x hx
      obtain ⟨b, hb, hx⟩ := Option.bind_eq_some_iff.mp hx
      change Bool at b
      have hk0 : k 0 Environment.empty = DomainResult.value ⟨b⟩ :=
        hk 0 _ _ envRelated_empty b hb
      have step : Semantics.conditional (k 1 Environment.empty, k 2 Environment.empty)
          (k 0 Environment.empty) = if b then k 1 Environment.empty else k 2 Environment.empty := by
        rw [hk0]
        exact Semantics.conditional_value _ _ b
      change Native.Represents _ (Semantics.conditional (k 1 _, k 2 _) (k 0 _)) x
      rw [step]
      cases b
      · exact hk 2 _ _ envRelated_empty x hx
      · exact hk 1 _ _ envRelated_empty x hx
  | fix => exact Native.agrees_none _ _
  | bitNot =>
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hx
      have hk0 : k 0 Environment.empty = DomainResult.value ⟨b⟩ :=
        hk 0 _ _ envRelated_empty b hb
      change Semantics.bitNot (k 0 _) = _
      rw [hk0]
      rfl
  | bitOp op =>
      intro x hx
      obtain ⟨u, hu, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hx
      change Semantics.binary _ (k 0 _) (k 1 _) = _
      rw [show k 0 Environment.empty = DomainResult.value ⟨u⟩ from hk 0 _ _ envRelated_empty u hu,
        show k 1 Environment.empty = DomainResult.value ⟨w⟩ from hk 1 _ _ envRelated_empty w hw]
      rfl
  | intOp op =>
      intro x hx
      obtain ⟨u, hu, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨w, hw, hx⟩ := Option.bind_eq_some_iff.mp hx
      change Semantics.binary _ (k 0 _) (k 1 _) = _
      rw [show k 0 Environment.empty = DomainResult.value ⟨u⟩ from hk 0 _ _ envRelated_empty u hu,
        show k 1 Environment.empty = DomainResult.value ⟨w⟩ from hk 1 _ _ envRelated_empty w hw,
        Semantics.binary_values]
      exact agrees_value_of_ofExcept hx
  | intEq =>
      intro x hx
      obtain ⟨u, hu, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hx
      change Semantics.binary _ (k 0 _) (k 1 _) = _
      rw [show k 0 Environment.empty = DomainResult.value ⟨u⟩ from hk 0 _ _ envRelated_empty u hu,
        show k 1 Environment.empty = DomainResult.value ⟨w⟩ from hk 1 _ _ envRelated_empty w hw]
      rfl
  | intLt =>
      intro x hx
      obtain ⟨u, hu, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hx
      change Semantics.binary _ (k 0 _) (k 1 _) = _
      rw [show k 0 Environment.empty = DomainResult.value ⟨u⟩ from hk 0 _ _ envRelated_empty u hu,
        show k 1 Environment.empty = DomainResult.value ⟨w⟩ from hk 1 _ _ envRelated_empty w hw]
      rfl

/-! ## Native evaluation equations -/

section Equations

variable {Γ : List ClosedTy} {a b : ClosedTy} (ρ : Env Native.Result Γ)

@[simp] theorem native_var (v : Var Γ a) : (Term.var v).denote native ρ = ρ v := rfl

@[simp] theorem native_bit (x : Bool) : (Term.bit x : Term Γ .bit).denote native ρ = some x := rfl

@[simp] theorem native_integer (i : Int) :
    (Term.integer i : Term Γ .integer).denote native ρ = some i := rfl

@[simp] theorem native_primitive (p : Primitive a) :
    (Term.primitive p : Term Γ a).denote native ρ = Native.primitive p := rfl

@[simp] theorem native_lam (body : Term (a :: Γ) b) :
    (Term.lam body).denote native ρ =
      some fun v => body.denote native (Env.cons (V := Native.Result) v ρ) := rfl

@[simp] theorem native_app (f : Term Γ (.arrow a b)) (x : Term Γ a) :
    (Term.app f x).denote native ρ =
      (f.denote native ρ).bind fun g => g (x.denote native ρ) := rfl

@[simp] theorem native_wordLogic {n : Nat} (op : BitOp) (x y : Term Γ (wordTy n)) :
    (Term.wordLogic op x y).denote native ρ =
      Native.wordLogic op (x.denote native ρ) (y.denote native ρ) := rfl

@[simp] theorem native_shift {n : Nat} (op : ShiftOp) (x : Term Γ (wordTy n))
    (k : Term Γ .integer) :
    (Term.shift op x k).denote native ρ =
      Native.shift op (x.denote native ρ) (k.denote native ρ) := rfl

end Equations

/-- Whatever native evaluation of a closed term returns, its lazy meaning represents. -/
theorem denote_agrees {a : ClosedTy} (t : Term [] a) :
    Native.Agrees a (denote t Environment.empty) (t.denote native Env.empty) :=
  Term.denoteDomain_related native_related t envRelated_empty

/-- A closed word function that evaluates natively certifies its lazy meaning at an input. -/
theorem word_function {n m : Nat} (t : Term [] (.arrow (wordTy n) (wordTy m)))
    {f : Native.Value (.arrow (wordTy n) (wordTy m))}
    (hf : t.denote native Env.empty = some f) {x : BitVec n} {y : BitVec m}
    (hy : f (Native.wordResult x) = Native.wordResult y) :
    DomainResult.applyContinuous (denote t Environment.empty) (.value (wordValue x)) =
      .value (wordValue y) := by
  obtain ⟨g, hg, hfg⟩ := denote_agrees t f hf
  have hx : Native.Agrees (wordTy n) (.value (wordValue x)) (some (Native.word x)) :=
    fun _ h => by cases h; exact Native.represents_word x
  have step : DomainResult.applyContinuous (denote t Environment.empty) (.value (wordValue x)) =
      g (.value (wordValue x)) := by
    rw [hg]
    rfl
  rw [step]
  exact Native.eq_wordValue_of_bits? (hfg _ _ hx _ hy) (Native.bits?_word y)

/-- An imported word function's body that evaluates natively certifies its meaning. -/
theorem word_function_lam {n m : Nat} (body : Term [wordTy n] (wordTy m)) {x : BitVec n}
    {y : BitVec m}
    (hy : body.denote native (Env.cons (Native.wordResult x) Env.empty) =
      Native.wordResult y) :
    DomainResult.applyContinuous (denote (Term.lam body) Environment.empty)
      (.value (wordValue x)) = .value (wordValue y) :=
  word_function (Term.lam body) rfl hy

end Cryptol.Resolved
