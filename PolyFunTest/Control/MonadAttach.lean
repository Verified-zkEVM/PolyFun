/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Support
public import PolyFun.Control.Monad.Support.Indexed

/-!
# Examples for exact monadic support and the always/never judgments

These examples pin the definitional-transfer contract of the support layer: the satisfaction
judgments must stay `Iff.rfl`-convertible both to their bounded-quantifier spellings and to
`MonadAttach.CanReturn`, so downstream support-based statements transfer without rewriting.
They also exercise the scoped `⊨ₐ` / `⊨ₛ` / `⊭` notation, the structural recursion of the
judgments over free-monad trees, and `MonadAttach.pbind`.

The stateful section is the executable justification for the canonical `MonadAttach`
instances of `StateT` and `ReaderT` not being `ExactMonadAttach`: flattening their initial
indices makes the bind introduction rule genuinely fail.
-/

@[expose] public section

universe u v uA uB

open MonadAttach
open scoped MonadAttach

section DefinitionalTransfer

variable {m : Type u → Type v} [MonadAttach m] {α : Type u} (p : α → Prop) (x : m α)

/-- `AllOutputs` is definitionally the bounded universal quantifier. -/
example : (x ⊨ₐ p) ↔ ∀ a ∈ support x, p a := Iff.rfl

/-- `SomeOutput` is definitionally the bounded existential quantifier. -/
example : (x ⊨ₛ p) ↔ ∃ a ∈ support x, p a := Iff.rfl

/-- `NoOutput` is definitionally the negated bounded quantifier. -/
example : (x ⊭ p) ↔ ∀ a ∈ support x, ¬ p a := Iff.rfl

/-- Membership in the support is `CanReturn`, definitionally. -/
example (a : α) : a ∈ support x ↔ CanReturn x a := Iff.rfl

/-- The "always" judgment is definitionally a quantifier over `CanReturn`. -/
example : (x ⊨ₐ p) ↔ ∀ a, CanReturn x a → p a := Iff.rfl

end DefinitionalTransfer

section Judgments

/-- A two-direction query interface: one position, boolean responses. -/
abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

open PFunctor in
/-- Flip one coin and return it. -/
def flipCoin : FreeM coinP Bool := FreeM.lift (P := coinP) PUnit.unit

open PFunctor in
/-- Flip two coins and return their conjunction. -/
def flipTwo : FreeM coinP Bool := do
  let a ← flipCoin
  let b ← flipCoin
  pure (a && b)

/-- Every outcome of a coin flip is a boolean tautology's witness. -/
example : flipCoin ⊨ₐ fun b => b = true ∨ b = false := by
  intro b _
  cases b <;> simp

/-- Some outcome of `flipTwo` is `true`, witnessed by two `true` flips. -/
example : flipTwo ⊨ₛ fun b => b = true := by
  rw [someOutput_iff_exists_support]
  refine ⟨true, ?_, rfl⟩
  rw [show flipTwo = flipCoin >>= (fun a => flipCoin >>= fun b => pure (a && b)) from rfl,
    mem_support_bind]
  have hcoin : (true : Bool) ∈ support flipCoin := by
    rw [flipCoin, PFunctor.FreeM.support_lift]
    exact Set.mem_univ true
  refine ⟨true, hcoin, ?_⟩
  rw [mem_support_bind]
  exact ⟨true, hcoin, by simp⟩

/-- No outcome of `flipTwo` lies outside `Bool`'s two values. -/
example : flipTwo ⊭ fun b => b ≠ true ∧ b ≠ false := by
  intro b _ hb
  cases b <;> simp_all

/-- `attach` is computable on free programs, so `pbind` can carry reachability proofs into
the continuation. -/
example : PFunctor.FreeM coinP {b : Bool // CanReturn flipCoin b} :=
  MonadAttach.attach flipCoin

/-- `pbind` gives the continuation a proof that its input was reachable. -/
example : PFunctor.FreeM coinP Bool :=
  MonadAttach.pbind flipCoin fun b (_ : CanReturn flipCoin b) => pure (!b)

/-- Both responses of the Boolean query are reachable; this rejects support
implementations that silently select one branch. -/
example : true ∈ support flipCoin ∧ false ∈ support flipCoin := by
  constructor <;> rw [flipCoin, PFunctor.FreeM.support_lift] <;> trivial

/-- A false output of the answer-dependent two-query continuation is
reachable (for example, choose `true` and then `false`). -/
example : false ∈ support flipTwo := by
  rw [show flipTwo = flipCoin >>= (fun a => flipCoin >>= fun b => pure (a && b)) from rfl,
    mem_support_bind]
  refine ⟨true, ?_, ?_⟩
  · rw [flipCoin, PFunctor.FreeM.support_lift]
    trivial
  · rw [mem_support_bind]
    refine ⟨false, ?_, by simp⟩
    rw [flipCoin, PFunctor.FreeM.support_lift]
    trivial

/-- `attachSupp` preserves a branch-dependent tree after erasing the attached
reachability proofs. -/
example : Subtype.val <$> PFunctor.FreeM.attachSupp flipTwo = flipTwo :=
  PFunctor.FreeM.map_attachSupp flipTwo

end Judgments

section BaseSupports

/-- Failed optional computations have empty support. -/
example : support (none : Option Bool) = ∅ := by
  ext b
  simp [support, CanReturn]

/-- Exceptions likewise have empty support. -/
example : support (.error () : Except Unit Bool) = ∅ := by
  ext b
  simp [support, CanReturn]

/-- `SetM` support preserves every member rather than selecting one. -/
def bothBools : SetM Bool := fun _ => True

example : support bothBools = Set.univ :=
  rfl

/-- `OptionT` success and failure bind paths retain their intended supports. -/
def optionSuccess : OptionT Id Bool := some true
def optionFailure : OptionT Id Bool := none

example : support (optionSuccess >>= fun b => pure (!b)) = {false} := by
  change {b | some false = some b} = {false}
  ext b
  simp

example : support (optionFailure >>= fun b => pure (!b)) = ∅ := by
  change {b | (none : Option Bool) = some b} = ∅
  ext b
  simp

/-- `ExceptT` success and failure bind paths retain their intended supports. -/
def exceptSuccess : ExceptT Unit Id Bool := .ok true
def exceptFailure : ExceptT Unit Id Bool := .error ()

example : support (exceptSuccess >>= fun b => pure (!b)) = {false} := by
  change {b | Except.ok false = Except.ok b} = {false}
  ext b
  simp

example : support (exceptFailure >>= fun b => pure (!b)) = ∅ := by
  change {b | (Except.error () : Except Unit Bool) = Except.ok b} = ∅
  ext b
  simp

end BaseSupports

section StatefulCounterexamples

/-! `StateT σ m` has a canonical `MonadAttach` instance — the union over initial states — so
`support` is defined and the elimination theory applies. It is not `ExactMonadAttach`: both
introduction rules fail, as the two examples below witness. Reason per run instead. -/

/-- Possible outputs do *not* compose along `bind` for `StateT`: the continuation may
observe a state the prefix never produced. -/
example : ¬ (∀ {α β : Type} {x : StateT Bool Id α} {f : α → StateT Bool Id β} {a : α}
      {b : β}, CanReturn x a → CanReturn (f a) b → CanReturn (x >>= f) b) := by
  intro h
  have hx : CanReturn (m := StateT Bool Id) (fun _ => ((), true)) () := ⟨false, true, rfl⟩
  have hf : CanReturn (m := StateT Bool Id) (fun s => (s, s)) false := ⟨false, false, rfl⟩
  obtain ⟨s, s', hs⟩ := h (x := fun _ => ((), true)) (f := fun _ => fun s => (s, s)) hx hf
  simp only [CanReturn, Id.run] at hs
  exact Bool.noConfusion (congrArg Prod.fst hs)

/-- Even the `pure` introduction rule fails when the state type is empty: there is no
initial state to run from. -/
example (a : Nat) : ¬ CanReturn (m := StateT Empty Id) (pure a) a := by
  rintro ⟨s, -, -⟩
  exact s.elim

/-- The usable form: state facts about a `StateT` computation per run. -/
example {m : Type → Type v} [Monad m] [MonadAttach m] {σ α : Type} (x : StateT σ m α)
    (a : α) : a ∈ support x ↔ ∃ s s', (a, s') ∈ support (x.run s) :=
  mem_support_stateT_iff

/-! ### The indexed form repairs both failures

The two failures above are failures of *flattening*, not of `StateT`: `CanReturn` picks an
initial state existentially and picks it independently on each side of a `bind`. Indexing by
the initial state removes that freedom, and both introduction rules come back. -/

/-- The introduction rule the flattened support lacks. `StateT.supportFrom_bind` is an
equation, so in particular the ⊇ direction holds: an outcome of the prefix followed by an
outcome of the continuation *from the state the prefix produced* is an outcome of the bind.
The flattened `canReturn_bind` above is exactly this with the two states decoupled. -/
example {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    {σ α β : Type} (s : σ) (x : StateT σ m α) (f : α → StateT σ m β)
    {a : α} {s' : σ} {b : β} {s'' : σ}
    (h : (a, s') ∈ StateT.supportFrom s x)
    (h' : (b, s'') ∈ StateT.supportFrom s' (f a)) :
    (b, s'') ∈ StateT.supportFrom s (x >>= f) := by
  rw [StateT.supportFrom_bind]
  exact Set.mem_biUnion h h'

/-- On the very data that refutes `canReturn_bind`, the indexed law gives the right answer:
the continuation is run only from `true`, the state the prefix actually produces, so the
disagreeing value is not reachable. -/
example : ((false, false) : Bool × Bool) ∉
    StateT.supportFrom (m := Id) (σ := Bool) true (fun s => (s, s)) := fun h =>
  Bool.noConfusion (congrArg Prod.fst (h : ((true, true) : Bool × Bool) = (false, false)))

/-- The `pure` rule also comes back: there is no initial state to quantify over, because the
initial state is an argument. Compare the `StateT Empty Id` failure above. -/
example {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    {σ α : Type} (s : σ) (a : α) :
    StateT.supportFrom s (pure a : StateT σ m α) = {(a, s)} :=
  StateT.supportFrom_pure s a

/-! ### `ReaderT` fails for the same reason

The flattened premises may choose different environments. The bind below has no `true`
output: at `false` the prefix selects the `false` branch of the continuation, while at
`true` it selects the `true` branch. Yet `false` is reachable from the prefix at one
environment and `true` is reachable from its continuation at the other. Indexing fixes
this by threading the same environment through both sides. -/

/-- Possible outputs do not compose for flattened `ReaderT` support, even over a nonempty
environment. -/
example : ¬ (∀ {α β : Type} {x : ReaderT Bool Id α} {f : α → ReaderT Bool Id β}
      {a : α} {b : β}, CanReturn x a → CanReturn (f a) b → CanReturn (x >>= f) b) := by
  intro h
  have hx : CanReturn (m := ReaderT Bool Id) (fun r => r) false := ⟨false, rfl⟩
  have hf : CanReturn (m := ReaderT Bool Id) (fun r => !false && r) true := ⟨true, rfl⟩
  obtain ⟨r, hr⟩ := h (x := fun r => r) (f := fun a r => !a && r) hx hf
  cases r
  · change (!false && false = true) at hr
    contradiction
  · change (!true && true = true) at hr
    contradiction

/-- `pure` has empty support over an empty environment: there is no environment to run in. -/
example (a : Nat) : ¬ CanReturn (m := ReaderT Empty Id) (pure a) a := by
  rintro ⟨r, -⟩
  exact r.elim

/-- Indexed by the environment, `pure` behaves. -/
example {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    {ρ α : Type} (r : ρ) (a : α) :
    ReaderT.supportAt r (pure a : ReaderT ρ m α) = {a} :=
  ReaderT.supportAt_pure r a

/-! ### Why `ExactMonadAttach` has to exist

`LawfulMonadAttach` bounds the support from one side only: every core law is an implication
*out of* `CanReturn`, so a uniformly-`False` predicate satisfies all of them vacuously. The
model below is the one the `ExactMonadAttach` docstring appeals to. Its mirror image is
`MonadAttach.trivial`, whose `CanReturn` is uniformly `True` and which core itself documents
as having no `LawfulMonadAttach` instance — so the two classes exclude the two degenerate
models from opposite sides. -/

/-- The constantly-`PUnit` monad, whose every law holds by `PUnit` eta. -/
private def PUnitM (_ : Type) : Type := PUnit

private instance : Monad PUnitM where
  pure _ := PUnit.unit
  bind _ _ := PUnit.unit

private instance : LawfulMonad PUnitM :=
  LawfulMonad.mk' _ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- `CanReturn` uniformly `False` — no value is ever a possible output. -/
private instance : MonadAttach PUnitM where
  CanReturn _ _ := False
  attach _ := PUnit.unit

/-- And it is *lawful*: both fields are discharged without saying anything about outputs.
This is why the introduction rules cannot be derived and must be assumed. -/
private instance : LawfulMonadAttach PUnitM where
  map_attach := rfl
  canReturn_map_imp h := h.elim

/-- The support of every computation in that model is empty, including `pure`. So
`LawfulMonadAttach` alone does not pin the support: `ExactMonadAttach.canReturn_pure` is
exactly what rules this out. -/
example (a : Nat) : support (pure a : PUnitM Nat) = ∅ := rfl

example (a : Nat) : ¬ CanReturn (pure a : PUnitM Nat) a := id

end StatefulCounterexamples

section AutomationBattery

/-! A compact living gate for the automation contract in `Control/Monad/Support.lean`.
Each distinct normalization path is closed by one terminal tactic; testing every goal
twice with both tactics would add volume without distinguishing regressions. -/

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

-- Membership normalizes to `CanReturn`, then to a concrete equation.
example (a b : Nat) : a ∈ support (pure b : Option Nat) ↔ a = b := by simp

-- The directed closed-form rule is also available to `grind`.
example (a : Nat) : support (some a) = {a} := by grind

example : support (none : Option Nat) = ∅ := by simp

-- Set-level structure decomposes before pointwise unfolding.
example (x : m Nat) (f : Nat → m Bool) :
    support (x >>= f) = ⋃ a ∈ support x, support (f a) := by simp

example (g : Nat → Bool) (x : m Nat) : support (g <$> x) = g '' support x := by simp

-- The indexed layer computes too.
example {σ : Type} (s : σ) (a : Nat) :
    StateT.supportFrom s (pure a : StateT σ m Nat) = {(a, s)} := by simp

-- The writer layer, which had no support at all before.
example {ω : Type} [Monoid ω] (a : Nat) (w : ω) (x : WriterT ω m Nat)
    (h : (a, w) ∈ support x.run) : a ∈ support x := by grind [mem_support_writerT_iff]

/-! The support-quantifier characterizations are deliberately kept out of `grind`'s
default set, so a naive `grind` on a support goal fails fast rather than saturating.
They remain available by explicit opt-in. -/

example (p : Nat → Prop) (x : m Nat) (h : ∀ a ∈ support x, p a) : AllOutputs p x := by
  grind [allOutputs_iff_forall_support]

example (p : Nat → Prop) (x : m Nat) (h : SomeOutput p x) : ¬ NoOutput p x := by
  grind [not_noOutput_iff]

end AutomationBattery

section TrivialTriple

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
variable {α : Type}

/-- The "always" judgment is the trivial-precondition `Prop`-valued triple. -/
example (x : m α) (p : α → Prop) :
    letI := mAlgOrderedPropDemonic (m := m)
    MAlgOrdered.Triple (l := Prop) ⊤ x p ↔ (x ⊨ₐ p) :=
  triple_top_iff_allOutputs x p

end TrivialTriple

section AlgebraSelection

/-- A computation used to distinguish transformer failure semantics from
support-based partial-correctness semantics. -/
def noResult : OptionT Id Nat := none

section TransformerDefault

local instance : MAlgOrdered Id Prop := mAlgOrderedPropDemonic

/-- Installing the support algebra only on the base monad leaves PolyFun's
existing `OptionT` algebra in charge, so `none` is failure (`⊥`). -/
example : ¬ MAlgOrdered.wp noResult (fun _ => True) := by
  change ¬ MAlgOrdered.wpOpt noResult (fun _ => True) False
  intro hw
  have hEq :=
    MAlgOrdered.wpOpt_fail (m := Id) (l := Prop) (α := Nat) (fun _ => True) False
  have hw' : MAlgOrdered.wpOpt (OptionT.mk (pure none) : OptionT Id Nat)
      (fun _ => True) False := by
    exact hw
  exact hEq.mp hw'

end TransformerDefault

/-- Installing support semantics explicitly on the transformer instead makes
its empty support satisfy every postcondition vacuously. -/
example :
    letI := mAlgOrderedPropDemonic (m := OptionT Id)
    MAlgOrdered.wp noResult (fun _ => True) := by
  rw [wp_iff_allOutputs]
  exact fun _ _ => trivial

end AlgebraSelection

section AngelicNotConjunctive

/-! ### Why there is no angelic `Std.Do.WP`

`Std.Do.PredTrans` carries conjunctivity as a *structure field*, and as a bi-entailment:
`t (Q₁ ∧ₚ Q₂) ⊣⊢ₛ t Q₁ ∧ t Q₂`. The demonic reading satisfies it in both directions, which
is what lets `MonadAttach.toWP` build a `PredTrans` at all. The angelic reading satisfies
only `→`: two *different* outputs may witness the two conjuncts separately, so nothing
forces a single output to satisfy both.

The consequence is structural rather than a gap in this development. The angelic
interpretation cannot be a `Std.Do.WP`, so it stays at the `MAlgOrdered` level, whose
`μ_bind_mono` asks only for monotonicity. Core's newer weakest-precondition stack drops
conjunctivity from `PredTrans` and reintroduces it as an opt-in `WPConjunctive`.
That optional class asks for exactly the direction refuted below; the angelic reading
is expressible against the newer base `WP` only without such an instance. -/

/-- The direction that does hold: an angelic conjunction splits. -/
example {α : Type} (x : SetM α) (p q : α → Prop) (h : x ⊨ₛ fun a => p a ∧ q a) :
    (x ⊨ₛ p) ∧ (x ⊨ₛ q) := by
  obtain ⟨a, hcan, hp, hq⟩ := h
  exact ⟨⟨a, hcan, hp⟩, ⟨a, hcan, hq⟩⟩

/-- The direction that fails, and with it conjunctivity of the angelic transformer.
Witness: `{0, 1}` has an output equal to `0` and an output equal to `1`, but none equal
to both. -/
example : ¬ (∀ {α : Type} (x : SetM α) (p q : α → Prop),
    (x ⊨ₛ p) → (x ⊨ₛ q) → (x ⊨ₛ fun a => p a ∧ q a)) := by
  intro h
  obtain ⟨a, -, ha0, ha1⟩ :=
    h (({0, 1} : Set ℕ) : SetM ℕ) (· = 0) (· = 1)
      ⟨0, Or.inl rfl, rfl⟩ ⟨1, Or.inr rfl, rfl⟩
  omega

/-- The demonic reading, by contrast, distributes in both directions — this is the
`conjunctiveRaw` field that `MonadAttach.toWP` discharges. -/
example {α : Type} (x : SetM α) (p q : α → Prop) :
    (x ⊨ₐ fun a => p a ∧ q a) ↔ (x ⊨ₐ p) ∧ (x ⊨ₐ q) :=
  allOutputs_and p q x

end AngelicNotConjunctive
