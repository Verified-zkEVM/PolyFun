/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.Basic.Sampler
import all PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Control.Monad.Support
public import PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessSamplerEquiv

/-!
# Routed plugging over the possibilistic `SetM` monad

`OpenProcess.interleaveRouted` lets a composition deliver the packets one side
emits to the other side. This file exercises that hook with the smallest
communicating composition: an open process with a synchronous `deliver`
transition, closed against a context by routing every emitted packet across the
plug. Over the possibilistic `SetM` monad the resulting closed systems are no
longer shape-only:

* the real one-time pad and its ideal functionality are sampler-bisimilar at
  `MonadRelFamily.eq SetM` through the key bijection `k ↦ xor k b`;
* a fixed distinguishing context can reach both verdicts against `real` and
  against `ideal`;
* the same context can never reach the verdict `false` against a protocol
  that leaks its plaintext, by an invariant every scheduled step preserves.

The third fact is the canary: the structural `plug` of `openTheory` erases
packets, so no statement of this shape is available there. Everything here is
possibilistic; probability enters downstream.
-/

@[expose] public section

namespace PolyFunTest.Interaction.UC.RoutedPlugExamples

open _root_.Interaction
open _root_.Interaction.UC
open _root_.Interaction.Concurrent

/-! ## Boundaries and trees -/

/-- Two parties: the protocol (`0`) and the environment (`1`). -/
abbrev Party : Type := Fin 2

/-- The environment party. -/
def env : Party := 1

/-- A single port carrying one bit. -/
abbrev bitInterface : Interface := ⟨Unit, fun _ => Bool⟩

/-- The protocol boundary: plaintext bits come in, ciphertext bits go out. -/
abbrev Δ : PortBoundary := ⟨bitInterface, bitInterface⟩

/-- The one-packet trace carrying bit `b` on a single port. -/
def bitPacket (b : Bool) : PFunctor.TraceList bitInterface :=
  FreeMonoid.of ⟨(), b⟩

/-- A one-node tree choosing a bit. -/
abbrev bitTree : TypeTree.{0} := TypeTree.node Bool fun _ => TypeTree.done

/-- A one-node tree with a trivial move (an idle tick). -/
abbrev tickTree : TypeTree.{0} := TypeTree.node Unit fun _ => TypeTree.done

/-- A hidden internal node with the given emission. -/
def hiddenNode {Γ : PortBoundary} {X : Type} (emit : PFunctor.Trace Γ.Out X) :
    OpenNodeContext Party Γ X where
  controllers := fun _ => []
  views := fun _ => .hidden
  boundary := { isActivated := false, emit := emit }

/-- A node whose move the environment picks; no emission. -/
def envNode {Γ : PortBoundary} {X : Type} : OpenNodeContext Party Γ X where
  controllers := fun _ => [env]
  views := fun me => if me = env then .pick else .hidden
  boundary := { isActivated := false, emit := 1 }

/-! ## Reactive open processes -/

/-- A reactive open process: an open process plus an initial state and a
synchronous, pure input transition. -/
structure RProc (Γ : PortBoundary) where
  /-- Residual state space. -/
  Proc : Type
  /-- The step observed by the open world. -/
  step : Proc → OpenStep Party Γ Proc
  /-- Per-state possibilistic sampler. -/
  stepSampler : ∀ s, TypeTree.Sampler SetM (step s).tree
  /-- Initial state. -/
  init : Proc
  /-- Receive one packet on the input face. -/
  deliver : Proc → Interface.Packet Γ.In → Proc

namespace RProc

/-- Forget delivery and the initial state. -/
def toOpen {Γ : PortBoundary} (p : RProc Γ) : OpenProcess.{0, 0, 0, 0} SetM Party Γ :=
  ⟨p.Proc, p.step, p.stepSampler⟩

/-- Deliver a whole emitted trace, in emission order. -/
def deliverAll {Γ : PortBoundary} (p : RProc Γ) (t : PFunctor.TraceList Γ.In) (s : p.Proc) :
    p.Proc :=
  (FreeMonoid.toList t).foldl p.deliver s

/-- Run `n` scheduler-driven steps, collecting every reachable state. -/
def runSteps {Γ : PortBoundary} (q : RProc Γ) : ℕ → q.Proc → SetM q.Proc
  | 0, s => pure s
  | n + 1, s => do
      let tr ← TypeTree.samplePath (q.step s).tree (q.stepSampler s)
      q.runSteps n ((q.step s).next tr)

end RProc

/-- The possibilistic scheduler: both sides are always schedulable. -/
def allSched : SetM (ULift.{0, 0} Bool) := Set.univ

/-- The routed closure of a reactive process against a reactive context: the
scheduler picks a side, that side steps, and every packet it emits is delivered
to the other side in emission order. -/
def rplugOpen {Γ : PortBoundary} (p : RProc Γ) (k : RProc (PortBoundary.swap Γ)) :
    OpenProcess.{0, 0, 0, 0} SetM Party PortBoundary.empty :=
  p.toOpen.interleaveRouted k.toOpen
    (OpenNodeContext.close Party Γ) (OpenNodeContext.close Party (PortBoundary.swap Γ))
    (schedulerNode Party PortBoundary.empty) allSched
    (fun s₁ tr s₂ => k.deliverAll (OpenStep.boundaryTrace (p.step s₁) tr) s₂)
    (fun s₂ tr s₁ => p.deliverAll (OpenStep.boundaryTrace (k.step s₂) tr) s₁)

/-- The routed closure as a reactive process on the empty boundary. -/
def rplug {Γ : PortBoundary} (p : RProc Γ) (k : RProc (PortBoundary.swap Γ)) :
    RProc PortBoundary.empty where
  Proc := (rplugOpen p k).Proc
  step := (rplugOpen p k).step
  stepSampler := (rplugOpen p k).stepSampler
  init := (p.init, k.init)
  deliver := fun s _ => s

/-! ## The protocols -/

/-- Idle step: a hidden tick, no emission, state unchanged. -/
def idleStep {Γ : PortBoundary} {P : Type} (s : P) : OpenStep Party Γ P where
  tree := tickTree
  semantics := ⟨hiddenNode 1, fun _ => ⟨⟩⟩
  next := fun _ => s

/-- The plaintext-receiving transition shared by all three protocols. -/
def receive : Option Bool → Interface.Packet Δ.In → Option Bool
  | none, pk => some pk.2
  | some b, _ => some b

/-- Real one-time pad: once a plaintext `b` is delivered, sample a key `k`
and emit `xor k b`. -/
def realStep : Option Bool → OpenStep Party Δ (Option Bool)
  | none => idleStep none
  | some b =>
    { tree := bitTree
      semantics := ⟨hiddenNode fun k => bitPacket (xor k b), fun _ => ⟨⟩⟩
      next := fun _ => none }

/-- Ideal functionality: emit a fresh bit unrelated to the plaintext. -/
def idealStep : Option Bool → OpenStep Party Δ (Option Bool)
  | none => idleStep none
  | some _ =>
    { tree := bitTree
      semantics := ⟨hiddenNode fun c => bitPacket c, fun _ => ⟨⟩⟩
      next := fun _ => none }

/-- Insecure protocol: emit the plaintext itself. -/
def leakyStep : Option Bool → OpenStep Party Δ (Option Bool)
  | none => idleStep none
  | some b =>
    { tree := tickTree
      semantics := ⟨hiddenNode fun _ => bitPacket b, fun _ => ⟨⟩⟩
      next := fun _ => none }

/-- The uniform bit sampler. -/
def anyBit : SetM Bool := Set.univ

/-- The trivial tick sampler. -/
def tick : SetM Unit := pure ()

/-- Sampler for `realStep`: every key is possible. -/
def realSampler : ∀ s, TypeTree.Sampler SetM (realStep s).tree
  | none => ⟨tick, fun _ => ⟨⟩⟩
  | some _ => ⟨anyBit, fun _ => ⟨⟩⟩

/-- Sampler for `idealStep`: every ciphertext is possible. -/
def idealSampler : ∀ s, TypeTree.Sampler SetM (idealStep s).tree
  | none => ⟨tick, fun _ => ⟨⟩⟩
  | some _ => ⟨anyBit, fun _ => ⟨⟩⟩

/-- Sampler for `leakyStep`: nothing is sampled. -/
def leakySampler : ∀ s, TypeTree.Sampler SetM (leakyStep s).tree
  | none => ⟨tick, fun _ => ⟨⟩⟩
  | some _ => ⟨tick, fun _ => ⟨⟩⟩

/-- The real one-time pad as a reactive process. -/
def real : RProc Δ := ⟨Option Bool, realStep, realSampler, none, receive⟩

/-- The ideal functionality as a reactive process. -/
def ideal : RProc Δ := ⟨Option Bool, idealStep, idealSampler, none, receive⟩

/-- The leaky protocol as a reactive process. -/
def leaky : RProc Δ := ⟨Option Bool, leakyStep, leakySampler, none, receive⟩

/-! ## The distinguisher -/

/-- Phases of the distinguishing context. -/
inductive KState where
  /-- About to send the plaintext `true`. -/
  | start
  /-- Waiting for a ciphertext. -/
  | wait
  /-- Received ciphertext `c`. -/
  | got (c : Bool)
  /-- Announced the verdict `c == true`. -/
  | halt (verdict : Bool)

/-- The distinguisher's steps: send `true`, wait, announce whether the
received ciphertext equals the plaintext. -/
def kStep : KState → OpenStep Party (PortBoundary.swap Δ) KState
  | .start =>
    { tree := tickTree
      semantics := ⟨hiddenNode fun _ => bitPacket true, fun _ => ⟨⟩⟩
      next := fun _ => .wait }
  | .wait => idleStep .wait
  | .got _ =>
    { tree := bitTree
      semantics := ⟨envNode, fun _ => ⟨⟩⟩
      next := fun tr => .halt tr.1 }
  | .halt v => idleStep (.halt v)

/-- The distinguisher's sampler: its only choice is the verdict, which is
determined by the received ciphertext. -/
def kSampler : ∀ s, TypeTree.Sampler SetM (kStep s).tree
  | .start => ⟨tick, fun _ => ⟨⟩⟩
  | .wait => ⟨tick, fun _ => ⟨⟩⟩
  | .got c => ⟨(pure (c == true) : SetM Bool), fun _ => ⟨⟩⟩
  | .halt _ => ⟨tick, fun _ => ⟨⟩⟩

/-- Receiving a ciphertext while waiting records it. -/
def kDeliver : KState → Interface.Packet (PortBoundary.swap Δ).In → KState
  | .wait, pk => .got pk.2
  | s, _ => s

/-- The distinguishing context. -/
def distinguisher : RProc (PortBoundary.swap Δ) := ⟨KState, kStep, kSampler, .start, kDeliver⟩

/-- The verdict recorded by a halted distinguisher. -/
def verdictOf : KState → Option Bool
  | .halt v => some v
  | _ => none

/-- Every verdict the distinguisher can reach against `p` within three steps. -/
def verdicts (p : RProc Δ) : SetM (Option Bool) :=
  (fun st => verdictOf st.2) <$> (rplug p distinguisher).runSteps 3 (rplug p distinguisher).init

/-! ## Membership lemmas for the `SetM` monad -/

theorem mem_bind {α β : Type} {s : SetM α} {f : α → SetM β} {b : β} :
    b ∈ SetM.run (s >>= f) ↔ ∃ a ∈ SetM.run s, b ∈ SetM.run (f a) := by
  change b ∈ ⋃ a ∈ SetM.run s, SetM.run (f a) ↔ _
  constructor
  · intro h
    obtain ⟨a, ha, hb⟩ := Set.mem_iUnion₂.1 h
    exact ⟨a, ha, hb⟩
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.2 ⟨a, ha, hb⟩

theorem mem_pure {α : Type} {a b : α} : b ∈ SetM.run (pure a : SetM α) ↔ b = a :=
  Set.mem_singleton_iff

theorem mem_map {α β : Type} {s : SetM α} {g : α → β} {b : β} :
    b ∈ SetM.run (g <$> s) ↔ ∃ a ∈ SetM.run s, g a = b := by
  change b ∈ g '' SetM.run s ↔ _
  exact Set.mem_image _ _ _

theorem mem_univ' {α : Type} (a : α) : a ∈ SetM.run (Set.univ : SetM α) := Set.mem_univ a

/-- Membership in a sampled path of a node: the head move is in the head
sampler and the tail is a sampled path of the chosen subtree. -/
theorem mem_samplePath_node {X : Type} {rest : X → TypeTree.{0}} (samp : SetM X)
    (sampRest : ∀ x, TypeTree.Sampler SetM (rest x)) (x : X) (tr : TypeTree.Path (rest x)) :
    (⟨x, tr⟩ : TypeTree.Path (TypeTree.node X rest)) ∈
        SetM.run (TypeTree.samplePath (TypeTree.node X rest) ⟨samp, sampRest⟩) ↔
      x ∈ SetM.run samp ∧ tr ∈ SetM.run (TypeTree.samplePath (rest x) (sampRest x)) := by
  rw [TypeTree.samplePath_node]
  constructor
  · intro h
    obtain ⟨x', hx', h⟩ := mem_bind.1 h
    obtain ⟨tr', htr', h⟩ := mem_bind.1 h
    obtain ⟨rfl, htr⟩ := Sigma.mk.inj_iff.1 (mem_pure.1 h)
    rw [eq_of_heq htr]
    exact ⟨hx', htr'⟩
  · rintro ⟨hx, htr⟩
    exact mem_bind.2 ⟨x, hx, mem_bind.2 ⟨tr, htr, mem_pure.2 rfl⟩⟩

/-- The unique path of a completed tree is always sampled. -/
theorem mem_samplePath_done (sampler : TypeTree.Sampler SetM (TypeTree.done : TypeTree.{0}))
    (tr : TypeTree.Path (TypeTree.done : TypeTree.{0})) :
    tr ∈ SetM.run (TypeTree.samplePath (TypeTree.done : TypeTree.{0}) sampler) := by
  rw [TypeTree.samplePath_done]
  exact mem_pure.2 rfl

theorem mem_runSteps_zero {Γ : PortBoundary} (q : RProc Γ) (s s' : q.Proc) :
    s' ∈ SetM.run (q.runSteps 0 s) ↔ s' = s :=
  mem_pure

theorem mem_runSteps_succ {Γ : PortBoundary} (q : RProc Γ) (n : ℕ) (s s' : q.Proc) :
    s' ∈ SetM.run (q.runSteps (n + 1) s) ↔
      ∃ tr ∈ SetM.run (TypeTree.samplePath (q.step s).tree (q.stepSampler s)),
        s' ∈ SetM.run (q.runSteps n ((q.step s).next tr)) := by
  rw [RProc.runSteps]
  exact mem_bind

end PolyFunTest.Interaction.UC.RoutedPlugExamples

end

/-! The claims below unfold non-exposed library definitions (`boundaryTrace`,
`IsSilentStep`, `interleaveRouted`'s underlying process), so they live outside
the public section. -/

namespace PolyFunTest.Interaction.UC.RoutedPlugExamples

open _root_.Interaction
open _root_.Interaction.UC
open _root_.Interaction.Concurrent

/-! ## Claim A: `real` and `ideal` are sampler-bisimilar at exact equality -/

/-- The key-shift bijection on the paths of `bitTree`. -/
def keyEquiv (b : Bool) : TypeTree.Path bitTree ≃ TypeTree.Path bitTree where
  toFun tr := ⟨xor tr.1 b, ⟨⟩⟩
  invFun tr := ⟨xor tr.1 b, ⟨⟩⟩
  left_inv := by
    rintro ⟨k, ⟨⟩⟩
    cases k <;> cases b <;> rfl
  right_inv := by
    rintro ⟨k, ⟨⟩⟩
    cases k <;> cases b <;> rfl

/-- Sampling a bit from `anyBit` reaches every path of `bitTree`. -/
theorem samplePath_bit_eq_univ :
    TypeTree.samplePath bitTree ⟨anyBit, fun _ => ⟨⟩⟩ =
      (Set.univ : SetM (TypeTree.Path bitTree)) := by
  apply Set.eq_univ_of_forall
  rintro ⟨k, ⟨⟩⟩
  exact (mem_samplePath_node _ _ _ _).2 ⟨mem_univ' _, mem_samplePath_done _ _⟩

/-- The real one-time pad and the ideal functionality are sampler-bisimilar at
exact `SetM` equality: the simulator is absorbed into the key bijection. -/
theorem real_ideal_bisim :
    IsSamplerBisimulation (MonadRelFamily.eq SetM) real.toOpen ideal.toOpen Eq := by
  constructor
  rintro s _ rfl
  cases s with
  | none =>
    refine ⟨Equiv.refl _, fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl, ?_⟩
    refine (MonadRelFamily.eq_rel _ _).2 ?_
    exact id_map' _
  | some b =>
    refine ⟨keyEquiv b, ?_, ?_, ?_, ?_⟩
    · rintro ⟨k, ⟨⟩⟩
      exact Iff.rfl
    · rintro ⟨k, ⟨⟩⟩
      rfl
    · rintro ⟨k, ⟨⟩⟩
      rfl
    · refine (MonadRelFamily.eq_rel _ _).2 ?_
      change (fun tr => keyEquiv b tr) <$> TypeTree.samplePath bitTree ⟨anyBit, fun _ => ⟨⟩⟩ =
        TypeTree.samplePath bitTree ⟨anyBit, fun _ => ⟨⟩⟩
      rw [samplePath_bit_eq_univ]
      change (fun tr => keyEquiv b tr) '' Set.univ = Set.univ
      exact Set.image_univ_of_surjective (keyEquiv b).surjective

/-! ## Claim B: the distinguisher reaches both verdicts against `ideal` and `real` -/

theorem verdict_mem_ideal (c : Bool) : some (c == true) ∈ SetM.run (verdicts ideal) := by
  refine mem_map.2 ⟨(none, KState.halt (c == true)), ?_, rfl⟩
  change (none, KState.halt (c == true)) ∈
    SetM.run ((rplug ideal distinguisher).runSteps 3 (none, KState.start))
  refine (mem_runSteps_succ _ _ _ _).2 ⟨⟨⟨false⟩, ⟨(), ⟨⟩⟩⟩, ?_, ?_⟩
  · exact (mem_samplePath_node _ _ _ _).2
      ⟨mem_univ' _, (mem_samplePath_node _ _ _ _).2 ⟨mem_pure.2 rfl, mem_samplePath_done _ _⟩⟩
  change (none, KState.halt (c == true)) ∈
    SetM.run ((rplug ideal distinguisher).runSteps 2 (some true, KState.wait))
  refine (mem_runSteps_succ _ _ _ _).2 ⟨⟨⟨true⟩, ⟨c, ⟨⟩⟩⟩, ?_, ?_⟩
  · exact (mem_samplePath_node _ _ _ _).2
      ⟨mem_univ' _, (mem_samplePath_node _ _ _ _).2 ⟨mem_univ' _, mem_samplePath_done _ _⟩⟩
  change (none, KState.halt (c == true)) ∈
    SetM.run ((rplug ideal distinguisher).runSteps 1 (none, KState.got c))
  refine (mem_runSteps_succ _ _ _ _).2 ⟨⟨⟨false⟩, ⟨c == true, ⟨⟩⟩⟩, ?_, ?_⟩
  · exact (mem_samplePath_node _ _ _ _).2
      ⟨mem_univ' _, (mem_samplePath_node _ _ _ _).2 ⟨mem_pure.2 rfl, mem_samplePath_done _ _⟩⟩
  change (none, KState.halt (c == true)) ∈
    SetM.run ((rplug ideal distinguisher).runSteps 0 (none, KState.halt (c == true)))
  exact (mem_runSteps_zero _ _ _).2 rfl

theorem some_true_mem_verdicts_ideal : some true ∈ SetM.run (verdicts ideal) :=
  verdict_mem_ideal true

theorem some_false_mem_verdicts_ideal : some false ∈ SetM.run (verdicts ideal) :=
  verdict_mem_ideal false

/-- Against the real one-time pad, key `k` yields ciphertext `xor k true`. -/
theorem verdict_mem_real (k : Bool) :
    some (xor k true == true) ∈ SetM.run (verdicts real) := by
  refine mem_map.2 ⟨(none, KState.halt (xor k true == true)), ?_, rfl⟩
  change (none, KState.halt (xor k true == true)) ∈
    SetM.run ((rplug real distinguisher).runSteps 3 (none, KState.start))
  refine (mem_runSteps_succ _ _ _ _).2 ⟨⟨⟨false⟩, ⟨(), ⟨⟩⟩⟩, ?_, ?_⟩
  · exact (mem_samplePath_node _ _ _ _).2
      ⟨mem_univ' _, (mem_samplePath_node _ _ _ _).2 ⟨mem_pure.2 rfl, mem_samplePath_done _ _⟩⟩
  change (none, KState.halt (xor k true == true)) ∈
    SetM.run ((rplug real distinguisher).runSteps 2 (some true, KState.wait))
  refine (mem_runSteps_succ _ _ _ _).2 ⟨⟨⟨true⟩, ⟨k, ⟨⟩⟩⟩, ?_, ?_⟩
  · exact (mem_samplePath_node _ _ _ _).2
      ⟨mem_univ' _, (mem_samplePath_node _ _ _ _).2 ⟨mem_univ' _, mem_samplePath_done _ _⟩⟩
  change (none, KState.halt (xor k true == true)) ∈
    SetM.run ((rplug real distinguisher).runSteps 1 (none, KState.got (xor k true)))
  refine (mem_runSteps_succ _ _ _ _).2 ⟨⟨⟨false⟩, ⟨xor k true == true, ⟨⟩⟩⟩, ?_, ?_⟩
  · exact (mem_samplePath_node _ _ _ _).2
      ⟨mem_univ' _, (mem_samplePath_node _ _ _ _).2 ⟨mem_pure.2 rfl, mem_samplePath_done _ _⟩⟩
  change (none, KState.halt (xor k true == true)) ∈
    SetM.run ((rplug real distinguisher).runSteps 0 (none, KState.halt (xor k true == true)))
  exact (mem_runSteps_zero _ _ _).2 rfl

theorem some_true_mem_verdicts_real : some true ∈ SetM.run (verdicts real) :=
  verdict_mem_real false

theorem some_false_mem_verdicts_real : some false ∈ SetM.run (verdicts real) :=
  verdict_mem_real true

/-! ## Claim C: against `leaky`, the verdict `false` is unreachable -/

/-- Invariant: the only plaintext in flight is `true`, so the distinguisher only
ever receives, and announces, `true`. -/
def LeakyInv (st : Option Bool × KState) : Prop :=
  (∀ b, st.1 = some b → b = true) ∧ (∀ c, st.2 = KState.got c → c = true) ∧
    (∀ v, st.2 = KState.halt v → v = true)

theorem leakyInv_step (st : Option Bool × KState) (h : LeakyInv st)
    (tr : TypeTree.Path ((rplug leaky distinguisher).step st).tree)
    (htr : tr ∈ SetM.run
      (TypeTree.samplePath _ ((rplug leaky distinguisher).stepSampler st))) :
    LeakyInv (((rplug leaky distinguisher).step st).next tr) := by
  obtain ⟨s₁, s₂⟩ := st
  obtain ⟨h₁, h₂, h₃⟩ := h
  rcases tr with ⟨⟨side⟩, tr⟩
  cases side
  · -- the distinguisher moves
    cases s₂ with
    | start =>
      rcases tr with ⟨⟨⟩, ⟨⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        cases s₁ with
        | none => exact (Option.some.inj hb).symm
        | some b' =>
          have hb' : b' = b := Option.some.inj hb
          exact hb' ▸ h₁ b' rfl
      · intro c hc
        cases hc
      · intro v hv
        cases hv
    | wait =>
      rcases tr with ⟨⟨⟩, ⟨⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · exact h₁
      · intro c hc
        cases hc
      · intro v hv
        cases hv
    | got c =>
      rcases tr with ⟨v, ⟨⟩⟩
      have hv : v = (c == true) :=
        mem_pure.1 ((mem_samplePath_node _ _ _ _).1 ((mem_samplePath_node _ _ _ _).1 htr).2).1
      refine ⟨?_, ?_, ?_⟩
      · exact h₁
      · intro c' hc
        cases hc
      · intro v' hv'
        have hvv : v = v' := KState.halt.inj hv'
        rw [← hvv, hv, h₂ c rfl]
        rfl
    | halt v =>
      rcases tr with ⟨⟨⟩, ⟨⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · exact h₁
      · intro c hc
        cases hc
      · intro v' hv'
        exact h₃ v' hv'
  · -- the leaky protocol moves
    cases s₁ with
    | none =>
      rcases tr with ⟨⟨⟩, ⟨⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        cases hb
      · exact h₂
      · exact h₃
    | some b =>
      rcases tr with ⟨⟨⟩, ⟨⟩⟩
      have hb : b = true := h₁ b rfl
      subst hb
      refine ⟨?_, ?_, ?_⟩
      · intro b' hb'
        cases hb'
      · intro c hc
        cases s₂ with
        | start => cases hc
        | wait => exact (KState.got.inj hc).symm
        | got c' =>
          have hcc : c' = c := KState.got.inj hc
          exact hcc ▸ h₂ c' rfl
        | halt v => cases hc
      · intro v hv
        cases s₂ with
        | start => cases hv
        | wait => cases hv
        | got c' => cases hv
        | halt v' =>
          have hvv : v' = v := KState.halt.inj hv
          exact hvv ▸ h₃ v' rfl

theorem leakyInv_runSteps :
    ∀ (n : ℕ) (st : Option Bool × KState), LeakyInv st →
      ∀ st' ∈ SetM.run ((rplug leaky distinguisher).runSteps n st), LeakyInv st'
  | 0, st, h, st', hst' => by
    rw [(mem_runSteps_zero _ _ _).1 hst']
    exact h
  | n + 1, st, h, st', hst' => by
    obtain ⟨tr, htr, hst'⟩ := (mem_runSteps_succ _ _ _ _).1 hst'
    exact leakyInv_runSteps n _ (leakyInv_step st h tr htr) st' hst'

/-- The initial state satisfies the invariant vacuously. -/
theorem leakyInv_init : LeakyInv (none, KState.start) :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩

/-- No scheduling and no sampling lets the distinguisher announce `false`
against the leaky protocol: the environment's verdict depends on what the
protocol sent it. -/
theorem some_false_not_mem_verdicts_leaky : some false ∉ SetM.run (verdicts leaky) := by
  intro hmem
  obtain ⟨⟨s₁, s₂⟩, hst, hv⟩ := mem_map.1 hmem
  obtain ⟨_, _, h₃⟩ := leakyInv_runSteps 3 (none, KState.start) leakyInv_init _ hst
  cases s₂ with
  | halt v =>
    have hv' : v = false := Option.some.inj hv
    have := h₃ v rfl
    rw [hv'] at this
    cases this
  | start => cases hv
  | wait => cases hv
  | got c => cases hv

end PolyFunTest.Interaction.UC.RoutedPlugExamples
