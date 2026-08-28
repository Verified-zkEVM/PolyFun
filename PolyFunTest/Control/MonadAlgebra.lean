/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Algebra

/-!
# Coverage of the ordered monad algebra transformer lifts

`MAlgOrdered` deliberately has no globally registered base instance: the structure map
`μ : m l → l` is a *choice* of semantics, not something a monad determines. On `FreeM P`
the choice is a per-operation spec (`PFunctor.OpSpec.toMAlgOrdered` takes the spec and its
monotonicity proof as arguments), and on a supported monad it is the demonic or angelic
reading. So there is nothing canonical to register.

What the library does register are the transformer *lifts*. This file is their coverage
check: with a single base algebra installed locally, every lift resolves by synthesis, and
the lifts stack. That is the intended usage pattern — install the intended algebra at the
verification boundary and let the transformers compose above it.
-/

@[expose] public section

namespace PolyFunTest.MonadAlgebraCoverage

open MAlgOrdered

/-- The base choice. Everything below is synthesized above this one local instance. -/
noncomputable local instance instIdProp : MAlgOrdered Id Prop where
  μ x := x
  μ_pure _ := rfl
  μ_bind_mono _ _ h x := h x

section Coverage

variable {σ ρ ε ω : Type} [Monoid ω]

noncomputable example : MAlgOrdered (StateT σ Id) (σ → Prop) := inferInstance
noncomputable example : MAlgOrdered (ReaderT ρ Id) (ρ → Prop) := inferInstance
noncomputable example : MAlgOrdered (ExceptT ε Id) Prop := inferInstance
noncomputable example : MAlgOrdered (OptionT Id) Prop := inferInstance
noncomputable example : MAlgOrdered (WriterT ω Id) (ω → Prop) := inferInstance

/-! The lifts stack, which is what makes the "install one base" pattern worth having. -/

noncomputable example : MAlgOrdered (StateT σ (OptionT Id)) (σ → Prop) := inferInstance
noncomputable example : MAlgOrdered (ReaderT ρ (ExceptT ε Id)) (ρ → Prop) := inferInstance
noncomputable example : MAlgOrdered (StateT σ (WriterT ω Id)) (σ → ω → Prop) := inferInstance

end Coverage

section Behaviour

/-- `tell` shifts the log the postcondition is shown: this is the content of indexing the
carrier by `ω`, and the analogue of `StateT`'s postcondition seeing the final state. -/
example (ω : Type) [Monoid ω] (w₀ : ω) (post : PUnit → ω → Prop) :
    wp (MonadWriter.tell w₀ : WriterT ω Id PUnit) post = fun w => post ⟨⟩ (w * w₀) :=
  by simp only [wp, bind_pure_comp]; funext w; rfl

end Behaviour

end PolyFunTest.MonadAlgebraCoverage
