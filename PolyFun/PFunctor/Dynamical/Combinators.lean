/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Basic

/-!
# Constructing dynamical systems from old ones

Niu–Spivak §4.3–4.4: dynamical systems are built up from smaller ones using the
monoidal and lens structure of `Poly`.

* `DynSystem.wrap` — change the interface along a lens `p ⟹ q` (a *wrapper*,
  §4.3.3), i.e. precomposition with the interface lens. Sections (§4.3.4) are the
  special case where the outer interface is `X`.
* `DynSystem.close` / `MooreMachine.feedback` — close a system off with a section
  `(a : p.A) → p.B a` (§4.3.4); for a Moore machine the section is a feedback map
  `O → I`, yielding an autonomous closed system.
* `DynSystem.tensor` — the *parallel product* (§4.3.2): juxtapose two systems;
  the states multiply and the interfaces tensor.
* `DynSystem.pairing` — the *categorical product* (§4.3.1): two interfaces driven
  by a shared state.
* `DynSystem.choiceProd` — asynchronous choice: juxtapose two systems on the
  product state, but expose the product interface `prod p q`, so each step
  advances exactly one side.
* `Wiring₂` / `DynSystem.wire₂` — a *wiring diagram* (§4.4) is a lens between the
  juxtaposed interfaces and an outer interface; installing systems into it is
  "tensor, then wrap".

Each combinator is given directly on the unpacked `expose` / `update` data (so it
is definitionally simple) and is related back to the corresponding `PFunctor.Lens`
combinator by a `*_toLens` lemma.
-/

@[expose] public section

universe u uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uO uI

namespace PFunctor

/-- The state polynomial of a product of state sets is the tensor of the state
polynomials: `selfMonomial (S × T) = selfMonomial S ⊗ selfMonomial T`. -/
theorem selfMonomial_prod (S : Type uA₁) (T : Type uA₂) :
    selfMonomial (S × T) = selfMonomial S ⊗ selfMonomial T := rfl

namespace DynSystem

/-! ## Wrappers (§4.3.3) and sections (§4.3.4) -/

variable {p : PFunctor.{uA₁, uB₁}} {q : PFunctor.{uA₂, uB₂}} {r : PFunctor.{uA₃, uB₃}}

/-- Change the interface of a system along a lens `w : p ⟹ q` (Niu–Spivak §4.3.3).
The new interface lens is `w` composed after the old one; see `wrap_toLens`. -/
def wrap (w : Lens p q) (s : DynSystem p) : DynSystem q where
  State := s.State
  expose := fun st => w.toFunA (s.expose st)
  update := fun st d => s.update st (w.toFunB (s.expose st) d)

@[simp] theorem wrap_toLens (w : Lens p q) (s : DynSystem p) :
    (wrap w s).toLens = w ∘ₗ s.toLens := rfl

@[simp] theorem wrap_id (s : DynSystem p) : wrap (Lens.id p) s = s := rfl

@[simp] theorem wrap_comp (w₂ : Lens q r) (w₁ : Lens p q) (s : DynSystem p) :
    wrap w₂ (wrap w₁ s) = wrap (w₂ ∘ₗ w₁) s := rfl

/-! ## Sections close systems (§4.3.4) -/

/-- Close a system off with a section `σ : (a : p.A) → p.B a` (Niu–Spivak §4.3.4):
wrap the interface along the section lens `p ⟹ X`, leaving a closed system whose
single available direction at each state is the one `σ` selects. -/
def close (σ : (a : p.A) → p.B a) (s : DynSystem p) : Closed := wrap (sectionLens σ) s

@[simp] theorem close_step (σ : (a : p.A) → p.B a) (s : DynSystem p) (st : s.State) :
    (close σ s).step st = s.update st (σ (s.expose st)) := rfl

@[simp] theorem close_toLens (σ : (a : p.A) → p.B a) (s : DynSystem p) :
    (close σ s).toLens = sectionLens σ ∘ₗ s.toLens := rfl

/-! ## Parallel product (§4.3.2) -/

/-- The **parallel product** of two systems (Niu–Spivak §4.3.2): the states
multiply and the interfaces tensor. -/
def tensor (s : DynSystem p) (t : DynSystem q) : DynSystem (p ⊗ q) where
  State := s.State × t.State
  expose := fun st => (s.expose st.1, t.expose st.2)
  update := fun st d => (s.update st.1 d.1, t.update st.2 d.2)

@[simp] theorem tensor_toLens (s : DynSystem p) (t : DynSystem q) :
    (s.tensor t).toLens = s.toLens ⊗ₗ t.toLens := rfl

/-! ## Categorical product (§4.3.1) -/

/-- The **categorical product** of two interfaces on a shared state (Niu–Spivak
§4.3.1): given two interface lenses out of the same state polynomial, expose both
interfaces at once, valued in the product `prod p q`. -/
def pairing {S : Type u} (l₁ : Lens (selfMonomial S) p) (l₂ : Lens (selfMonomial S) q) :
    DynSystem (prod p q) where
  State := S
  expose := fun s => (l₁.toFunA s, l₂.toFunA s)
  update := fun s => Sum.elim (l₁.toFunB s) (l₂.toFunB s)

@[simp] theorem pairing_toLens {S : Type u} (l₁ : Lens (selfMonomial S) p)
    (l₂ : Lens (selfMonomial S) q) : (pairing l₁ l₂).toLens = ⟨l₁, l₂⟩ₗ := rfl

/-! ## Asynchronous choice -/

/-- The **asynchronous choice** of two systems: the states multiply as in
`tensor`, but the interface is the product `prod p q`, whose directions at a
position choose a side, so each step advances exactly one component and leaves
the other frozen. Where `tensor` steps both systems in lockstep, `choiceProd`
interleaves them one step at a time; scheduled interleavings of processes are
wrappers of this combinator. -/
def choiceProd (s : DynSystem p) (t : DynSystem q) : DynSystem (prod p q) where
  State := s.State × t.State
  expose := fun st => (s.expose st.1, t.expose st.2)
  update := fun st =>
    Sum.elim (fun d => (s.update st.1 d, st.2)) (fun d => (st.1, t.update st.2 d))

/-! ## Wiring diagrams (§4.4) -/

/-- A **(binary) wiring diagram** with inner interfaces `p`, `q` and outer
interface `r` is a lens `p ⊗ q ⟹ r` (Niu–Spivak §4.4). -/
abbrev Wiring₂ (p : PFunctor.{uA₁, uB₁}) (q : PFunctor.{uA₂, uB₂}) (r : PFunctor.{uA₃, uB₃}) :
    Type _ := Lens (p ⊗ q) r

/-- Install two systems into a wiring diagram: juxtapose them with `tensor`, then
wrap along the diagram lens. -/
def wire₂ (w : Wiring₂ p q r) (s : DynSystem p) (t : DynSystem q) : DynSystem r :=
  wrap w (s.tensor t)

@[simp] theorem wire₂_toLens (w : Wiring₂ p q r) (s : DynSystem p) (t : DynSystem q) :
    (wire₂ w s t).toLens = w ∘ₗ (s.toLens ⊗ₗ t.toLens) := rfl

end DynSystem

/-! ## Feedback: closing a Moore machine on itself -/

namespace MooreMachine

variable {O : Type uO} {I : Type uI}

/-- Close a Moore machine into an autonomous (closed) system by feeding its output
back as its next input through `f : O → I` (Niu–Spivak §4.3.4). A section of the
Moore interface `O X^ I` is exactly such a function, so this is `DynSystem.close`.
The closed-loop state set is unchanged, so `m.output` still reads each state. -/
def feedback (f : O → I) (m : MooreMachine O I) : Closed := DynSystem.close f m

@[simp] theorem feedback_step (f : O → I) (m : MooreMachine O I) (st : m.State) :
    (feedback f m).step st = m.transition st (f (m.output st)) := rfl

end MooreMachine

end PFunctor
