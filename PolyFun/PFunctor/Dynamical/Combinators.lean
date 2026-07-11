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
monoidal and lens structure of `Poly`. Since a dynamical system *is* a lens out
of its self monomial, every combinator here is literally a `PFunctor.Lens`
construction — wrapping is diagrammatic composition, juxtaposition is `⊗ₗ`, the
categorical product is the lens pairing — and the dynamical `expose` / `update`
readings are recorded as derived `@[simp]` equations.

* `DynSystem.wrap` — change the interface along a lens `p ⟹ q` (a *wrapper*,
  §4.3.3): literally `s ⨟ w`. Sections (§4.3.4) are the special case where the
  outer interface is `X`.
* `DynSystem.close` / `MooreMachine.feedback` — close a system off with a section
  `(a : p.A) → p.B a` (§4.3.4); for a Moore machine the section is a feedback map
  `O → I`, yielding an autonomous closed system.
* `DynSystem.tensor` — the *parallel product* (§4.3.2): juxtapose two systems;
  literally `s ⊗ₗ t` (the states multiply and the interfaces tensor).
* `DynSystem.pairing` — the *categorical product* (§4.3.1): two interfaces driven
  by a shared state; literally the lens pairing `⟨l₁, l₂⟩ₗ`.
* `DynSystem.choiceProd` — asynchronous choice: juxtapose two systems on the
  product state, but expose the product interface `prod p q`, so each step
  advances exactly one side.
* `Wiring₂` / `DynSystem.wire₂` — a *wiring diagram* (§4.4) is a lens between the
  juxtaposed interfaces and an outer interface; installing systems into it is
  "tensor, then wrap": `(s ⊗ₗ t) ⨟ w`.
-/

@[expose] public section

universe u v uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uO uI

namespace PFunctor

/-- The state polynomial of a product of state sets is the tensor of the state
polynomials: `selfMonomial (S × T) = selfMonomial S ⊗ selfMonomial T`. -/
theorem selfMonomial_prod (S : Type uA₁) (T : Type uA₂) :
    selfMonomial (S × T) = selfMonomial S ⊗ selfMonomial T := rfl

namespace DynSystem

/-! ## Wrappers (§4.3.3) and sections (§4.3.4) -/

variable {S : Type u} {T : Type v}
variable {p : PFunctor.{uA₁, uB₁}} {q : PFunctor.{uA₂, uB₂}} {r : PFunctor.{uA₃, uB₃}}

/-- Change the interface of a system along a lens `w : p ⟹ q` (Niu–Spivak
§4.3.3): the *wrapper* is literally diagrammatic lens composition `s ⨟ w`. -/
def wrap (w : Lens p q) (s : DynSystem S p) : DynSystem S q := s ⨟ w

@[simp] theorem wrap_expose (w : Lens p q) (s : DynSystem S p) (st : S) :
    (wrap w s).expose st = w.toFunA (s.expose st) := rfl

@[simp] theorem wrap_update (w : Lens p q) (s : DynSystem S p) (st : S)
    (d : q.B ((wrap w s).expose st)) :
    (wrap w s).update st d = s.update st (w.toFunB (s.expose st) d) := rfl

theorem wrap_eq_comp (w : Lens p q) (s : DynSystem S p) : wrap w s = w ∘ₗ s := rfl

@[simp] theorem wrap_id (s : DynSystem S p) : wrap (Lens.id p) s = s := rfl

@[simp] theorem wrap_comp (w₂ : Lens q r) (w₁ : Lens p q) (s : DynSystem S p) :
    wrap w₂ (wrap w₁ s) = wrap (w₂ ∘ₗ w₁) s := rfl

/-! ## Sections close systems (§4.3.4) -/

/-- Close a system off with a section `σ : (a : p.A) → p.B a` (Niu–Spivak §4.3.4):
wrap the interface along the section lens `p ⟹ X`, leaving a closed system whose
single available direction at each state is the one `σ` selects. -/
def close (σ : (a : p.A) → p.B a) (s : DynSystem S p) : Closed S :=
  wrap (sectionLens σ) s

@[simp] theorem close_step (σ : (a : p.A) → p.B a) (s : DynSystem S p) (st : S) :
    (close σ s).step st = s.update st (σ (s.expose st)) := rfl

theorem close_eq_comp (σ : (a : p.A) → p.B a) (s : DynSystem S p) :
    close σ s = s ⨟ sectionLens σ := rfl

/-! ## Parallel product (§4.3.2) -/

/-- The **parallel product** of two systems (Niu–Spivak §4.3.2): the states
multiply and the interfaces tensor — literally the lens tensor `s ⊗ₗ t`, since
`selfMonomial (S × T) = selfMonomial S ⊗ selfMonomial T`. -/
def tensor (s : DynSystem S p) (t : DynSystem T q) : DynSystem (S × T) (p ⊗ q) :=
  s ⊗ₗ t

@[simp] theorem tensor_expose (s : DynSystem S p) (t : DynSystem T q) (st : S × T) :
    (s.tensor t).expose st = (s.expose st.1, t.expose st.2) := rfl

@[simp] theorem tensor_update (s : DynSystem S p) (t : DynSystem T q) (st : S × T)
    (d : (p ⊗ q).B ((s.tensor t).expose st)) :
    (s.tensor t).update st d = (s.update st.1 d.1, t.update st.2 d.2) := rfl

theorem tensor_eq_tensorMap (s : DynSystem S p) (t : DynSystem T q) :
    s.tensor t = s ⊗ₗ t := rfl

/-! ## Categorical product (§4.3.1) -/

/-- The **categorical product** of two interfaces on a shared state (Niu–Spivak
§4.3.1): given two interface lenses out of the same state polynomial, expose both
interfaces at once, valued in the product `prod p q` — literally the lens pairing
`⟨l₁, l₂⟩ₗ`. -/
def pairing (l₁ : DynSystem S p) (l₂ : DynSystem S q) : DynSystem S (prod p q) :=
  ⟨l₁, l₂⟩ₗ

@[simp] theorem pairing_expose (l₁ : DynSystem S p) (l₂ : DynSystem S q) (st : S) :
    (pairing l₁ l₂).expose st = (l₁.expose st, l₂.expose st) := rfl

@[simp] theorem pairing_update (l₁ : DynSystem S p) (l₂ : DynSystem S q) (st : S)
    (d : (prod p q).B ((pairing l₁ l₂).expose st)) :
    (pairing l₁ l₂).update st d = Sum.elim (l₁.update st) (l₂.update st) d := rfl

/-! ## Asynchronous choice -/

/-- The **asynchronous choice** of two systems: the states multiply as in
`tensor`, but the interface is the product `prod p q`, whose directions at a
position choose a side, so each step advances exactly one component and leaves
the other frozen. Where `tensor` steps both systems in lockstep, `choiceProd`
interleaves them one step at a time; scheduled interleavings of processes are
wrappers of this combinator. -/
def choiceProd (s : DynSystem S p) (t : DynSystem T q) :
    DynSystem (S × T) (prod p q) :=
  (fun st => (s.expose st.1, t.expose st.2)) ⇆ fun st =>
    Sum.elim (fun d => (s.update st.1 d, st.2)) (fun d => (st.1, t.update st.2 d))

@[simp] theorem choiceProd_expose (s : DynSystem S p) (t : DynSystem T q) (st : S × T) :
    (s.choiceProd t).expose st = (s.expose st.1, t.expose st.2) := rfl

@[simp] theorem choiceProd_update (s : DynSystem S p) (t : DynSystem T q) (st : S × T)
    (d : (prod p q).B ((s.choiceProd t).expose st)) :
    (s.choiceProd t).update st d =
      Sum.elim (fun d => (s.update st.1 d, st.2)) (fun d => (st.1, t.update st.2 d)) d := rfl

/-! ## Wiring diagrams (§4.4) -/

/-- A **(binary) wiring diagram** with inner interfaces `p`, `q` and outer
interface `r` is a lens `p ⊗ q ⟹ r` (Niu–Spivak §4.4). -/
abbrev Wiring₂ (p : PFunctor.{uA₁, uB₁}) (q : PFunctor.{uA₂, uB₂}) (r : PFunctor.{uA₃, uB₃}) :
    Type _ := Lens (p ⊗ q) r

/-- Install two systems into a wiring diagram: juxtapose them with `tensor`, then
wrap along the diagram lens — literally `(s ⊗ₗ t) ⨟ w`. -/
def wire₂ (w : Wiring₂ p q r) (s : DynSystem S p) (t : DynSystem T q) :
    DynSystem (S × T) r :=
  wrap w (s.tensor t)

theorem wire₂_eq_comp (w : Wiring₂ p q r) (s : DynSystem S p) (t : DynSystem T q) :
    wire₂ w s t = (s ⊗ₗ t) ⨟ w := rfl

end DynSystem

/-! ## Feedback: closing a Moore machine on itself -/

namespace MooreMachine

variable {S : Type u} {O : Type uO} {I : Type uI}

/-- Close a Moore machine into an autonomous (closed) system by feeding its output
back as its next input through `f : O → I` (Niu–Spivak §4.3.4). A section of the
Moore interface `O X^ I` is exactly such a function, so this is `DynSystem.close`.
The closed-loop state set is unchanged, so `m.output` still reads each state. -/
def feedback (f : O → I) (m : MooreMachine S O I) : Closed S := DynSystem.close f m

@[simp] theorem feedback_step (f : O → I) (m : MooreMachine S O I) (st : S) :
    (feedback f m).step st = m.transition st (f (m.output st)) := rfl

end MooreMachine

end PFunctor
