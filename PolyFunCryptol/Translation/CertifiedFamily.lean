/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.PolySpecialization
public import PolyFunCryptol.Translation.DataCertificate

/-!
# Certificates for one finite polymorphic source

A family interface specifies the admitted instantiations and represented input
and output shapes. A certificate retains one polymorphic source and proves
correspondence with a native function at every instance of that interface.
Restricting the interface restricts the claim; unlisted instantiations are not
certified.
-/

public section

namespace Cryptol.Finite

open Polymorphic

/-- The checked instances on which a polymorphic source is to be specified. -/
structure FamilyInterface {w : Polymorphic.Scope} (s : w.ValueSort) (I : Type) where
  /-- Assignment of the source's free parameters. -/
  assignment : I → w.Assignment
  /-- Represented input shape at each instance. -/
  input : I → Ty
  /-- Represented output shape at each instance. -/
  output : I → Ty
  /-- Inputs are finite data, not arbitrary functions. -/
  inputData : ∀ i, DataShape (input i)
  /-- Outputs are finite data, not arbitrary functions. -/
  outputData : ∀ i, DataShape (output i)
  /-- Ordered arguments and constraint evidence reaching the instance's function type. -/
  specialization : ∀ i, Specialization s (assignment i).val
    (.arrow (input i).core (output i).core)

/-- The source's meaning at one admitted instance. -/
@[expose] noncomputable def FamilyInterface.observe {w : Polymorphic.Scope} {s : w.ValueSort}
    {I : Type} (interface : FamilyInterface s I) (source : Polymorphic.Term w [] s) (i : I) :
    Computation (.arrow (interface.input i).core (interface.output i).core) :=
  source.observe (interface.assignment i) (interface.specialization i) (Polymorphic.Env.empty _)

/-- All-input semantic correspondence for one finite polymorphic description. -/
structure CertifiedFamily {w : Polymorphic.Scope} {s : w.ValueSort} {I : Type}
    (interface : FamilyInterface s I) where
  /-- The single source, before any instantiation. -/
  source : Polymorphic.Term w [] s
  /-- Native functions at the admitted instances. -/
  implementation : ∀ i, (interface.input i).Native → (interface.output i).Native
  /-- Every instance and represented input has the full represented result. -/
  correct : ∀ i x, DomainResult.applyContinuous (interface.observe source i)
    (encodeData (interface.inputData i) x) =
      encodeData (interface.outputData i) (implementation i x)

/-- The certificate at one admitted instance. -/
@[expose] noncomputable def CertifiedFamily.certificateAt {w : Polymorphic.Scope}
    {s : w.ValueSort} {I : Type} {interface : FamilyInterface s I}
    (f : CertifiedFamily interface) (i : I) :
    DataCertificate (interface.inputData i) (interface.outputData i) where
  meaning := DomainResult.applyContinuous (interface.observe f.source i)
  implementation := f.implementation i
  correct := f.correct i

end Cryptol.Finite
