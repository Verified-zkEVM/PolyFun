# Corrections ledger: announced (ePrint 2026/899) vs. actual

Running audit of claims made in the VCVio paper and the PolyFun docs against
the code as it stands, so the next paper can state repairs honestly and so
stale claims don't propagate. Add entries as found; move entries to "resolved"
with the commit/PR that fixed them.

## Open

2. **Polytime encoding model (in-flight repair on `dtumad/k-l-examples`).**
   The earlier existential-encoding `EncPolyTime` model admitted an
   advice-collapse and an encoding-caching triviality
   (`enc x := std x ++ block (f x)` caches any `f`). Being replaced by pinned
   canonical `BitEncFam`/`BoundaryData`/`EncPolyTimeFam`
   (see `docs/agents/polytime-model.md` in VCVio). Paper 2 should present the
   canonical-boundary model as the definition and note the failure mode of
   the naive one.

3. **`QueryImpl`/`ProbHandler` vs. PolyFun `Sampler`/`Decoration` duplication.**
   `ProbHandler spec := QueryImpl spec SPMF` (per-query subdistribution) is
   the memoryless oracle-signature-level analogue of PolyFun's
   `Spec.Sampler m spec := Decoration (fun X => m X) spec` (per-node monadic
   move). Two vocabularies for one concept; decide the canonical one when the
   generic Kleisli-Mealy wiring lands (roadmap Phase A) and reconcile.

4. **`OracleSpec` sum/prod/sigma/pi re-derivations.**
   `OracleSpec` re-states `PFunctor` +/×/Σ/Π operations through its own API.
   Long-standing, low-harm, but any new algebra should go through
   `PFunctor.Basic` and be re-exported, not re-proved.

5. **Two "Spec" vocabularies.** PolyFun's `Interaction.Spec`
   (`FreeM basePFunctor PUnit`, a *tree* of typed nodes) is not
   `OracleSpec ≅ PFunctor` (a flat signature). Documentation should never
   conflate them; check paper 3 drafts especially (the UC layer uses the
   former, the oracle layer the latter).

6. **Paper §9 claim "inductive rather than coinductive" is now only half the
   story.** The announced paper positions `OracleComp` as deliberately
   inductive; the branch adds the coinductive/coalgebraic complement
   (`OracleStrategy`, `RunLimit`, ITree bridge). Not an error, but paper 2
   must reconcile the framing (the pitch becomes: both sides over one
   substrate, with the free/cofree pairing between them).

8. **Spivak–Niu arXiv id / subtitle inconsistency.** The book's preprint is
   cited two ways across the repo: arXiv:2312.00990 with subtitle "A General
   Theory of Interaction" (roadmap, this bibliography's highlights) versus
   arXiv:2202.00534 with subtitle "A Mathematical Theory of Interaction"
   (`REFERENCES.md` SN24 entry, `docs/wiki/interaction.md:433`,
   `PolyFun/Control/Trace.lean`, `PolyFun/PFunctor/Trace.lean`,
   `PolyFun/PFunctor/Dynamical/Basic.lean`). Reconcile to a single canonical
   id + subtitle once verified against arXiv; deferred from the 2026-07-12
   hygiene pass to avoid guessing which posting each `Trace`/§4.3 citation
   actually intends.

## Watch (potential over-claims to avoid in future writing)

- `IPFunctor ≅ bicomodules over discrete comonoids`: folklore
  (Ahman–Uustalu–Garner directed containers), *not* stated in Spivak–Niu in
  the sections read (see `overview.md` §Vision-adjustments #5). Verify
  against the primary literature before citing.
- PolyFun coverage prose that calls `exp` "the internal hom of ⊗" — it is
  the *cartesian* exponential (5.28); the ⊗-hom (4.75) is a different object
  (roadmap ticket A1 adds it).
- Never claim "our ITrees have no Tau" — `ITree.Shape.step` is a τ node
  guarding `iter`. The true differentiator is `Bisim = Eq` (M-type
  universal property; no strong-bisim setoid). Verified against
  `PolyFun/ITree/{Basic.lean,Bisim/Defs.lean}` 2026-07-10.
- The ⊗-internal hom does **not** turn a coproduct in its first argument into
  a tensor: `[q₁ + q₂, r] ≅ [q₁,r] × [q₂,r]` uses the **categorical product
  `*`**, not `⊗`. A direction of `[q₁+q₂, r]` is `Σ j : q₁.A ⊕ q₂.A, …`, and
  a Σ over a *sum* splits as a *coproduct* of sigmas (positions ×, directions
  ⊕ = `*`), not multiplicatively (`⊗`). Formalized as `PFunctor.ihomSum`
  (`InternalHom.lean`); the earlier roadmap draft wrongly wrote `⊗`.
- The Ex 6.84 catalogue iso `By ⊗ p ≅ By ◃ p` uses the **linear** functor
  `By = linear B`, **not** the constant `C B`. `C B ⊗ p ≅ C (B × p.A)` while
  `C B ◃ p ≅ C B` (a constant absorbs substitution), so the `C B` version is
  false unless `p.A` is a singleton. Formalized correctly as
  `PFunctor.Lens.Equiv.linearTensor` (`Lens/Duoidal.lean`).

## Resolved

- **Item 1 (`FreeM ⊣ Cofree` over-claim).** Wording fixed on
  `dtumad/cleanup-hygiene`: `PolyFun/Interaction/Basic/Spec.lean`,
  `REFERENCES.md`, and `AGENTS.md`/`CLAUDE.md` now describe the
  pattern-runs-on-matter *module structure* (Libkind–Spivak) rather than an
  adjunction, and note that PolyFun formalizes `LawfulMonad (FreeM P)` /
  `LawfulComonad (CofreeC F)` separately. Formalizing the true `U ⊣ 𝒯`
  adjunction (Thm 8.45) remains roadmap Phase C.
- **Item 7 (Spivak–Niu publisher).** Corrected to Cambridge University Press,
  LMS Lecture Note Series 498, 2025 (DOI 10.1017/9781009576734) on
  `dtumad/cleanup-hygiene` across `REFERENCES.md`, `AGENTS.md`/`CLAUDE.md`, and
  `PolyFun/PFunctor/Adjunctions.lean`. The arXiv-id/subtitle inconsistency
  surfaced during that pass is tracked separately as open item 8.
