# References

This file centralizes the public external references cited in module
docstrings across `PolyFun/`. When adding a new citation in shared docs,
prefer linking here instead of duplicating partial citations inline.

## Foundational citations

### HS00 — Hancock and Setzer, *Interactive programs in dependent type theory*

Peter Hancock and Anton Setzer.
*Interactive Programs in Dependent Type Theory*.
In *Computer Science Logic, 14th Annual Conference of the EACSL*, 2000.

Recursion over interaction interfaces; the free interaction structure on
a polynomial container; command/response interfaces with embedded
observation modes. Companion paper: *Interactive programs and weakly
final coalgebras in dependent type theory* (FOSAD III, 2005).

Used in: `PolyFun/PFunctor/Free/Path.lean`, `PolyFun/PFunctor/Trace.lean`,
`PolyFun/Interaction/Basic/TypeTree.lean`,
`PolyFun/Interaction/Basic/Telescope.lean`,
`PolyFun/Interaction/Multiparty/Core.lean`.

### AGHMM15 — Altenkirch, Ghani, Hancock, McBride, Morris, *Indexed Containers*

Thorsten Altenkirch, Neil Ghani, Peter Hancock, Conor McBride, and
Peter Morris.
*Indexed Containers*.
*Journal of Functional Programming* 25, e5, 2015.
DOI: <https://doi.org/10.1017/S095679681500009X>

Containers, indexed containers, and interaction structures. The
foundational result that polynomial functors / containers represent
strictly-positive datatypes.

Used in: `PolyFun/PFunctor/Free/Path.lean`,
`PolyFun/Interaction/Basic/TypeTree.lean`.

### SN24 — Spivak and Niu, *Polynomial Functors*

David I. Spivak and Nelson Niu.
*Polynomial Functors: A Mathematical Theory of Interaction*.
Cambridge University Press, London Mathematical Society Lecture Note
Series 498, 2025 (DOI 10.1017/9781009576734; preprint: arXiv:2312.00990).

The polynomial-functor calculus, charts, lenses, the composition product,
the free-monad / cofree-comonad pairing, and the slogan "pattern runs on
matter". (The pairing is the module structure of Libkind–Spivak below, not
an adjunction; PolyFun formalizes `LawfulMonad (FreeM P)` and
`LawfulComonad (CofreeC F)` separately.)

Used in: `PolyFun/PFunctor/Trace.lean`, `PolyFun/PFunctor/Lens/State.lean`,
`PolyFun/PFunctor/Free/Path.lean`, the dynamical-systems layer in
`PolyFun/PFunctor/Dynamical/` (Ch. 4), `PolyFun/Interaction/Basic/TypeTree.lean`,
`PolyFun/Interaction/Basic/Telescope.lean`,
`PolyFun/Interaction/UC/Interface.lean`, and
companion files in `PolyFun/Interaction/UC/`.

### LS25 — Libkind and Spivak, *Pattern runs on matter*

Sophie Libkind and David I. Spivak.
*Pattern runs on matter: the free monad monad as a module over the
cofree comonad comonad*.
Electronic Proceedings in Theoretical Computer Science 429 (2025), pp. 1–28.
DOI 10.4204/EPTCS.429.1; arXiv:2404.16321.

Free polynomial monads as terminating decision trees, with the
free-monad-as-module-over-cofree-comonad structure made explicit (a module
action, not an adjunction).

Used in: `PolyFun/PFunctor/SubstMonoid.lean`,
`PolyFun/PFunctor/Free/Path.lean`,
`PolyFun/PFunctor/PatternRunsOnMatter/`, and
`PolyFun/Realizability/Basic.lean`.

### XZHHMPZ20 — Xia, Zakowski, He, Hur, Malecha, Pierce, Zdancewic, *Interaction Trees*

Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha,
Benjamin C. Pierce, and Steve Zdancewic.
*Interaction Trees: Representing Recursive and Impure Programs in Coq*.
*Proceedings of the ACM on Programming Languages* 4 (POPL),
Article 51, January 2020.
DOI: <https://doi.org/10.1145/3371087>

Coinductive interaction trees as the M-type of a one-step polynomial
functor; the strong / weak bisimulation framework; the iter combinator;
event-handler composition.

Used in: `PolyFun/ITree/Basic.lean`, `PolyFun/ITree/Bisim/Defs.lean`,
`PolyFun/ITree/Sim/Defs.lean`, `PolyFun/PFunctor/Free/Path.lean`.

### EO23 — Escardó and Oliva, *Higher-order games with dependent types*

Martín Escardó and Paulo Oliva.
*Higher-order games with dependent types*.
*Theoretical Computer Science* 974 (2023), 114133.
DOI: <https://doi.org/10.1016/j.tcs.2023.114133>

Games as type trees; selection-functor games; dependent moves and
strategies.

Used in: `PolyFun/PFunctor/Free/Path.lean`,
`PolyFun/Interaction/Basic/TypeTree.lean`.

### McB10 — McBride, *Ornamental Algebras, Algebraic Ornaments*

Conor McBride.
*Ornamental Algebras, Algebraic Ornaments*.
Manuscript, 2010.

Displayed algebras and the calculus of ornaments. The displayed-free
machinery in `PolyFun/PFunctor/Free/Displayed.lean` follows this
viewpoint.

Used in: `PolyFun/Interaction/Basic/TypeTree.lean`,
`PolyFun/PFunctor/Free/Displayed.lean` (implicit).

### DM14 — Dagand and McBride, *Transporting functions across ornaments*

Pierre-Évariste Dagand and Conor McBride.
*Transporting functions across ornaments*.
*Journal of Functional Programming* 24, e23, 2014.

The displayed-algebra/ornament correspondence used to manage indexed
data over polynomial substrates.

Used in: `PolyFun/Interaction/Basic/TypeTree.lean`.

### Abe26 — Aberlé, *Compositional Program Verification with Polynomial Functors*

Christian Aberlé.
*Compositional Program Verification with Polynomial Functors*.
arXiv:2604.01303, 2026.

Dependent polynomials over a base polynomial, their free displayed extension,
displayed handlers, and compositional verification applications.

Used in: `PolyFun/PFunctor/Display/`,
`PolyFun/Realizability/Basic.lean`.

### Spi12 — Spivak, *Functorial data migration*

David I. Spivak.
*Functorial Data Migration*.
*Information and Computation*, 217:31–51, 2012.

Schemas as structured descriptions whose instances carry data; the
schema/context distinction underlies node-context schemas.

Used in: `PolyFun/Interaction/Basic/Node.lean`.

### FKKKT26 — Farshim, Karvonen, Knispel, Kohlweiss, Tyagi, *UC, Categorically*

Pooya Farshim, Martti Karvonen, André Knispel, Markulf Kohlweiss, and
Shravan Tyagi.
*UC, Categorically: Rigorous Diagrammatic Proofs*.
Cryptology ePrint Archive, Report 2026/1605; arXiv:2608.04521, 2026.

A categorical account of static/simple universal composability in which
computational indistinguishability is an equivalence on resources closed
under sequential and parallel composition. It supplies the external
instantiation contract tracked in `docs/wiki/uc.md`; probability and
efficiency remain downstream obligations.

Used in: `docs/wiki/uc.md`.

### CSV19 — Canetti, Stoughton, Varia, *EasyUC*

Ran Canetti, Alley Stoughton, and Mayank Varia.
*EasyUC: Using EasyCrypt to Mechanize Proofs of Universally Composable
Security*.
IEEE Computer Security Foundations Symposium (CSF), pp. 167–183, 2019.
DOI: <https://doi.org/10.1109/CSF.2019.00019>; ePrint 2019/582.

An EasyCrypt realization of a restricted UC model and a composed secure
messaging case study. Its experience with routing boilerplate and the mismatch
between procedure calls and coroutine communication informs the typed-boundary
and control-transfer requirements in the UC audit.

Used in: `docs/wiki/uc.md`.

### KTR20 — Küsters, Tuengerthal, Rausch, *The IITM Model*

Ralf Küsters, Max Tuengerthal, and Daniel Rausch.
*The IITM Model: A Simple and Expressive Model for Universal Composability*.
*Journal of Cryptology* 33, pp. 1461–1584, 2020.
DOI: <https://doi.org/10.1007/s00145-020-09352-1>.

A UC model with named tapes, explicit environmental boundedness, dummy
forwarding, and theorems relating networks of IITMs to single machines. It is
the main comparison point for the efficiency and addressing obligations that
PolyFun deliberately leaves to an instantiation.

Used in: `docs/wiki/uc.md`.

### HARM+23 — Haselwarter et al., *SSProve*

Philipp G. Haselwarter, Exequiel Rivas, Antoine Van Muylder, Théo
Winterhalter, Carmine Abate, Nikolaj Sidorenco, Cătălin Hrițcu, Kenji
Maillard, and Bas Spitters.
*SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq*.
*ACM Transactions on Programming Languages and Systems* 45(3), 2023.
DOI: <https://doi.org/10.1145/3594735>; ePrint 2021/397.

Free-monad cryptographic packages, sequential and parallel composition, and
machine-checked algebraic package laws connected to a probabilistic relational
program logic.

Used in: `docs/wiki/uc.md`.

### LS25-N — Larsen and Schürmann, *Nominal State-Separating Proofs*

Markus Krabbe Larsen and Carsten Schürmann.
*Nominal State-Separating Proofs*.
IEEE Computer Security Foundations Symposium (CSF), 2025; ePrint 2025/598.

A nominal extension of SSProve in which packages receive local state-name
spaces and composition automatically avoids capture. It makes explicit the
modularity cost of globally named mutable state.

Used in: `docs/wiki/uc.md`.

### PKWC24 — Patrignani, Künnemann, Wahby, Cecchetti, *Universal Composability Is Robust Compilation*

Marco Patrignani, Robert Künnemann, Riad S. Wahby, and Ethan Cecchetti.
*Universal Composability Is Robust Compilation*.
*ACM Transactions on Programming Languages and Systems* 46(4), Article 13,
pp. 1–64, 2024. DOI: <https://doi.org/10.1145/3698234>;
arXiv:1910.08634.

An axiomatic comparison between UC and robust compilation, including explicit
interface and composition requirements and mechanized symbolic case studies.

Used in: `docs/wiki/uc.md`.

### FGMPS07 — Foster, Greenwald, Moore, Pierce, Schmitt, *Combinators for bidirectional tree transformations*

J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore,
Benjamin C. Pierce, and Alan Schmitt.
*Combinators for Bidirectional Tree Transformations: A Linguistic
Approach to the View-Update Problem*.
*ACM Transactions on Programming Languages and Systems* 29, 3,
Article 17, May 2007.

Lenses; the bidirectional-transformation calculus that the polynomial
lens layer in `PolyFun/PFunctor/Lens/` makes dependent.

Used in: `PolyFun/PFunctor/Lens/State.lean`,
`PolyFun/PFunctor/Lens/Basic.lean`.

## Realizability citations

### KC96 — Kapron and Cook, *A new characterization of type-2 feasibility*

Bruce M. Kapron and Stephen A. Cook.
*A New Characterization of Type-2 Feasibility*.
*SIAM Journal on Computing* 25(1):117–132, 1996.
DOI: <https://doi.org/10.1137/S0097539794263452>

Second-order polynomials with oracle-length applications, used here as syntax
for bounds on adaptive open computations. PolyFun does not import the paper's
machine-model feasibility claim; concrete backend adequacy remains an external
obligation.

Used in: `PolyFun/Complexity/SecondOrderPolynomial.lean`.

The realizability layer in `PolyFun/Realizability/` recombines pieces owned by
four separate communities; these are the canonical sources for each. No single
source states the combination — a machine realization whose *structure maps* are
constrained by an abstract predicate — so the layer's docstrings cite the
ingredients rather than claiming a name for the whole.

### AM74 — Arbib and Manes, *Machines in a category*

Michael A. Arbib and Ernest G. Manes.
*Machines in a Category: An Expository Introduction*.
*SIAM Review* 16(2):163–192, 1974.
DOI: <https://doi.org/10.1137/1016026>

A machine in an arbitrary category as an initialization / transition / readout
triple, and its induced behaviour. The `expose` / `update` / readout triple of a
`DynComputation` is an Arbib–Manes machine for the one-step polynomial functor;
what the realizability layer adds is that the structure maps must lie in a
distinguished class. Companion sources for "realization is universal": Goguen
1972/73 and Naudé, *Universal realization*, JCSS 19(3), 1979.

Used in: `PolyFun/Realizability/Basic.lean`.

### AMMS13 — Adámek, Milius, Moss, Sousa, *Well-pointed coalgebras*

Jiří Adámek, Stefan Milius, Lawrence S. Moss, and Lurdes Sousa.
*Well-Pointed Coalgebras*.
*Logical Methods in Computer Science* 9(3), 2013.
arXiv:1305.0576

The coalgebraic use of the word *realization*: a pointed coalgebra realizes the
corresponding element of the terminal coalgebra, and the well-pointed coalgebras
are exactly the minimal realizations. This is the realizability predicate of
`PolyFun/Realizability/` with the admissibility constraint removed.

Used in: `PolyFun/Realizability/Basic.lean`.

### PR89 — Pnueli and Rosner, *On the synthesis of a reactive module*

Amir Pnueli and Roni Rosner.
*On the Synthesis of a Reactive Module*.
In *Principles of Programming Languages* (POPL), 1989.
DOI: <https://doi.org/10.1145/75277.75293>

*Realizability* as the existence of a finite-state machine meeting a
specification — the reading recovered by `StepClass.finite`, for which
`IsFiniteStateRealizable` is provided as the community's name. Ancestor: Church,
*Applications of recursive arithmetic to the problem of circuit synthesis*, 1963.

Used in: `PolyFun/Realizability/Instances.lean`.

### Uus15 — Uustalu, *Stateful runners of effectful computations*

Tarmo Uustalu.
*Stateful Runners of Effectful Computations*.
*Mathematical Foundations of Programming Semantics* XXXI,
*Electronic Notes in Theoretical Computer Science* 319:403–421, 2015.
DOI: <https://doi.org/10.1016/j.entcs.2015.12.024>

A stateful runner of `T`-computations is exactly a comodel, i.e. a coalgebra of
the corresponding comonad. This is why a `p`-coalgebra with state `S` *is* a way
of running every `FreeM p` program in `S`, and hence why realizability is a
statement about coalgebras. See also Katsumata, Rivas, and Uustalu,
*Interaction laws of monads and comonads*, LICS 2020 (arXiv:1912.13477).

Used in: `PolyFun/Realizability/Basic.lean`.

### PM15 — Petcher and Morrisett, *The Foundational Cryptography Framework*

Adam Petcher and Greg Morrisett.
*The Foundational Cryptography Framework*.
In *Principles of Security and Trust* (POST/ESOP), LNCS 9036, 2015.
arXiv:1410.3735

Security definitions parameterized by an *admissibility predicate* naming the
class of allowed adversaries, over a free-monad-shaped computation type. This is
the design precedent for taking the resource bound as a predicate on the
implementation rather than as a measure on runs, and the source of the
`admissible` / `_mem` vocabulary used throughout the layer.

Used in: `PolyFun/Realizability/StepClass.lean`.

### Blum67 — Blum, *A machine-independent theory of complexity*

Manuel Blum.
*A Machine-Independent Theory of the Complexity of Recursive Functions*.
*Journal of the ACM* 14(2):322–336, 1967.
DOI: <https://doi.org/10.1145/321386.321395>

Complexity measures axiomatized rather than fixed, with a complexity class as
"there exists a program from an enumeration satisfying a resource predicate" —
the same existential shape as `IsRealizableBy`, but quantifying over a Gödel
numbering of programs rather than over machines with constrained structure maps.

Used in: `PolyFun/Realizability/Basic.lean`.

### GHP09 — Ghani, Hancock, Pattinson, *Representations of stream processors*

Neil Ghani, Peter Hancock, and Dirk Pattinson.
*Representations of Stream Processors Using Nested Fixed Points*.
*Logical Methods in Computer Science* 5(3:9), 2009.
arXiv:0905.4813

Continuous and computable functions on final coalgebras represented by an
alternating `νX.μY.` fixpoint — a machine whose individual steps are finite
well-founded programs. This is the known special case of admissible
realizability at the class "given by a finite `FreeM` term".

Used in: `PolyFun/Realizability/Basic.lean`.

## Distributive-category citations

The closure structure a step class needs — finite products, finite coproducts, and
distributivity — is exactly a distributive category. These are the canonical
sources for the concept and for the complexity-theory vocabulary it replaces.

### Coc93 — Cockett, *Introduction to distributive categories*

J. Robin B. Cockett.
*Introduction to Distributive Categories*.
*Mathematical Structures in Computer Science* 3(3):277–307, 1993.
DOI: <https://doi.org/10.1017/S0960129500000232>

The definition: a category with finite products and binary coproducts in which the
canonical map has an inverse. Also the distributive / recognizable / extensive /
familial hierarchy, and the theorem that the distributive completion of a
cartesian category is its coproduct completion.

`PFunctor.StepClass.IsDistributive` axiomatizes the inverse direction; the
canonical (cogap) direction is derivable from products and sums alone and ships as
`StepClass.codistrib_mem`, so the two together give Cockett's axiom verbatim. Only
the binary case is required here. Compare
`Mathlib.CategoryTheory.IsCartesianDistributive`, which states the axiom in the
cogap orientation.

Used in: `PolyFun/Realizability/StepClass.lean`.

### CLW93 — Carboni, Lack, Walters, *Extensive and distributive categories*

Aurelio Carboni, Stephen Lack, and R. F. C. Walters.
*Introduction to Extensive and Distributive Categories*.
*Journal of Pure and Applied Algebra* 84(2):145–158, 1993.
DOI: <https://doi.org/10.1016/0022-4049(93)90035-R>

Disentangles distributivity from extensivity, which had been conflated. Includes
the nullary clause `0 ≅ A × 0` that full finite distributivity also demands and
that this layer deliberately omits, extensivity being a statement about pullbacks
that a class of resource-bounded functions has no business claiming.

Textbook companion: R. F. C. Walters, *Categories and Computer Science*,
Cambridge Computer Science Texts 28, CUP, 1991 — the treatment that made
distributive categories the CS-facing default.

Used in: `PolyFun/Realizability/StepClass.lean`.

### CF92 — Cockett and Fukushima, *About Charity*

J. Robin B. Cockett and Tom Fukushima.
*About Charity*.
Yellow Series Report 92/480/18, Department of Computer Science,
University of Calgary, 1992.

The internal language of distributive categories, as a programming language, and
the source of the reading this layer uses: distributivity is what makes *proof by
case analysis* available. `IsDistributive.elimCtx_mem` — case analysis in a
context — is that reading made into the working lemma. Companion:
Cockett and Spencer, *Strong categorical datatypes II: A term logic for
categorical programming*, TCS 139(1–2):69–113, 1995.

Used in: `PolyFun/Realizability/StepClass.lean`.

### CDGH12 — Cockett, Díaz-Boïls, Gallagher, Hrubeš, *Timed sets*

J. Robin B. Cockett, Joaquín Díaz-Boïls, Jonathan Gallagher, and Pavel Hrubeš.
*Timed Sets, Functional Complexity, and Computability*.
*Electronic Notes in Theoretical Computer Science* 286:117–137, 2012 (MFPS XXVIII).
DOI: <https://doi.org/10.1016/j.entcs.2012.08.009>

Categories of timed sets modulo a complexity order form distributive restriction
categories, with PTIME and LOGSPACE as worked examples. The closest existing
statement that a complexity class *is* a distributive category, and hence the
nearest prior art for treating a resource-bounded function class as one.

Used in: `docs/wiki/realizability.md`.

### CH08 — Cockett and Hofstra, *Introduction to Turing categories*

J. Robin B. Cockett and Pieter J. W. Hofstra.
*Introduction to Turing Categories*.
*Annals of Pure and Applied Logic* 156(2–3):183–209, 2008.
DOI: <https://doi.org/10.1016/j.apal.2008.04.005>

Axioms for when a class of total maps is the total-map subcategory of a Turing
category, instantiated at LINTIME, PTIME, and EXPTIME. This is the precedent for
presenting a complexity class as a cartesian category with a faithful functor to
`Set` — and, by omission, evidence that the coproduct and distributivity
requirements here are not inherited from that tradition: the Turing-category
axioms mention neither, using two disjoint points of a universal object as a
hand-rolled stand-in for `1 ⊕ 1`.

Companion: Cockett, Hofstra, and Hrubeš, *Total maps of Turing categories*,
ENTCS 308:129–146, 2014.

Used in: `docs/wiki/realizability.md`.

### Clo99 — Clote, *Computation models and function algebras*

Peter Clote.
*Computation Models and Function Algebras*.
In *Handbook of Computability Theory* (E. R. Griffor, ed.),
Studies in Logic and the Foundations of Mathematics 140,
Elsevier, 1999, pp. 589–681.
DOI: <https://doi.org/10.1016/S0049-237X(99)80033-0>

The complexity-native vocabulary for a class of functions closed under
composition: a *function algebra*. Foundational instances: Cobham, *The intrinsic
computational difficulty of functions*, 1965 (FP by bounded recursion on
notation), and Bellantoni and Cook, *A new recursion-theoretic characterization of
the polytime functions*, Computational Complexity 2:97–110, 1992.

Function algebras are single-sorted, so branching enters as a *base function*
(`caseBit`, Bellantoni–Cook's `C`) and distributivity is invisible in that
tradition. Making the axiom visible is a consequence of this layer being
multi-sorted and representation-indexed.

Used in: `docs/wiki/realizability.md`.
