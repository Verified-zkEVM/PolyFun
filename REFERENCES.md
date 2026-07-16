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
`PolyFun/PFunctor/Free/Path.lean`, and
`PolyFun/PFunctor/PatternRunsOnMatter/`.

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

### Spi12 — Spivak, *Functorial data migration*

David I. Spivak.
*Functorial Data Migration*.
*Information and Computation*, 217:31–51, 2012.

Schemas as structured descriptions whose instances carry data; the
schema/context distinction underlies node-context schemas.

Used in: `PolyFun/Interaction/Basic/Node.lean`.

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
