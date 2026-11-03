# Writing Vocabulary

Use this page with the [writing standard](writing.md). STE's general dictionary stays the
reference for general words, meanings, and grammatical roles. This page adds subject-field terms
and advice for PolyFun prose. It does not replace the dictionary or list every permitted English
word.

## How to add a term

1. Find the concept in Mathlib, CSLib, Lean documentation, or its mathematical source.
2. Prefer the established term over a local synonym.
3. Record the intended meaning and grammatical role when the word can cause ambiguity.
4. Use a qualifier when two technical meanings occur in the same passage.
5. Add a missing term or meaning when the contribution first needs it.

A noun and a verb need separate technical uses, even when they have the same spelling. A noun entry for
"query" does not approve every verb use of that word. A category example is not a reason
to reject another established term from that field.

## Terms and context

These distinctions help a reader identify the intended concept. They do not prohibit the ordinary
meaning of a word in a different context:

| Term | Technical use | Clarify when necessary |
|---|---|---|
| answer, response | A direction of a polynomial interface, given for a request | Use one of the two words in a passage. "Answer" is also a verb for a handler: "the handler answers the request". |
| backend | A concrete complexity model in `ComplexityBackends`, or the model behind a quantitative realization | Write "complexity backend" or name the machine model. Do not use the word for a Lean compiler backend without a qualifier. |
| bound | A numeric or order constraint, as a noun | As a technical verb, state the quantity that it bounds. "Bounded run" means a run with fuel or a budget. |
| budget, fuel, charge | A query budget, a recursion limit for a run, and the cost assigned to a step | Keep the three words distinct. Name the declaration when the passage depends on it. |
| expose | A machine exposes its current request, or `@[expose]` makes a Lean definition body public | Write "the `@[expose]` attribute" for the Lean meaning when both meanings occur. |
| free | A free construction such as `FreeM`, or a free type parameter | Write "free monad" or "free program" for the construction. |
| handler | A value that answers each request of an interface, such as `Handler m P` | Distinguish a stateful handler from a machine. Name the monad when it matters. |
| instance | A typeclass instance, or an instantiation of a generic interface | Write "typeclass instance" when both meanings occur. |
| interface | A polynomial interface of requests and responses, or the public API of a module | Write "polynomial interface" or "public API" when both meanings occur. |
| module | A Lean module | Write "Lean module" if an algebraic module occurs in the same passage. |
| package | A Lake package, or a stateful handler in the sense of state-separating proofs | Write "Lake package" or "state-separating package". |
| position, direction | The shape `P.A` and the arity family `P.B` of a polynomial functor | Do not rotate with "shape" and "arity" in one passage (W3). Introduce the alternative names once if a source uses them. |
| process | An open process in `PolyFun/Interaction/Open/`, or an operating-system process | Write "open process" or "operating-system process" when both occur. |
| program | A value of a free or indexed program type, such as `FreeM P α` | Write "executable" for a compiled Lean program. |
| query, request | A position of a polynomial interface, as a noun. "Query" is also a technical verb: "the machine queries the interface". | Use one noun in a passage. |
| run | The execution of a program or machine, as a noun or a verb | Name the runner, such as `Control.Transition.run`, when several runners occur. |
| state | A machine state, a handler state, or an index of an indexed interface | Write "machine state", "handler state", or "index" when the meaning could change. |
| step | A silent step of an interaction tree, a machine transition, or a proof step | Write "silent step" or "machine step" when the meaning could change. |
| trace, observation | A recorded sequence of visible events, or a chosen relation that compares closed systems | Name the observation relation. A coarse observation is not a security observation. |
| valid, admissible | Satisfaction of a stated predicate, such as admissibility for a `StepClass` | Name the predicate. Do not use "valid" for "admissible" unless they mean the same thing. |
| verify | A formal-verification result, or a check of recorded data | Use "check" for routine repository tests. Identify the predicate or theorem. |

## Technical nouns

These examples identify relevant subject fields. Preserve established terms and their spellings.
Introduce a longer or unfamiliar term before you use an abbreviation:

| Field | Examples |
|---|---|
| Polynomial functors | polynomial functor, position, direction, lens, chart, composition product, tensor product, free monad, cofree comonad, comonoid |
| Indexed programs | indexed polynomial functor, indexed container, indexed program, pre-state, post-state, command substitution |
| Interaction trees | interaction tree, silent step, visible event, handler, resumption, iteration, strong bisimulation, weak bisimulation |
| Machines | dynamical system, state machine, machine state, transition, behavior, trajectory, simulation |
| Interaction | type tree, decoration, role, party, strategy, sequential composition, parallel composition, open process, context |
| Program logic | weakest precondition, support, ordered algebra, partial correctness, monad morphism |
| Realizability | represented type, step class, admissible function, boundary, encoding, realization, resource certificate |
| Complexity backends | complexity backend, machine model, single-tape machine, time bound, query bound, work bound |
| Lean | declaration, theorem, lemma, hypothesis, docstring, namespace, typeclass, instance, module, `public section`, transparency, axiom |
| Repository tools | branch, commit, pull request, build, linter, axiom sweep, umbrella module, consumer package, validation, CI |

Prose uses Oxford spelling or American spelling, as rule W8 describes. Keep the original spelling
in a cited title or a declaration name.

## Technical -ing nouns

These terms name the stated technical concepts. They do not authorize a verbal clause.
The checker reads this table for rule V2.

| Term | Technical meaning |
|---|---|
| `encoding`, `decoding` | The representation and interpretation of values or messages under specified formats. |
| `folding`, `batching` | Reduction and aggregation constructions on words or computations. |
| `hashing`, `binding`, `hiding` | Hash constructions and named commitment properties. |
| `sampling`, `padding` | Random-choice constructions and prescribed data extension. |
| `rewriting`, `normalizing` | Lean expression transformations by equations or reduction. |
| `pattern matching` | Selection of a branch by a constructor pattern. |
| `indexing`, `mapping` | Index conventions and maps between mathematical objects. |
| `working tree`, `dangling symlink` | A Git checkout and a symlink with no target. |
| `programming`, `computing` | Program construction and computation as subject fields. |
| `unfolding`, `embedding` | The behavior map of a machine and inclusions that preserve structure. |
| `routing`, `branching`, `linking` | Request dispatch, choice structure, and composition of processes. |
| `counting`, `typing` | Cardinality arguments and the types of dependent expressions. |
| `opening` | Initial meeting formalities. The [coverage notes](../../Examples/Parliament/Docs/coverage.md) identify these as outside the model. |
| `operating system` | The system that hosts an executable process. |

## Technical verbs

Use these verbs for the stated subject-field actions. Keep the meaning of a verb consistent within
a passage. Explain the operation or name the relevant declaration when its meaning is not clear:

| Field | Examples of actions |
|---|---|
| Mathematics | prove a claim, define an object, assume a hypothesis, bound a quantity, compose morphisms |
| Programs and machines | interpret a program, handle a request, query an interface, run a machine, unfold a machine to its behavior, simulate a machine |
| Indexed programs | substitute a command, reindex a family, traverse the leaves of a program |
| Realizability | realize a program, encode a value, charge a step, transport a realization |
| Lean | instantiate a variable, specialize a theorem, unfold a definition, rewrite an expression, elaborate a term, expose a definition |
| Repository tools | build a target, run a linter, validate a change, rebase a branch, merge a PR, stage a file, review a contribution |

"Replace" is a technical verb for substitution and state updates: "`put s` replaces the current
state with `s`". Do not use it in reference text to describe a change to the library (rule C3).
In the same way, "previously" can refer to an earlier point in a run, as in "previously set
flags".

## Words to avoid

This table gives prompts for a revision pass over ordinary prose. It does not define STE word
approval. Use a replacement only when it preserves the meaning and grammatical role. Rewrite the
sentence when a direct replacement does not work:

| Avoid | Use |
|---|---|
| "utilize", "leverage", "make use of" | use |
| "ensure" | make sure that, or name the condition and the action |
| "in order to" | to |
| "prior to", "subsequent to" | before, after |
| "in the event that" | if |
| "comprised of" | has, contains |
| "a number of", "various" | the number, or "some", if the quantity is not specified |
| "e.g.", "i.e.", "etc." | for example, that is, the full list |
| "cf.", "resp.", "w.r.t.", "wlog" | compare, explicit pairings, with respect to, without loss of generality |
| "respectively" | explicit pairings when the reference would otherwise be unclear |
| "robust", "seamless", "comprehensive", "powerful", "elegant", "crucial" | the measurement or the reason |
| "clearly", "obviously", "trivially", "basically" | the reason, or delete the word |
| "it is worth noting that", "it is important to" | delete the phrase when it adds no information |
| "now", "no longer", "previously", "formerly", "currently", "new", "renamed from" | in library reference text, the fact about the present state (rule C3) |

"The following are equivalent" is a permitted mathematical introduction. A word in the table can
also occur in a technical term, such as "robust compilation". Words such as "simply" and
"essentially" occur in "simply typed" and "essentially surjective". Review their meaning. Do not delete them as isolated words.
