# Writing Standard

Use this guide to write clear technical English for PolyFun. It draws on ASD-STE100 Simplified
Technical English (STE), Issue 9, January 2025. STE is the reference for improving the prose.
An existing repository convention is not a reason to keep unclear writing.

The [vocabulary](writing-vocabulary.md) records technical meanings and wording to avoid.
[CONTRIBUTING.md](../../CONTRIBUTING.md#writing) states where the standard applies to a
contribution. The [writing workflow](write-technical-prose.md) describes how to draft and revise
text.

## Scope

Apply this guide when you add or revise documentation, Lean comments and docstrings, commit
messages, PR and issue descriptions, and review comments. Read the surrounding text for context.
Correct related defects that affect the passage, but keep unrelated rewrites in a separate change.

Keep formulas, identifiers, commands, source quotations, official titles, generated output, and
license terms accurate. Do not rewrite them to satisfy a prose rule. These exclusions do not cover
explanations that an author puts in quotation marks. Headings and table labels can be fragments,
but they must use clear and consistent terms.

## How to use STE

STE combines writing rules with a general dictionary. The dictionary limits both word meanings
and parts of speech. Subject-specific technical nouns and technical verbs supplement it under
STE rules 1.5 to 1.13. Mathematical terminology does not replace the general dictionary.

Use the STE dictionary when you need to confirm the approved meaning or grammatical role of a
general word. Use the project vocabulary for technical terms. A missing term is not automatically
a defect, and a familiar English word is not automatically STE-approved. When a literal replacement
changes the meaning, rewrite the sentence. Alternatively, keep the necessary term and explain its
technical use.

Technical accuracy takes priority over the rules in this guide. A rule can conflict with a term or
language pattern that is standard in cryptography research and engineering, computer science, or
mathematics. In that case, keep the standard form and apply the rules to the rest of the sentence.
A wording that is only a habit in this repository is not a standard form.

This guide is a repository adaptation, not a complete copy of STE or a claim of full STE
conformance. It does not distribute or automatically check the official dictionary. The
[relation to STE](#relation-to-ste) separates the adaptations from the source rules.

## Text types

Choose a text type from its purpose, not from its Markdown marker:

| Type | Purpose | Examples | Sentence limit |
|---|---|---|---|
| Procedural | Tell a reader how to do a task | Build instructions, workflow steps, contributor tasks | 20 words |
| Descriptive | Explain a result, concept, or observation | Guides, docstrings, PR explanations | 25 words |

A numbered list can describe results. A paragraph can contain an instruction. Apply the limit for
the purpose of the sentence. Keep commands distinct from explanations and warnings.

## Rules

The identifiers below are PolyFun labels. STE references identify the source principle. They do
not claim that this page reproduces each source rule. STE's general recommendations (GR) are
advice in the standard. This guide adopts the recommendations named below as repository
requirements.

### Words

- **W1.** Prefer an STE-approved general word with the intended meaning and part of speech.
  Use an established technical term when the subject requires it. Rephrase before making a
  replacement that changes the meaning. (STE 1.1 to 1.4, 9.1, 9.2)
- **W2.** Use technical terms with their stated meanings and grammatical roles. Qualify a term
  when the passage could support more than one meaning. (STE 1.5 to 1.13)
- **W3.** Use one term for one concept within a passage. Do not rotate synonyms for variety.
  Introduce a different technical meaning before you use it. (STE 1.11, 9.4)
- **W4.** Limit a multi-word noun to three words. Split a dense noun group with words such as
  "of", "for", or "on". Preserve established terms under W5. (STE 2.1, 2.2)
- **W5.** Introduce a longer technical noun in full. Then use a clear shorter name, a defined
  abbreviation, or suitable hyphenation. Do not invent an abbreviation only to shorten the text.
  (STE 2.2)
- **W6.** Replace a phrasal verb with a direct verb when the replacement preserves the meaning.
  For example, write "find" rather than "figure out". (STE 9.3)
- **W7.** Write English words instead of Latin abbreviations in prose. For example, write
  "for example" instead of "e.g.". Preserve official titles and source quotations. (STE GR-6)
- **W8.** Use American English spelling in prose. Preserve official names, identifiers, and
  quotations with a different spelling. (STE 1.14)
- **W9.** Use gender-neutral language when gender is not relevant. Use "they" for a person whose
  pronouns you do not know. (STE GR-7)

### Verbs

- **V1.** Prefer simple tenses, the imperative, and the infinitive. Avoid a complex verb form
  when a simpler construction gives the same information. Preserve time and uncertainty:
  "the build may have failed" does not mean "the build failed". (STE 3.1 to 3.4, PolyFun
  adaptation)
- **V2.** A verb form ending in "-ing" must act as a technical noun or modify one. Rewrite other
  verbal uses. "Unfolding" can name the passage from a machine to its behavior. "During" is a
  preposition, so this rule does not apply to it. (STE 3.5)
- **V3.** Use the active voice. Name the person, tool, handler, machine, or mathematical object
  that performs the action. Do not invent an actor. (STE 3.6)
- **V4.** Use the passive voice in descriptive text only when the actor is unknown. A participle
  can describe a state without forming a passive construction: "the run is bounded".
  (STE 3.3, 3.6)
- **V5.** Express an action with a verb rather than an abstract noun phrase. Write
  "the handler answers the request", not "the handler provides an answer to the request".
  (STE 3.7)
- **V6.** Use "that" after "prove", "show", "assume", or "make sure" when it separates a claim
  from the preceding verb. Do not add it before an object: "prove the theorem". (STE GR-1)

### Sentences

- **S1.** Use the sentence limits for the text type. Split a long sentence at a logical boundary.
  Keep its conditions and qualifications. Use the [word-count rules](#word-count). (STE 5.1, 6.3)
- **S2.** Give a sentence one topic. Give a work step one instruction, except for actions that
  must occur together. (STE 4.1, 5.2)
- **S3.** Put a condition before an instruction when the reader needs it before acting.
  For example, "If the build fails, read the log." (STE 5.4)
- **S4.** Use the imperative for work steps. Distinguish an instruction from a requirement or a
  description. Preserve the force of "must", "may", and "can" when you revise a requirement.
  (STE 5.3, PolyFun adaptation)
- **S5.** Keep the articles, subjects, and verbs that a sentence needs. Do not use contractions
  to shorten prose. (STE 4.2, 4.5)
- **S6.** Connect related sentences so the reader can follow the argument. State the connection
  rather than expecting punctuation alone to express it. (STE 4.4)
- **S7.** Give each pronoun a clear antecedent. After "this" or "these", name the object when
  the reference could be ambiguous. (STE GR-3, GR-4)
- **S8.** Put instructions in the procedure, not inside a note. Readers can skip notes. Use notes
  for supporting information. (STE 5.5)

### Paragraphs and lists

- **P1.** Give each paragraph one topic. Introduce that topic before its details. (STE 6.4, 6.5)
- **P2.** Keep a paragraph to six sentences or fewer. Split it where the subject or purpose
  changes. (STE 6.6)
- **P3.** Introduce information gradually. Define unfamiliar terms and notation before using
  them in an explanation. (STE 6.1, 6.2)
- **L1.** Use a vertical list when it makes steps, cases, or conditions easier to distinguish.
  A short series does not always need a list. (STE 4.3)
- **L2.** Introduce a list with a clear purpose and a colon. Each item must connect to that
  introduction. Items can complete the introductory sentence or be complete sentences. (STE 4.3)
- **L3.** Keep the grammatical form and punctuation consistent within a list. Start prose items
  with a capital letter. Preserve the case of identifiers. (STE 4.3, PolyFun formatting
  convention)
- **L4.** Number work steps when their order matters. Do not imply an order for independent
  facts. (STE 5.2)

### Punctuation and emphasis

- **U1.** Replace a prose semicolon with an appropriate sentence boundary or conjunction.
  Do not change code punctuation. (STE 8.1)
- **U2.** Avoid a dash between clauses. State the relationship in words or use two sentences.
  A dash can separate a term from its description. This convention does not restrict
  mathematical notation. (PolyFun addition)
- **U3.** Use hyphens to group related words when that grouping makes the term clearer.
  Preserve the conventional spelling of an established technical term. (STE 8.2)
- **U4.** Use parentheses for references, identifiers, abbreviations, explanations, or
  alternatives. Keep information needed for an instruction in the instruction itself. (STE 8.3)
- **U5.** Use emphasis for a term, label, warning, or specific requirement. Avoid emphasis across
  an entire paragraph. (PolyFun addition)

### Word count

STE 8.4 to 8.7 defines word counting. A number with its unit, an abbreviation, a proper name,
a quoted title, a formula, and a hyphenated group each count as one word. Do not add hyphens or
quotation marks to hide a long sentence.

Text in parentheses counts as one word in the enclosing sentence. Check the parenthetical text
separately for sentence length. A list introduction ends at its colon for word counting. Each list
item counts separately.

PolyFun also counts an identifier, command, URL, or citation key as one word. Ordinary link text
keeps its words. This word-count convention is a technical-text adaptation. The
[checker](write-technical-prose.md#use-the-checker) approximates these conventions. Review the
actual sentence when its count is doubtful.

### Claims and source evidence

PolyFun adds these requirements to the STE principles:

- **C1.** State only what the code or recorded evidence establishes. Identify assumptions,
  conditional results, and checks that you did not run.
- **C2.** Preserve the strength of a claim. Keep hypotheses, quantifiers, negations, bounds,
  and qualifications. Do not turn a possible result into an established one.
- **C3.** Describe the present library in its reference documentation and docstrings. Change
  history belongs in commit messages, PR descriptions, and Git history.
- **C4.** Replace internal session notes and temporary planning codes with accessible
  explanations or maintained references. A reader of the merged tree must be able to find the
  cited source.
- **C5.** Replace unsupported quality claims with a fact or evidence. Words such as "robust" or
  "comprehensive" do not supply that evidence.
- **C6.** Give an argument, a witness, or a precise reference instead of calling a result
  "obvious" or "trivial". Established technical names such as "trivial group" remain
  permitted.
- **C7.** Remove repetition that adds no useful context. Repeat a condition when the reader
  needs it at the point of use.
- **C8.** Make the source of each mathematical claim traceable. Cite public literature through
  [`REFERENCES.md`](../../REFERENCES.md), and follow the
  [content-control rules](review-hardening.md#content-control) for paper-facing claims.

### Mathematical conventions

"Let", "fix", and "suppose" can introduce mathematical notation. They do not issue a work step.
"We" can refer to the author and reader in an argument. A state such as "the request tree is
well-founded" is not an instruction or a passive action.

A technical word can have a noun use and a verb use, as in "a query" and "query an interface".
STE permits these dual roles when each use meets the rules for its category (STE 1.7, 1.12,
1.13). Record the noun use and the verb use separately in the vocabulary. Qualify words such as
"state", "step", "run", "package", and "expose" when their meaning changes between polynomial
interfaces, machines, Lean, and the build tools.

## Examples

These examples come from PolyFun prose. They show when to revise and when to keep accurate
wording:

| Before | After | Reason |
|---|---|---|
| "A handler can also introduce its own effects or nontermination; well-founded syntax alone does not certify arbitrary external execution." | A handler can also introduce its own effects or nontermination. Well-founded syntax alone does not certify arbitrary external execution. | Replace the semicolon (U1). Keep "alone" and "arbitrary", which limit the claim (C2). |
| "Ensure these are committed so all worktrees see them." | Commit these files so that every worktree can read them. | State the action and name the object (W1, S7). |
| "`EncPolyTime` is trivially inhabited against a non-injective codomain encoding (the erasing machine), so faithfulness is always a hypothesis." | The erasing machine inhabits `EncPolyTime` against a non-injective codomain encoding, so faithfulness is always a hypothesis. | Name the witness instead of calling the result trivial (C6), and name the actor (V3). |
| "`tick`'s pre-state `Phase.counting` doesn't unify with the fresh `s'`" | `tick`'s pre-state `Phase.counting` does not unify with the fresh `s'` | Write the full form of the contraction (S5). |
| "A well-founded request tree need not have one finite bound on the lengths of all its branches." | Keep as written. | "Need not" denies a guarantee. "Does not have" makes a stronger claim (C2). |
| "Robust-compilation accounts (PKWC24) derive UC composition and dummy results from explicit interface axioms." | Keep as written. | "Robust compilation" is a standard term in secure-compilation research. It is not a quality claim (C5). |
| "`Front S` is the type of currently enabled frontier events." | Keep as written. | "Currently enabled" describes the state of a run, not the history of the library (C3). |
| "Unfolding forgets the internal state representation." | Keep as written. | "Unfolding" is a technical noun for the passage from a machine to its behavior (V2). |

Use the [writing workflow](write-technical-prose.md) to compare a mathematical rewrite with its
source. A shorter sentence is not an improvement if it changes the statement.

## Relation to STE

| Source | Use in PolyFun |
|---|---|
| STE 1.1 to 1.4, general vocabulary | Kept as the reference for general meanings and grammatical roles. This guide and its checker do not implement the full dictionary. |
| STE 1.5 to 1.13, technical terms | Applied through the project vocabulary and established subject-field usage. |
| STE 1.7, 1.12, and 1.13, noun and verb roles | STE permits one word as a technical noun and a technical verb when each use meets the rules for its category. An example is "query". This use is not an adaptation. |
| All STE rules, technical accuracy | PolyFun adaptation. Standard terminology and language patterns in cryptography, computer science, and mathematics stay when a rule conflicts with them. Repository habit is not a reason for this exception. |
| STE 2 to 6, 8, and 9 | The source principles inform the rules above. Mathematical notation and the stated adaptations preserve technical meaning. |
| STE 3.1 to 3.4, verb forms | PolyFun adaptation. Simple constructions stay preferred. A modal or complex form stays when a change would lose uncertainty or time. |
| STE 5.3, imperative instructions | PolyFun adaptation. A requirement keeps its force ("must", "may", "can") when it is revised as a description. |
| STE 7, safety instructions | Apply the relevant principle to risky operations. Put the condition or instruction before an explanation of the consequence. |
| STE 8.4 to 8.7, word count | PolyFun adaptation. An identifier, command, URL, or citation key counts as one word. |
| STE general recommendations | The named recommendations are local requirements. This guide does not represent them as STE rules. |
| PolyFun additions | Source evidence, history scope, citations, clause-joining dashes, emphasis, and the capital letter on list items are local contribution policies. |

Refer to [ASD's official Issue 9](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf)
for the full rules and dictionary. ASD owns the standard. This guide uses original repository
examples. It does not claim certification or reproduce the official dictionary.
