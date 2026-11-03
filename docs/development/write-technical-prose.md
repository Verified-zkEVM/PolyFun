# Writing Workflow

Use this workflow when you draft or revise PolyFun documentation, comments, docstrings, commit
messages, PR text, issue text, or review comments. Use it for short comments as well as long
guides. Agents follow it as the `write-technical-prose` skill. Work on the text that the task
requests. A writing review does not authorize unrelated source changes or publication.

## Read the local requirements

Read the [writing standard](writing.md) and the [vocabulary](writing-vocabulary.md). Read the
relevant section of [CONTRIBUTING.md](../../CONTRIBUTING.md) for the contribution or text that
you prepare. The standard owns the requirements. This workflow explains how to apply them.

Treat existing prose as material to assess, not as a style to preserve automatically. Use STE's
writing principles to correct defects. Keep established identifiers, quotations, and technical
meanings accurate. Consult the official standard when the source of a rule or the approval of a
word matters. Do not invent a dictionary approval or claim full STE conformance from a checker
result.

## Establish the facts

Read the source that the claims in the passage depend on. A theorem name or a successful build
alone does not establish a mathematical claim. Inspect the statement, its hypotheses, and the
relevant proof or axiom evidence. For a mathematical contribution, use the
[review passes](review-hardening.md#required-review-passes) before review.

For a PR description, separate the change, the checks that you actually ran, and the remaining
gaps. Keep output instructions separate from repository facts. A request for a draft does not
establish the status, approval, or CI result of a PR. State those facts only when the source
supplies them.

For a review comment, identify the affected code or statement and explain the consequence. For
reference documentation, describe the interface or result that exists in the reviewed source.
Do not substitute a session history for that explanation.

If the source does not support a claim, narrow or remove the claim. Preserve uncertainty when the
evidence is incomplete. A prose task does not by itself require a new proof, build, or experiment.

## Draft and revise

Choose procedural or descriptive writing from the purpose of the passage. Start with the result,
problem, or action that the reader needs. Develop one topic in each paragraph. Add headings,
lists, and examples when they make the text easier to use.

Revise the text for direct verbs, clear actors and antecedents, consistent terms, and short
sentences. Introduce unfamiliar concepts before you use them. Remove empty praise and repetition.
Keep instructions distinct from explanations and optional advice.

Compare every mathematical rewrite with its source. Keep the hypotheses, quantifiers, negations,
bounds, exceptional cases, and direction of implication. Preserve time and requirement strength:
"may have failed" does not mean "failed", and "recommended" does not mean "required". A shorter
expression is useful only when it keeps the intended meaning.

Do not let a writing rule change standard terminology. A rule can conflict with a term or language
pattern that is standard in cryptography research and engineering, computer science, or
mathematics. In that case, keep the standard form and apply the rules to the rest of the passage.
Repository habit alone does not make a wording standard.

Use the vocabulary to resolve ambiguous terms, not to erase valid technical meanings. "The machine
exposes a request" and "the `@[expose]` attribute" need qualifiers only when the context could
confuse them.

## Use the checker

`scripts/check-writing.py` is an editing aid. It reports patterns for some rules of the writing
standard as suggestions. It uses only the Python standard library. Run it with
[uv](https://docs.astral.sh/uv/getting-started/installation/) from the repository root:

```bash
uv run --no-project --python 3.12 python scripts/check-writing.py path/to/document.md
uv run --no-project --python 3.12 python scripts/check-writing.py --base origin/main
uv run --no-project --python 3.12 python scripts/check-writing.py --stdin description < /tmp/pr-description.md
git log --format=%B origin/main..HEAD | uv run --no-project --python 3.12 python scripts/check-writing.py --stdin commits
```

For changed prose, give the actual review base to `--base`. A stacked PR can have a feature branch
as its base. Do not assume that every PR targets `main`. The checker reads each paragraph, list
item, or table cell that contains an added line, not only the added words.

Read each finding before you edit. Counts and grammar patterns are approximations. Correct real
defects, keep accurate technical expressions, and report a recurring checker defect with an
example. Do not rewrite a correct claim only to make the checker quiet.

The checker does not establish clarity, fidelity to the source, dictionary compliance, or
permission to publish. Its exit code is 0 when it runs, whatever it finds. The
[writing check in CI](validation.md#ci-mapping) reports the same findings as warnings and does
not fail a pull request.

## Read the final text before handoff

Read the complete affected passage after the last edit. Confirm that its structure is useful and
that its claims still agree with the source. Check the links and references that the edit changes.
A good sentence can still be wrong in its paragraph.

Return or save the requested text. Publish it only when the instructions of the user authorize
that action. If the task includes a commit or push, run the validation that the contribution
workflow requires first. Report material evidence gaps without a standard disclaimer on every
text.
