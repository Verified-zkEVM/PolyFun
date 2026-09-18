# Research ledger

Specification baseline: **RONR, 12th edition**, ordinary formal assembly.
The [official edition page](https://robertsrules.com/books/newly-revised-12th-edition/)
identifies this edition. This implementation is independent and is not an official
Robert's Rules publication or a substitute for the complete manual.

Sources consulted:

- [Official frequently asked questions](https://robertsrules.com/frequently-asked-questions/):
  voting thresholds, abstentions, chair participation, quorum, and minutes.
- [Official interpretations](https://robertsrules.com/official-interpretations/):
  interpretive context; older-edition interpretations require edition-specific care.
- [RONR 12th-edition text, hosted PDF](https://static1.squarespace.com/static/632a33aaad395c03987c7993/t/64a249bcd345564990cbbcf2/1688357315799/Roberts%2BRules%2B12th%2BEdition.pdf):
  primary rule text used to check the section references in the coverage ledger.
  No book text is bundled in this repository.

Key research distinctions retained in the design:

- Interpretive applicability requires recorded external judgments.
- Parliamentary sessions and meetings are distinct; calendar-quarter calculations
  cannot be replaced by a fixed number of days.
- Suspended business carries its adhering questions and relevant debate context.
- A vote on an appeal asks whether to sustain the ruling.
- Debate, consent, and counted voting require distinct control phases.
- The action register and speech transcript serve different purposes.

The [coverage ledger](coverage.md) links each modeled family to its source sections
and states the implementation's narrower scope. Read that ledger together with the
[architecture](architecture.md) when assessing what a theorem actually guarantees.

## PolyFun integration

The case study is maintained in PolyFun and imports the same checkout's public
APIs. It uses indexed free computations, dynamical systems, resumable execution,
and monadic handlers. Its toolchain and dependency versions come from the root
`lean-toolchain` and `lakefile.toml`; it has no separate production dependency pin.
