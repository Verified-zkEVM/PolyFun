# Coverage and boundaries

This is an executable RONR-inspired subset for an ordinary formal assembly. Section
references below locate the research basis in RONR, 12th edition; they are not claims
that every exception in a section is implemented. Governing rules take precedence
through explicit configuration or a future extension, not through an invisible oracle.

| Area | Implemented behavior | Boundary / source sections |
| --- | --- | --- |
| Membership | Fixed roster; separate voting and quorum rights; presence updates; chair authorization | Host authenticates identities and supplies quorum; §§3, 40, 44 |
| Main motion | Recognition, proposal, distinct second, external admissibility ruling, chair statement, decision | Semantic admissibility and renewal supplied by handler; §4 |
| Amendments | Word insertion/deletion/replacement; primary and secondary targets; checked edits; versioned parent updates | No third degree; no procedural-parameter amendments, filling blanks, or separate substitute/perfection workflow; §12 |
| Debate | Explicit floor requests and recognition; daily per-question speech count; timed speeches; saved interrupted floor | Default two speeches and 600 seconds; chair speaks only on an appeal; preference among competing recognition claims remains with the host; §§42–43 |
| Previous Question | Two-thirds threshold; specified contiguous scope; closes debate and prevents word amendment in scope | No separate limit/extend-debate motion; §16 |
| Open voting | Latest choice per member; changes before announcement; explicit abstention; exact majority/two-thirds arithmetic | Nonsecret binary votes only; no elections, ballot secrecy, divisions, or roll-call presentation; §§4, 44–45 |
| Chair voting | Nonabstaining vote accepted at announcement only when it changes the result | Ordinary formal-assembly profile; no small-board profile; §44 |
| Unanimous consent | Chair opens an objection window; any present member can object; unopposed close adopts | Host supplies a real opportunity to object; already-stated modeled questions only; §4 |
| Quorum | Checked at proposal, statement, opening and closing decisions; recess/adjourn exceptions | No retrospective invalidation of completed business; §40 |
| Withdrawal | Maker withdraws before statement; afterward an unseconded request requires assembly approval | Main motions and word amendments; §33 |
| Points of order | Save interrupted proposal/floor/poll; external ruling; prospective remedies | One outstanding review; no nested points during appeal, retroactive correction, or disciplinary system; §23 |
| Appeals | Explicit appeal window, second, special speech count, vote on sustaining ruling, tie sustains | Context supplies debate flag; detailed unappealability/timing exceptions are not fully enumerated; §24 |
| Referral/report | Registered committee; whole pending series retained; report restores attachments | Chair records delivery; no internal committee protocol, new report text, or committee instructions; §13 |
| Postpone definitely | Future valid civil date within the modeled next-session/quarter limits; due-item restoration | Date granularity only; no same-day timed postponement, special orders, or parameter amendment; §14 |
| Lay on table | Urgency ruling, ranked adoption, whole-series suspension, expiry | No use as an unchecked debate-closing shortcut; §17 |
| Take from table | Majority vote, idle business, available bundle, restoration of adhering motions | No nested suspension of an active appeal; §34 |
| Business order | Reports, unfinished business, new business; due general orders block fresh main motions | Opening formalities, officer reports, special orders, and customized agendas deferred; §41 |
| Sessions | Recess and resumption; adjournment; meeting/session identifiers; unfinished and suspended carryover | Explicit regular-session calendar and continuing-membership flag; §§8–9, 20–21 |
| Records | Certified command history, contextual draft entries, exact wording versions, canonical JSON/Markdown, replay verification | Unapproved drafts for the bounded policy; approval/correction and full editorial RONR compliance remain outside the model; §48 |

Unsupported interactions return a specific rejection or `RuleError.unsupported`.
`Command.unsupported name` lets a host represent an unimplemented operation without
silently accepting it. Reconsideration, rescission, postpone indefinitely, suspension
of rules, elections, disciplinary proceedings, and committee/small-board procedure
are outside this release.

Interpretive replies may be wrong, biased, or inconsistent. The safety theorems
still concern procedural handling of those replies; no semantic-correctness theorem
is asserted. The host also supplies fair recognition, genuine response windows,
authentication, clock accuracy, and the validity of organizational rule overrides.

## Regression map

`ParliamentTest.Boundaries` checks threshold edges, zero-vote outcomes, quarter/month
boundaries, leap years, valid edits, and the exposed public API. `Scenarios` covers
16 complete meeting journals. `Edges` adds nine meeting journals plus PolyFun-fold,
external-handler, replay-error, and invalid-configuration checks. Every successful
scenario replays its accepted command journal and compares the entire final state
and ordered event log.

The separate `test/ParliamentConsumer` Lake package imports the public
`Examples.Parliament` umbrella from this PolyFun checkout. Sharing downloaded
dependencies is a test optimization; the package still checks ordinary imports
across a Lake package boundary.

## Executable IO and draft minutes

The terminal application covers the same word-domain procedure commands as the library.
It uses a reusable PolyFun `DynComputation` driver with Lean IO handlers, plus the same
machine under an in-memory backend. See [runtime guarantees](runtime.md).

Draft records distinguish counted decisions, unanimous consent, lack of a second,
post-statement withdrawals, rulings/appeals, dispositions, restoration/expiry, and
meeting boundaries. Proposed wording and a rejected command are not themselves
completed actions. A pre-statement withdrawal is omitted. Subsidiary decisions and
their resulting business effects may both appear; they are distinct sourced facts,
not two votes on the main motion. Unresolved wording is displayed separately.

The ordered recordability relation formalizes this explicit editorial policy. It
is not a new proof that every exception in RONR §48 has been implemented. The
bare-event `minutes` filter serves a separate event-summary API; certified drafts
use the contextual policy.

`ParliamentTest.Application` runs all 25 meeting scenarios through the actual
persistence/publication machine and compares complete states, events, reconstructed
entries, and output payloads. It also tests rejected inputs, ambiguous write failures,
publication/readback failures, chunk resumption, exact amended wording, and tampering.
`scripts/test-parliament-cli.py` exercises the compiled executable against real temporary files,
including guided commands, live judgments, EOF, recovery, immutable exports, and locks.
