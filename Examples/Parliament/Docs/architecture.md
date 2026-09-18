# Architecture and implementation plan

The implementation follows five layers: executable content operations, parliamentary
state, procedural premises, certified transaction boundaries, and PolyFun interaction.
The first release is implemented; the coverage ledger identifies deliberate limits.

## Data and identity

`Foundation` separates membership rights, presence, quorum, exact integer vote
thresholds, and civil dates. Quorum is supplied by the organization's governing
rules. The chair is an externally authenticated role; the model permits a presiding
officer outside the voting membership. Present members may have distinct voting and
quorum rights. Membership itself is fixed during a configured run.

`Content` supplies a `MotionDomain` adapter with partial primary and secondary edit
operations. `wordDomain` implements bounded insertion, deletion, and replacement of
word ranges. Secondary changes edit replacement wording or narrow a deletion.
Structural validity does not establish germaneness or acceptability of the resulting
meaning; those are interpretive inputs.

Questions have identities independent of their wording and an incrementing wording
version. Pending questions are innermost first. An amendment points to its parent by
identity. `ValidTargets` checks matching parent kinds and requires a main motion to
be the root of its series. Suspended bundles retain the entire series, origin
session/date, business class, and expiry information. Resolved question versions are
kept separately in the decision history.

Dates use Gregorian month lengths. The ordering key is not an elapsed-day count.
The quarter predicate compares absolute calendar months and permits the remainder
of the third following month. Within-day time is an explicit host input. Interruptions
pause the saved speaker's clock; a date change releases that saved floor.

## Specification and execution

`RuleProgram` is a small language with explicit rejection, Boolean premises, and a
conclusion. `RuleProgram.Derives` is an inductive inference relation; `evaluate` is
its executable interpreter. Their equivalence is proved by induction. Procedure
modules author the premise programs for commands; they are the shared source of
procedure-specific policy for both execution and derivation.

`LegalStep` additionally requires source integrity, actor authorization, candidate
integrity, and independent event contracts. `step` checks those requirements and
increments the revision on success. It exposes no intermediate replacement state or
partial events on failure. Its correspondence theorem is:

```lean
step rules s command = .ok (next, events) ↔ LegalStep rules s command next events
```

The independent contracts include unique live question identities, valid amendment
parents, unique voters, presence of recognized members, quorum authorization for
substantive adopted decisions, and exact agreement of a counted decision with its
source poll and prescribed outcome.

The preservation theorems establish that *accepted* transitions preserve these
contracts. The checker explicitly validates the postcondition; this release does not
prove that every raw procedural candidate automatically satisfies it. A procedure
bug may consequently reject a command with `invalidState` without compromising the
accepted-transition theorem. Scenario coverage exercises intended successful cases.

## Interpretive interaction

An outstanding `JudgmentRequest` captures proposed wording, current question
versions, suspended questions, and prior decisions. The handler returns a `Ruling`
with an answer and explanation. `answerInput` invokes that handler and feeds its
request-indexed reply through `checkInput`. Both approving and rejecting handlers
are valid; no theorem asserts the semantic truth of either answer.

Request identity and issuance revision are echoed by the reply. Live question
identities and versions must still match. Attendance updates and seconding do not
invalidate the request merely by advancing the overall transaction revision.

A ruling remains pending until `continueAfterRuling`, or an appeal is proposed,
seconded, stated, and resolved. On appeal, affirmative votes sustain the chair;
a tie sustains. Original proposals and interrupted floor/poll state are restored
when the interpretive interruption finishes. Remedies change future execution;
past decisions are not silently rewritten. Unsupported nested review and suspension
of an active appeal are rejected explicitly.

The host controls the real-world opportunity to respond before issuing
`continueAfterRuling`, `announce`, or `closeConsent`. The engine neither schedules
people nor assumes that elapsed wall-clock time constitutes consent.

## PolyFun and replay

`JudgmentSig` exposes requests and request-indexed replies as a `PFunctor`.
`MeetingP` is an `IPFunctor.Endo` over assembly states. It has one await-input shape
at each state; a direction is an `EnabledInput`, carrying a raw command, result,
events, and `LegalStep` certificate. `checkInput` constructs this certificate from
successful runtime validation.

`Script` is `IPFunctor.IFreeM (MeetingP D rules) X s`, with a result family that may
depend on the final state. `Script.interpret` uses PolyFun's actual `mapM` fold into
an arbitrary monad. `meetingSystem` uses the sigma polynomial of the same interface
as a `PFunctor.DynSystem`. Its update is definitionally the polynomial source map.
The system is ongoing; no free-monad termination proof is used to assert meeting
termination or fairness.

`MeetingPath` records finite selected directions. Both directions of its
correspondence with `LegalTrace` are proved. `ScriptRun` records a finite execution
of an indexed script and proves that it replays. Arbitrary certified handlers
preserve step safety but need not make progress or eventually adjourn.

`replay` processes raw commands in order. Its failure value contains the failing
index and command, rejection reason, previous state, accepted prefix, and that
prefix's events. `replay_error_prefix` proves that the retained prefix itself
replays successfully and that the reported command fails at the retained state.
It also proves agreement of the index with the accepted prefix length.

## Validation and extension

The test suite combines kernel-checked concrete arithmetic/calendar/edit facts,
replay-checked meeting scenarios, error-boundary tests, external judgment handlers,
an actual PolyFun interpreter, and a separate consumer package using ordinary public
imports. `scripts/check.sh` also runs the dependency's kernel-level axiom sweep over
all `Parliament` modules; the umbrella coverage check prevents unaudited production
files from being omitted. CI invokes that same wrapper.

To extend the model:

1. Add explicit parameters and errors; extend the coverage ledger with the source section.
2. Write procedural premises and effects, retaining contextual judgments as inputs.
3. Extend independent contracts when the new operation introduces a new invariant.
4. Add successful and rejecting interaction scenarios, including replay and interruptions.
5. Export the module, document its API, and run the complete validation wrapper.

Natural follow-up increments are procedural-parameter amendments, same-day timed
orders, nested and undebatable appeal refinements, richer recognition preferences,
special orders, and reconsideration. They require new specification work and should
not be treated as aliases for existing commands.

## Implemented IO application layer

The [runtime and minutes specification](runtime.md) describes the new execution layer.
It adds a certified `History`/`Journal`, contextual `MinuteEntry` values, ordered
`Records`/`RecordsHistory` judgments, typed draft and payload certificates, a resumable
PolyFun driver, explicit application phases, and real/in-memory effect handlers.

This layer preserves the underlying parliamentary rules. It reconstructs all derived
state from the stored configuration and commands, checks publication bytes by readback,
and keeps filesystem success separate from the pure proof that the requested payload
is the canonical rendering of a certified history.
