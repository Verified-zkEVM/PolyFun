#!/usr/bin/env python3
"""Black-box executable tests using isolated real filesystem directories."""
from pathlib import Path
import copy
import json
import os
import selectors
import subprocess
import sys
import tempfile
import time
from cli_test_support import conversation

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / 'Examples/Parliament/.lake/build/bin/polyfun-parliament'


def run(*args, text='', success=True):
    result = subprocess.run([str(EXE), *map(str, args)], input=text,
                            text=True, capture_output=True, timeout=30)
    if (result.returncode == 0) != success:
        raise AssertionError(f'{args}: status={result.returncode}\n{result.stdout}\n{result.stderr}')
    return result


def command(tag, **fields):
    return json.dumps({tag: fields}, ensure_ascii=False)


def journal(directory):
    return json.loads((directory / 'journal.json').read_text())


def exported(directory, revision):
    return directory / 'exports' / f'rev-{revision}'


def readme_session(root):
    """Adopt the README's first motion using guided prompts, then resume/verify/replay."""
    meeting = root / 'readme-meeting'
    actor = 'Actor member ID: '
    actions = [
        ('attendance', [(actor, '0'), ('Member ID: ', str(member)), ('Present (yes/no): ', 'yes')])
        for member in range(4)]
    actions += [
        ('openMeeting', [(actor, '0')]),
        ('advanceBusiness', [(actor, '0')]),
        ('advanceBusiness', [(actor, '0')]),
        ('requestFloor', [(actor, '1')]),
        ('recognize', [(actor, '0'), ('Member ID: ', '1')]),
        ('propose', [(actor, '1'), ('Motion (main,', 'main'),
                     ('Motion wording: ', 'fund the library')]),
        ('second', [(actor, '2')]),
        ('judge', [('Ruling (allow, deny, cancel): ', 'allow'),
                   ('Explanation: ', 'Within the assembly purpose.')]),
        ('continueAfterRuling', [(actor, '0')]),
        ('stateQuestion', [(actor, '0')]),
        ('openVote', [(actor, '0')]),
        ('vote', [(actor, '1'), ('Choice (yes/no/abstain): ', 'yes')]),
        ('vote', [(actor, '2'), ('Choice (yes/no/abstain): ', 'yes')]),
        ('announce', [(actor, '0')]),
        ('status', []),
        ('quit', [])]
    exchanges = []
    for action, fields in actions:
        exchanges.append(('Action (', action))
        exchanges.extend(fields)
    output = conversation([EXE, 'new', '--config',
                           ROOT / 'Examples/Parliament/Fixtures/assembly.json',
                           '--dir', meeting], exchanges)
    assert 'Accepted revision 18.' in output, output
    assert 'Meeting 0, revision 18; phase' in output, output
    assert len(journal(meeting)['commands']) == 18
    draft = exported(meeting, 18)
    minutes = json.loads((draft / 'minutes.json').read_text())
    assert minutes['status'] == 'draft-unapproved' and minutes['adjourned'] is False
    decisions = [entry['action'] for entry in minutes['entries']
                 if entry['action']['kind'] == 'decided']
    assert len(decisions) == 1 and decisions[0]['adopted'] is True
    assert decisions[0]['question']['motion']['main']['text'] == ['fund', 'the', 'library']
    before = (meeting / 'journal.json').read_bytes()
    assert 'revision 18' in run('resume', meeting, text='status\nquit\n').stdout
    assert (meeting / 'journal.json').read_bytes() == before
    run('verify', meeting / 'journal.json', draft)
    reconstructed = root / 'readme-reconstructed'
    run('replay', meeting / 'journal.json', '--out', reconstructed)
    for filename in ['minutes.md', 'minutes.json']:
        assert (draft / filename).read_bytes() == (exported(reconstructed, 18) / filename).read_bytes()
    print('Parliament README session: adopt, resume, verify and replay: ok')


def stop_process(process):
    """Reap a child even when an assertion or timeout interrupts its test."""
    try:
        if process.poll() is None:
            process.kill()
        process.wait(timeout=5)
    finally:
        for stream in (process.stdin, process.stdout, process.stderr):
            if stream is not None:
                stream.close()


def wait_for_output(process, expected, timeout=10):
    """Wait for an output prefix without blocking on an unfinished line."""
    deadline = time.monotonic() + timeout
    output = b''
    with selectors.DefaultSelector() as selector:
        selector.register(process.stdout, selectors.EVENT_READ)
        while len(output) < len(expected):
            if not selector.select(max(0, deadline - time.monotonic())):
                raise TimeoutError(f'waiting for {expected!r}; received {output!r}')
            chunk = os.read(process.stdout.fileno(), 4096)
            if not chunk:
                raise AssertionError(f'child exited before {expected!r}; received {output!r}')
            output += chunk
    assert output.startswith(expected), output


# A child that never prints must fail promptly rather than hanging the CI job.
silent = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'],
                          stdout=subprocess.PIPE)
try:
    try:
        wait_for_output(silent, b'\n', timeout=0.05)
    except TimeoutError:
        pass
    else:
        raise AssertionError('silent child did not time out')
finally:
    stop_process(silent)


with tempfile.TemporaryDirectory(prefix='parliament-cli-') as temporary:
    root = Path(temporary)
    readme_session(root)
    run('verify', ROOT / 'Examples/Parliament/Fixtures/draft/journal.json', ROOT / 'Examples/Parliament/Fixtures/draft')
    config = json.loads(run('example-config').stdout)
    config['metadata'].update(organization='Assembly α & β', title='Budget *review*\n# literal')
    config_path = root / 'config.json'
    config_path.write_text(json.dumps(config, ensure_ascii=False))
    assert 'resume' in run('--help').stdout
    assert '--config' in run('new', '--help').stdout
    for args in [('unknown',), ('new',), ('resume',), ('verify', 'one-argument')]:
        run(*args, success=False)
    conversation([EXE, 'new', '--dir', root / 'terminal', '--config', config_path], [
        ('Action (', 'status'), ('Action (', 'compareRuling'), ('Action (', 'quit')])
    # Initialization claims the directory exclusively, even when two processes race.
    raced = root / 'new-parent' / 'raced-meeting'
    competitors = []
    try:
        for _ in range(2):
            competitors.append(subprocess.Popen(
                [str(EXE), 'new', '--config', str(config_path), '--dir', str(raced) + '/'],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True))
        for process in competitors:
            process.communicate('', timeout=30)
        assert sorted(process.returncode for process in competitors) == [0, 1]
    finally:
        for process in competitors:
            stop_process(process)
    assert journal(raced)['commands'] == []
    meeting = root / 'meeting'
    text = (ROOT / 'Examples/Parliament/Fixtures/meeting.input').read_text()
    result = run('new', '--config', config_path, '--dir', meeting, text=text)
    assert 'Ruling (allow, deny, cancel)' in result.stdout
    saved = journal(meeting)
    assert len(saved['commands']) == 18
    first_export = exported(meeting, 18)
    minutes = json.loads((first_export / 'minutes.json').read_text())
    assert minutes['status'] == 'draft-unapproved' and minutes['adjourned'] is False
    decisions = [e['action'] for e in minutes['entries'] if e['action']['kind'] == 'decided']
    assert len(decisions) == 1 and decisions[0]['adopted'] is True
    assert decisions[0]['question']['motion']['main']['text'] == ['fund', 'the', 'library']
    md = (first_export / 'minutes.md').read_text()
    assert 'α \\& β' in md and '\\*review\\*\\n\\# literal' in md
    run('verify', meeting / 'journal.json', first_export)
    recreated = root / 'recreated'
    run('replay', meeting / 'journal.json', '--out', recreated)
    for filename in ['minutes.md', 'minutes.json']:
        assert (first_export / filename).read_bytes() == (exported(recreated, 18) / filename).read_bytes()

    # EOF exports an unfinished draft without adding an adjournment or any other command.
    before = (meeting / 'journal.json').read_bytes()
    run('resume', meeting)
    assert (meeting / 'journal.json').read_bytes() == before
    # More than two IO chunks execute without losing or repeating terminal interactions.
    resumed = run('resume', meeting, text='status\n' * 150 + 'quit\n')
    assert resumed.stdout.count('Meeting 0, revision 18; phase') == 150
    assert (meeting / 'journal.json').read_bytes() == before
    run('new', '--config', config_path, '--dir', meeting, success=False)
    assert (meeting / 'journal.json').read_bytes() == before

    # Invalid JSON, illegal commands, and stale judgment replies are not journal entries.
    invalid = '\n'.join(['{broken', command('unsupported', name='reconsider'),
        command('answerJudgment', actor=0, request=1, revision=999,
                answer={'allowed': True, 'reason': 'stale'}), 'quit']) + '\n'
    result = run('resume', meeting, text=invalid)
    assert 'Input error' in result.stdout and 'Rejected' in result.stdout
    assert (meeting / 'journal.json').read_bytes() == before

    # Guided terminal actions (including structured motions) follow the same machine.
    guided = '\n'.join(['requestFloor', '1', 'recognize', '0', '1',
                        'propose', '1', 'adjourn', 'second', '2', 'stateQuestion', '0',
                        'seekConsent', '0', 'closeConsent', '0', 'quit']) + '\n'
    run('resume', meeting, text=guided)
    assert len(journal(meeting)['commands']) == 25
    closed = exported(meeting, 25)
    closed_data = json.loads((closed / 'minutes.json').read_text())
    assert closed_data['adjourned'] is True
    assert any(e['action'].get('method') == 'consent' for e in closed_data['entries'])
    run('verify', meeting / 'journal.json', closed)

    # A second meeting keeps prior minutes and records new meeting identifiers.
    next_calendar = copy.deepcopy(config['calendar'])
    next_calendar.update(today={'year': 2026, 'month': 2, 'day': 15},
                         nextRegular={'year': 2026, 'month': 3, 'day': 15}, meeting=1, session=1)
    restart = command('nextMeeting', actor=0, calendar=next_calendar, newSession=True) + '\n'
    restart += command('openMeeting', actor=0) + '\nquit\n'
    run('resume', meeting, text=restart)
    later = exported(meeting, 27)
    assert {e['meeting'] for e in json.loads((later / 'minutes.json').read_text())['entries']} == {0, 1}
    run('verify', meeting / 'journal.json', later)

    # Both files, including the machine-readable one, must exactly match the journal.
    for filename in ['minutes.md', 'minutes.json']:
        path = later / filename
        original = path.read_bytes()
        path.write_bytes(original + b'altered')
        run('verify', meeting / 'journal.json', later, success=False)
        run('replay', meeting / 'journal.json', '--out', meeting, success=False)
        assert path.read_bytes() == original + b'altered'  # immutable export is not overwritten
        path.write_bytes(original)

    invalid_wire = root / 'invalid.json'
    unknown = journal(meeting)
    unknown['version'] = 99
    invalid_wire.write_text(json.dumps(unknown))
    assert 'unsupported journal version' in run('replay', invalid_wire, '--out', root/'bad',
                                               success=False).stderr
    illegal = journal(meeting)
    illegal['commands'].append({'unsupported': {'name': 'reconsider'}})
    invalid_wire.write_text(json.dumps(illegal))
    assert 'command 27' in run('replay', invalid_wire, '--out', root/'bad', success=False).stderr
    invalid_wire.write_text('{bad')
    run('replay', invalid_wire, '--out', root/'bad', success=False)
    assert not (root/'bad').exists()

    # A real filesystem write failure stops acceptance and leaves the old journal recoverable.
    before = (meeting / 'journal.json').read_bytes()
    (meeting / 'journal.json.pending').mkdir()
    result = run('resume', meeting, text=command('attendance', actor=0, member=1, present=True)+'\n',
                 success=False)
    assert 'Journal persistence failed' in result.stdout
    assert (meeting / 'journal.json').read_bytes() == before
    (meeting / 'journal.json.pending').rmdir()
    run('resume', meeting)

    # An incomplete export directory stays unpublished; retry can complete it after recovery.
    broken = root / 'broken-export'
    (broken / 'exports/.pending-27/minutes.md').mkdir(parents=True)
    run('replay', meeting/'journal.json', '--out', broken, success=False)
    assert not exported(broken, 27).exists()
    (broken / 'exports/.pending-27/minutes.md').rmdir()
    run('replay', meeting/'journal.json', '--out', broken)
    run('verify', meeting/'journal.json', exported(broken, 27))

    # Cancelled/EOF judgment prompts never manufacture a ruling.
    cancelled = root / 'cancelled'
    prefix = text.split('judge\n')[0]
    run('new', '--config', config_path, '--dir', cancelled, text=prefix+'judge\ncancel\n')
    assert len(journal(cancelled)['commands']) == 11
    assert not any('answerJudgment' in c for c in journal(cancelled)['commands'])
    run('resume', cancelled, text='judge\n')
    assert len(journal(cancelled)['commands']) == 11
    before = (cancelled / 'journal.json').read_bytes()
    exports_before = {p.relative_to(cancelled): p.read_bytes()
                      for p in (cancelled / 'exports').rglob('*') if p.is_file()}
    comparison = run('resume', cancelled, text='compareRuling\nquit\n')
    assert 'HYPOTHETICAL ONLY' in comparison.stdout
    assert 'ALLOW\n' in comparison.stdout and 'DENY\n' in comparison.stdout
    assert (cancelled / 'journal.json').read_bytes() == before
    assert {p.relative_to(cancelled): p.read_bytes()
            for p in (cancelled / 'exports').rglob('*') if p.is_file()} == exports_before
    result = run('resume', cancelled, text='history\n0\njudge\nallow\nreason\nlive\nquit\n')
    assert 'History is read-only; enter live before a command or judgment.' in result.stdout
    assert (cancelled / 'journal.json').read_bytes() == before

    # A lock covers the live writer even though the journal itself is replaced by rename.
    live = subprocess.Popen([str(EXE), 'resume', str(meeting)], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        # The newline header is emitted after acquiring the writer lock.
        wait_for_output(live, b'\n')
        blocked = run('resume', meeting, success=False)
        assert 'another writer' in blocked.stderr
        live.communicate(b'quit\n', timeout=10)
        assert live.returncode == 0
    finally:
        stop_process(live)

    # The editable document is not a rewritten action register. Exercise actual guided IO too.
    minutes = root / 'minutes-lifecycle'
    run('new', '--config', config_path, '--dir', minutes,
        text=text.removesuffix('quit\n') + guided)
    assert len(journal(minutes)['commands']) == 25
    calendar = dict(config['calendar'], meeting=1)
    commands = [command('nextMeeting', actor=0, calendar=calendar, newSession=False)]
    commands += [command('attendance', actor=0, member=i, present=True) for i in range(4)]
    commands += [command('openMeeting', actor=0)]
    run('resume', minutes, text='\n'.join(commands) + '\n'
        'submitMinutesDraft\n1\n0\n25\nintentionally inaccurate\n'
        'openMinutesReview\n0\n0\n0\ncloseMinutesReview\n0\n0\n0\nquit\n')
    approved_wire = journal(minutes)
    approved_revision = len(approved_wire['commands'])
    approved_doc = json.loads((exported(minutes, approved_revision) / 'minutes.json').read_text())
    assert approved_doc['documents'][0]['originalApprovedText'] == ['intentionally', 'inaccurate']
    prefix_entries = approved_doc['entries']
    run('resume', minutes, text='requestFloor\n1\nrecognize\n0\n1\n'
        'propose\n1\ncorrectMinutes\n0\n0\nlater correction\nsecond\n2\n'
        'stateQuestion\n0\nseekConsent\n0\ncloseConsent\n0\nquit\n')
    changed_revision = len(journal(minutes)['commands'])
    changed = json.loads((exported(minutes, changed_revision) / 'minutes.json').read_text())
    doc = changed['documents'][0]
    assert doc['originalApprovedText'] == ['intentionally', 'inaccurate']
    assert doc['currentText'] == ['later', 'correction'] and doc['version'] == 1
    assert changed['entries'][:len(prefix_entries)] == prefix_entries
    before = (minutes / 'journal.json').read_bytes()
    result = run('resume', minutes, text='history\n0\nback\nforward\njudge\nlive\nquit\n')
    assert 'READ-ONLY HISTORY' in result.stdout
    assert (minutes / 'journal.json').read_bytes() == before
    legacy = dict(journal(minutes), version=1)
    legacy_path = root / 'legacy.json'
    legacy_path.write_text(json.dumps(legacy))
    assert 'unsupported journal version 1' in run(
        'replay', legacy_path, '--out', root / 'legacy-output', success=False).stderr

print('CLI: live judgments, guided commands, new/resume/replay/verify, exact exports, EOF, '
      'invalid input, multiple meetings, locks, and filesystem recovery passed.')
