#!/usr/bin/env python3
"""Compile disposable modules to test registration, roots, private bodies, and caches."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def run(command, **kwargs):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, **kwargs)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout


with tempfile.TemporaryDirectory(prefix='polyfun-linter-coverage-') as directory:
    scratch = Path(directory)
    # Lake computes the pinned dependency search path; add only our disposable modules.
    search = run(['lake', 'env', 'printenv', 'LEAN_PATH']).strip()
    env = dict(os.environ, LEAN_PATH=str(scratch) + os.pathsep + search)
    for root in ('LintFixtureMain', 'LintFixtureAux'):
        source = scratch / (root + '.lean')
        source.write_text('module\n\npublic import Batteries.Tactic.Lint\n\n'
                          f'namespace {root}\n'
                          'public def undocumented : Nat := 7\n'
                          'private def privateUnused (argument : Nat) : Nat := 7\n'
                          '/-- A deliberately unused argument. -/\n'
                          '@[nolint unusedArguments] public def suppressed (argument : Nat) : Nat := 7\n'
                          'end ' + root + '\n')
        run(['lake', 'env', 'lean', '-R', directory, str(source), '-o', str(source.with_suffix('.olean'))])
    command = ['lean', '--run', 'scripts/PolyFunLintAudit.lean', 'LintFixtureMain', 'LintFixtureAux']
    # Use lake's resolved PATH as well as LEAN_PATH, without letting lake rewrite the latter.
    env['PATH'] = run(['lake', 'env', 'printenv', 'PATH']).strip()
    first = json.loads(run(command, env=env))
    second = json.loads(run(command, env=env))
    for report in (first, second):
        assert len(report['roots']) == 2
        for row in report['roots']:
            assert {'docBlame', 'unusedArguments', 'simpNF'} <= set(row['active'])
            assert any(f['linter'] == 'docBlame' and f['declaration'].endswith('.undocumented')
                       for f in row['findings']), row
            assert any(f['annotation'] and f['declaration'].endswith('.suppressed')
                       for f in row['findings']), row
    server = first
    for row in server['roots']:
        assert any(f['linter'] == 'unusedArguments' and 'privateUnused' in f['declaration']
                   for f in row['findings']), row
    print('Coverage fixtures passed: both roots, registered linters, annotations, warm cache, private bodies.')
    print('Private findings:', sum('privateUnused' in f['declaration']
          for row in first['roots'] for f in row['findings']))
