#!/usr/bin/env python3
"""Read-only lint inventory. Run after building PolyFun and ToCslib.

The Lean probe uses the same per-root environments as Batteries' runner and additionally
checks annotated declarations. This frontend accounts for the shared JSON allowlist and
source-level exceptions. It never regenerates exceptions or changes Lean source files.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parent.parent


def environment_exceptions(reports, exceptions):
    """Classify entries across all roots, without last-root-wins updating."""
    active = {n for r in reports for n in r['active']}
    findings = {(f['linter'], f['declaration']) for r in reports for f in r['findings']}
    seen = set()
    rows = []
    for linter, declaration in exceptions:
        key = (linter, declaration)
        status = ('duplicate' if key in seen else
                  'inactive-linter' if linter not in active else
                  'needed' if key in findings else 'stale')
        rows.append(dict(linter=linter, declaration=declaration, status=status))
        seen.add(key)
    return rows


def unicode_exceptions(text, root):
    """The pinned Mathlib matcher ignores lines, matching a path and character."""
    rows, seen = [], set()
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith('--'):
            continue
        match = re.fullmatch(r"(.+) : line (\d+) : ERR_UNICODE : .*allowlist '(.)' \(U\+[0-9a-fA-F]+\).*", line)
        if not match:
            rows.append(dict(entry=number, status='unsupported-entry', text=line))
            continue
        filename, _, char = match.groups()
        key = (filename, char)
        path = root / filename
        status = ('duplicate' if key in seen else
                  'missing-file' if not path.is_file() else
                  'stale' if char not in path.read_text() else 'present')
        rows.append(dict(entry=number, file=filename, character=char, status=status))
        seen.add(key)
    return rows


def source_options(root):
    rows = []
    for directory in ('PolyFun', 'ToCslib', 'PolyFunTest'):
        for path in sorted((root / directory).rglob('*.lean')):
            for line, text in enumerate(path.read_text().splitlines(), 1):
                match = re.match(r'\s*set_option ((?:weak\.)?linter\.\S+)\s+(\S+)', text)
                if match:
                    rows.append(dict(file=str(path.relative_to(root)), line=line,
                                     option=match[1], value=match[2], scoped=text.rstrip().endswith(' in')))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exported', action='store_true', help='diagnose ordinary-import coverage (not the runner environment)')
    parser.add_argument('--extra', action='append', default=[], help='trial a registered optional environment linter')
    parser.add_argument('--check', action='store_true', help='fail on unsuppressed findings or obsolete environment annotations/entries')
    parser.add_argument('--json', action='store_true', help='print the complete machine-readable inventory')
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    pins = {}
    for package in manifest['packages']:
        if package['name'] not in ('mathlib', 'cslib', 'batteries'):
            continue
        path = ROOT / manifest['packagesDir'] / package['name']
        actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != package['rev']:
            parser.error(f"{package['name']}: checkout {actual} differs from pin {package['rev']}; restore dependencies first")
        pins[package['name']] = actual
    command = ['lake', 'env', 'lean', '--run', 'scripts/PolyFunLintAudit.lean']
    if args.exported:
        command.append('--exported')
    command.extend('--extra=' + name for name in args.extra)
    process = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if process.returncode:
        sys.stderr.write(process.stdout + process.stderr)
        return process.returncode
    report = json.loads(process.stdout)
    roots = report['roots']
    exceptions = json.loads((ROOT / 'scripts/nolints.json').read_text())
    entries = environment_exceptions(roots, exceptions)
    allowed = {tuple(e) for e in exceptions}
    unexpected = [dict(root=r['root'], **f) for r in roots for f in r['findings']
                  if not f['annotation'] and (f['linter'], f['declaration']) not in allowed]
    stale_annotations = [dict(root=r['root'], **a) for r in roots for a in r['annotations'] if not a['needed']]
    report.update(pins=pins, toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
                  environment_exceptions=entries, unexpected=unexpected,
                  stale_annotations=stale_annotations,
                  unicode_exceptions=unicode_exceptions((ROOT / 'scripts/nolints-style.txt').read_text(), ROOT),
                  source_options=source_options(ROOT),
                  lake_options=tomllib.loads((ROOT / 'lakefile.toml').read_text())['leanOptions'])
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(f"Toolchain: {report['toolchain']} ({report['visibility']} visibility)")
        for name, rev in pins.items():
            print(f'{name}: {rev}')
        for root in roots:
            print(f"{root['root']}: {root['declarations']} declarations; active: {', '.join(root['active'])}")
        print('Environment exceptions:', dict(Counter(e['status'] for e in entries)))
        print('Unicode entries:', dict(Counter(e['status'] for e in report['unicode_exceptions'])))
        print('Scoped/source options:', dict(Counter(e['option'] for e in report['source_options'])))
        print(f'Unexpected findings: {len(unexpected)}; stale annotations: {len(stale_annotations)}')
        for row in unexpected + stale_annotations:
            print(f"  {row['root']}: {row['linter']}: {row['declaration']}")
    return int(bool(args.check and (unexpected or stale_annotations or any(e['status'] != 'needed' for e in entries))))


if __name__ == '__main__':
    sys.exit(main())
