#!/usr/bin/env python3
"""Regression tests for cross-root exception accounting."""
import importlib.util
from pathlib import Path
import tempfile
import sys
sys.dont_write_bytecode = True
import unittest

spec = importlib.util.spec_from_file_location('audit', Path(__file__).with_name('audit-linters.py'))
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AccountingTests(unittest.TestCase):
    def test_two_roots_and_disappeared_linter(self):
        roots = [dict(active=['docBlame'], findings=[dict(linter='docBlame', declaration='A.f')]),
                 dict(active=['docBlame'], findings=[dict(linter='docBlame', declaration='B.g')])]
        entries = [('docBlame', 'A.f'), ('docBlame', 'B.g'), ('docBlame', 'A.f'),
                   ('docBlame', 'Gone'), ('topNamespace', 'A.f')]
        self.assertEqual([r['status'] for r in audit.environment_exceptions(roots, entries)],
                         ['needed', 'needed', 'duplicate', 'stale', 'inactive-linter'])
        self.assertEqual(audit.environment_exceptions(roots, entries),
                         audit.environment_exceptions(roots[::-1], entries))

    def test_unicode_lines_do_not_narrow_exceptions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.lean').write_text('-- ⨟\n')
            line = "A.lean : line {} : ERR_UNICODE : This line contains a unicode character that is not on the allowlist '⨟' (U+2a1f)."
            rows = audit.unicode_exceptions(line.format(1) + '\n' + line.format(999), root)
            self.assertEqual([r['status'] for r in rows], ['present', 'duplicate'])
            (root / 'A.lean').write_text('-- ordinary text\n')
            self.assertEqual(audit.unicode_exceptions(line.format(1), root)[0]['status'], 'stale')
            self.assertEqual(audit.unicode_exceptions('not an exception', root)[0]['status'], 'unsupported-entry')


if __name__ == '__main__':
    unittest.main()
