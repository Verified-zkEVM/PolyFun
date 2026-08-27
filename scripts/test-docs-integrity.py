#!/usr/bin/env python3
"""Regression tests for ``check-docs-integrity.py``."""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path

SCRIPT_PATH = Path(__file__).with_name("check-docs-integrity.py")
SPEC = importlib.util.spec_from_file_location("check_docs_integrity", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class ModuleDocstringTests(unittest.TestCase):
    def test_standard_module_docstring(self) -> None:
        text = """/- header -/

module

public import PolyFun.PFunctor.Basic
import all PolyFun.PFunctor.Free.Basic
public meta import Lean.Elab.Do.Basic

/-! # Module documentation -/

public section
"""
        self.assertTrue(CHECKER.has_module_docstring(text))

    def test_later_section_comment_is_not_module_docstring(self) -> None:
        text = """/- header -/

module

public import PolyFun.PFunctor.Basic

public section

/-! ## Later section -/
"""
        self.assertFalse(CHECKER.has_module_docstring(text))


class LeanPathTests(unittest.TestCase):
    def test_literal_and_grouped_paths_expand(self) -> None:
        text = """
`PolyFun/PFunctor/Basic.lean`
`PolyFun/PFunctor/Dynamical/{Responder, Game}.lean`
`PolyFun/ITree/{Basic.lean,Bisim/Defs.lean}`
"""
        self.assertEqual(
            set(CHECKER.lean_paths(text)),
            {
                "PolyFun/PFunctor/Basic.lean",
                "PolyFun/PFunctor/Dynamical/Responder.lean",
                "PolyFun/PFunctor/Dynamical/Game.lean",
                "PolyFun/ITree/Basic.lean",
                "PolyFun/ITree/Bisim/Defs.lean",
            },
        )

    def test_missing_member_of_group_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_root = Path(temp_dir)
            existing = repo_root / "PolyFun/PFunctor/Existing.lean"
            existing.parent.mkdir(parents=True)
            existing.write_text("module\n")
            text = "`PolyFun/PFunctor/{Existing, DefinitelyMissing}.lean`"
            self.assertEqual(
                CHECKER.missing_lean_paths(text, repo_root),
                ["PolyFun/PFunctor/DefinitelyMissing.lean"],
            )


if __name__ == "__main__":
    unittest.main()
