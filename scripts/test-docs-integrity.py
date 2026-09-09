#!/usr/bin/env python3
"""Regression tests for ``check-docs-integrity.py``."""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

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

    def test_auxiliary_modules_and_umbrellas_are_checked(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_root = Path(temp_dir)
            for root_name in ("ToCslib", "PolyFunCslib"):
                source = repo_root / root_name / "MissingDoc.lean"
                source.parent.mkdir()
                source.write_text("module\n\npublic section\n")
            (repo_root / "PolyFunCslib.lean").write_text("module\n")
            with patch.object(CHECKER, "REPO_ROOT", repo_root):
                self.assertCountEqual(
                    CHECKER.check_module_docstrings(),
                    [
                        "Missing module docstring: ToCslib/MissingDoc.lean",
                        "Missing module docstring: PolyFunCslib/MissingDoc.lean",
                        "Missing module docstring: PolyFunCslib.lean",
                    ],
                )


class LeanPathTests(unittest.TestCase):
    def test_literal_and_grouped_paths_expand(self) -> None:
        text = """
`PolyFun/PFunctor/Basic.lean`
`PolyFun/PFunctor/Dynamical/{Responder, Game}.lean`
`PolyFun/ITree/{Basic.lean,Bisim/Defs.lean}`
`ToCslib/Computability/PolyTime.lean`
`PolyFunCslib/{Backend, PPoly}.lean`
"""
        self.assertEqual(
            set(CHECKER.lean_paths(text)),
            {
                "PolyFun/PFunctor/Basic.lean",
                "PolyFun/PFunctor/Dynamical/Responder.lean",
                "PolyFun/PFunctor/Dynamical/Game.lean",
                "PolyFun/ITree/Basic.lean",
                "PolyFun/ITree/Bisim/Defs.lean",
                "ToCslib/Computability/PolyTime.lean",
                "PolyFunCslib/Backend.lean",
                "PolyFunCslib/PPoly.lean",
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
