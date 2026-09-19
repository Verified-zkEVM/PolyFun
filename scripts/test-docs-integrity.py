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

    def test_import_all_annotation_is_allowed_in_prologue(self) -> None:
        text = """/- header -/

module

-- import all: unfolds `Foo.bar`
import all PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Free.Basic

/-! # Module documentation -/
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
            for root_name in ("ToCslib", "ComplexityBackends", "Examples/Tutorials",
                              "test/DocumentationConsumer", "test/ParliamentConsumer"):
                source = repo_root / root_name / "MissingDoc.lean"
                source.parent.mkdir(parents=True)
                source.write_text("module\n\npublic section\n")
            (repo_root / "ComplexityBackends.lean").write_text("module\n")
            (repo_root / "PolyFunParliamentMain.lean").write_text("module\n")
            cached = repo_root / "test/ParliamentConsumer/.lake/build/Cached.lean"
            cached.parent.mkdir(parents=True)
            cached.write_text("module\n")
            with patch.object(CHECKER, "REPO_ROOT", repo_root):
                self.assertCountEqual(
                    CHECKER.check_module_docstrings(),
                    [
                        "Missing module docstring: ToCslib/MissingDoc.lean",
                        "Missing module docstring: ComplexityBackends/MissingDoc.lean",
                        "Missing module docstring: ComplexityBackends.lean",
                        "Missing module docstring: Examples/Tutorials/MissingDoc.lean",
                        "Missing module docstring: test/DocumentationConsumer/MissingDoc.lean",
                        "Missing module docstring: test/ParliamentConsumer/MissingDoc.lean",
                        "Missing module docstring: PolyFunParliamentMain.lean",
                    ],
                )


class LeanPathTests(unittest.TestCase):
    def test_literal_and_grouped_paths_expand(self) -> None:
        text = """
`PolyFun/PFunctor/Basic.lean`
`PolyFun/PFunctor/Dynamical/{Responder, Game}.lean`
`PolyFun/ITree/{Basic.lean,Bisim/Defs.lean}`
`ComplexityBackends/CslibSingleTape/PolyTime.lean`
`ComplexityBackends/CslibSingleTape/{Backend, PPoly}.lean`
`Examples/Tutorials/Requests.lean`
"""
        self.assertEqual(
            set(CHECKER.lean_paths(text)),
            {
                "PolyFun/PFunctor/Basic.lean",
                "PolyFun/PFunctor/Dynamical/Responder.lean",
                "PolyFun/PFunctor/Dynamical/Game.lean",
                "PolyFun/ITree/Basic.lean",
                "PolyFun/ITree/Bisim/Defs.lean",
                "ComplexityBackends/CslibSingleTape/PolyTime.lean",
                "ComplexityBackends/CslibSingleTape/Backend.lean",
                "ComplexityBackends/CslibSingleTape/PPoly.lean",
                "Examples/Tutorials/Requests.lean",
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


class MarkdownTests(unittest.TestCase):
    def test_headings_duplicates_and_fences(self) -> None:
        text = '''# A `Lean` heading
## A `Lean` heading
```lean
# Not a heading
```
~~~text
# Not a heading either
~~~
<a id="explicit"></a>
'''
        self.assertEqual(CHECKER.markdown_anchors(text),
                         {"a-lean-heading", "a-lean-heading-1", "explicit"})

    def test_local_and_cross_page_fragments(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "Other Page.md").write_text("# Destination\n")
            doc = root / "README.md"
            doc.write_text('''# Start
[same](#start)
[cross](Other%20Page.md#destination)
[missing](#missing)
[bad cross](Other%20Page.md#wrong)
[missing file](absent.md)
```
[example](also-absent.md)
```
''')
            self.assertEqual(CHECKER.markdown_link_errors(doc), [
                "Broken heading anchor: #missing",
                "Broken heading anchor: Other%20Page.md#wrong",
                "Broken link: absent.md",
            ])


class ExampleTests(unittest.TestCase):
    def test_excerpt_source_and_region_contract(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            source = root / "Example.lean"
            source.write_text('''module
public import PolyFun.PFunctor.Basic
-- BEGIN README
example : True := True.intro
-- END README
''')
            doc = '''<!-- lean-example: Example.lean#README -->
```lean
import PolyFun.PFunctor.Basic

example : True := True.intro
```
'''
            self.assertEqual(CHECKER.example_errors(doc, root), [])
            self.assertIn("differs", CHECKER.example_errors(doc.replace("True.intro", "by trivial"), root)[0])
            self.assertIn("region", CHECKER.example_errors(doc.replace("#README", "#MISSING"), root)[0])
            self.assertIn("source", CHECKER.example_errors(doc.replace("Example.lean", "Missing.lean"), root)[0])
            self.assertIn("differs", CHECKER.example_errors(doc.replace("```lean", "```text"), root)[0])


if __name__ == "__main__":
    unittest.main()
