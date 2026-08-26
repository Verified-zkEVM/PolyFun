#!/usr/bin/env python3
"""Check PolyFun documentation integrity.

Checks:
1. `CLAUDE.md` exists and is a symlink to `AGENTS.md`.
2. Local markdown links in tracked top-level docs and `docs/` resolve.
3. Repository-rooted Lean paths in those documents resolve even when they
   are written as code rather than markdown links.
4. Every production and test Lean module has a module documentation comment.

Exit code 0 if all checks pass, 1 otherwise.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CLAUDE_PATH = REPO_ROOT / "CLAUDE.md"
AGENTS_PATH = REPO_ROOT / "AGENTS.md"

# The set of tracked markdown files we walk for link checking. Top-level
# repo docs plus everything under `docs/`. Keep this list in sync with the
# wiki maintenance contract in `docs/wiki/README.md`.
TRACKED_PATHS = [
    "AGENTS.md",
    "CONTRIBUTING.md",
    "README.md",
    "REFERENCES.md",
    "docs",
]

MARKDOWN_LINK_RE = re.compile(r"(?<!!)\[[^\]]+\]\(([^)]+)\)")
LEAN_PATH_RE = re.compile(
    r"(?<![A-Za-z0-9_./])((?:PolyFun|PolyFunTest)/[A-Za-z0-9_./-]+\.lean)"
)


def tracked_markdown_files() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "--", *TRACKED_PATHS],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return [
        REPO_ROOT / rel_path
        for rel_path in result.stdout.splitlines()
        if rel_path.endswith(".md")
    ]


def check_claude_symlink() -> list[str]:
    errors: list[str] = []
    if not AGENTS_PATH.exists():
        errors.append("Missing AGENTS.md")
        return errors
    if not CLAUDE_PATH.exists() and not CLAUDE_PATH.is_symlink():
        errors.append("Missing CLAUDE.md")
        return errors
    if not CLAUDE_PATH.is_symlink():
        errors.append("CLAUDE.md must be a symlink to AGENTS.md")
        return errors

    target = Path(CLAUDE_PATH.readlink())
    if target != Path("AGENTS.md"):
        errors.append(f"CLAUDE.md must point to AGENTS.md, found {target}")
    elif not CLAUDE_PATH.resolve().samefile(AGENTS_PATH):
        errors.append("CLAUDE.md symlink does not resolve to AGENTS.md")
    return errors


def resolve_link(source_file: Path, raw_target: str) -> Path | None:
    target = raw_target.strip().strip("`")
    if not target or "://" in target or target.startswith("mailto:"):
        return None

    path_part = target.split("#", 1)[0].strip()
    if not path_part:
        return None

    if path_part.startswith("/"):
        return (REPO_ROOT / path_part.lstrip("/")).resolve()
    return (source_file.parent / path_part).resolve()


def check_markdown_links() -> list[str]:
    errors: list[str] = []
    for doc_file in tracked_markdown_files():
        text = doc_file.read_text()
        for raw_target in MARKDOWN_LINK_RE.findall(text):
            resolved = resolve_link(doc_file, raw_target)
            if resolved is None:
                continue
            if not resolved.exists():
                rel_doc = doc_file.relative_to(REPO_ROOT)
                errors.append(f"Broken link in {rel_doc}: {raw_target}")
    return errors


def check_lean_paths() -> list[str]:
    errors: list[str] = []
    for doc_file in tracked_markdown_files():
        text = doc_file.read_text()
        for rel_path in sorted(set(LEAN_PATH_RE.findall(text))):
            if not (REPO_ROOT / rel_path).exists():
                rel_doc = doc_file.relative_to(REPO_ROOT)
                errors.append(f"Missing Lean path in {rel_doc}: {rel_path}")
    return errors


def check_module_docstrings() -> list[str]:
    errors: list[str] = []
    for source_root in (REPO_ROOT / "PolyFun", REPO_ROOT / "PolyFunTest"):
        for lean_file in source_root.rglob("*.lean"):
            if "/-!" not in lean_file.read_text():
                rel_path = lean_file.relative_to(REPO_ROOT)
                errors.append(f"Missing module docstring: {rel_path}")
    return errors


def main() -> int:
    all_errors: list[str] = []

    print("Checking CLAUDE.md symlink...")
    all_errors.extend(check_claude_symlink())

    print("Checking tracked markdown links...")
    all_errors.extend(check_markdown_links())

    print("Checking repository-rooted Lean paths...")
    all_errors.extend(check_lean_paths())

    print("Checking Lean module docstrings...")
    all_errors.extend(check_module_docstrings())

    if all_errors:
        print(f"\n{len(all_errors)} issue(s) found:\n")
        for err in all_errors:
            print(f"  - {err}")
        return 1

    print("\nAll documentation integrity checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
