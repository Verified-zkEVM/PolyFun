#!/usr/bin/env python3
"""Check PolyFun documentation integrity.

Checks:
1. `CLAUDE.md` exists and is a symlink to `AGENTS.md`.
2. Local markdown links and heading anchors in tracked docs resolve.
3. Repository-rooted Lean paths in those documents resolve even when they
   are written as code rather than markdown links.
4. Lean excerpts match marked regions of checked tutorial modules.
5. Every library, example and consumer Lean module has a module docstring.

Exit code 0 if all checks pass, 1 otherwise.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections.abc import Iterator
from pathlib import Path
from urllib.parse import unquote

REPO_ROOT = Path(__file__).resolve().parent.parent
CLAUDE_PATH = REPO_ROOT / "CLAUDE.md"
AGENTS_PATH = REPO_ROOT / "AGENTS.md"

# The set of tracked markdown files we walk for link checking. Top-level
# repo docs plus everything under `docs/`. Keep this list in sync with the
# maintenance contract in `docs/README.md`.
TRACKED_PATHS = [
    "AGENTS.md",
    "CONTRIBUTING.md",
    "README.md",
    "REFERENCES.md",
    "docs",
    "Examples",
    "test/DocumentationConsumer",
    "test/ParliamentConsumer",
]

MARKDOWN_LINK_RE = re.compile(r"(?<!!)\[[^\]]+\]\(([^)]+)\)")
LEAN_PATH_RE = re.compile(
    r"(?<![A-Za-z0-9_./])"
    r"((?:PolyFun|ToCslib|ComplexityBackends|PolyFunTest|Examples)/(?:"
    r"[A-Za-z0-9_./-]+\.lean|"
    r"[A-Za-z0-9_./-]*\{[A-Za-z0-9_./, -]+\}(?:[A-Za-z0-9_./-]*\.lean)?"
    r"))"
    r"(?![A-Za-z0-9_./-])"
)
MODULE_COMMAND_RE = re.compile(r"^module[ \t]*$", re.MULTILINE)
IMPORT_COMMAND_RE = re.compile(
    r"(?:(?:public|private|meta)[ \t]+)*import(?:[ \t]+all)?[ \t]+[^\n]+"
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
    target = raw_target.strip().strip("`").strip("<>")
    if not target or "://" in target or target.startswith("mailto:"):
        return None

    path_part = unquote(target.split("#", 1)[0].strip())
    if not path_part:
        return source_file

    if path_part.startswith("/"):
        return (REPO_ROOT / path_part.lstrip("/")).resolve()
    return (source_file.parent / path_part).resolve()


def outside_fences(text: str) -> str:
    """Remove fenced code so examples do not create headings or links."""
    lines: list[str] = []
    fence = ""
    for line in text.splitlines():
        marker = re.match(r"^\s{0,3}(`{3,}|~{3,})", line)
        if fence:
            if re.match(r"^\s{0,3}" + re.escape(fence[0]) +
                        "{" + str(len(fence)) + r",}\s*$", line):
                fence = ""
        elif marker:
            fence = marker.group(1)
        else:
            lines.append(line)
    return "\n".join(lines)


def markdown_anchors(text: str) -> set[str]:
    """GitHub-style heading slugs (including duplicates) and explicit anchors."""
    text = outside_fences(text)
    anchors = set(re.findall(r'<[^>]+\b(?:id|name)=[\'"]([^\'"]+)[\'"]', text))
    used: set[str] = set()
    lines = text.splitlines()
    for index, line in enumerate(lines):
        heading = re.match(r"^ {0,3}#{1,6}\s+(.+?)(?:\s+#+)?\s*$", line)
        if heading:
            title = heading.group(1)
        elif index + 1 < len(lines) and line.strip() and re.fullmatch(
                r" {0,3}(?:=+|-+)\s*", lines[index + 1]):
            title = line.strip()
        else:
            continue
        title = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", title)
        title = re.sub(r"<[^>]+>", "", title).lower()
        slug = "".join(c for c in title if c.isalnum() or c in " _-").replace(" ", "-")
        candidate = slug
        suffix = 0
        while candidate in used:
            suffix += 1
            candidate = f"{slug}-{suffix}"
        used.add(candidate)
        anchors.add(candidate)
    return anchors


def markdown_link_errors(doc_file: Path) -> list[str]:
    """Check local paths and Markdown fragments, including same-page links."""
    errors: list[str] = []
    text = outside_fences(doc_file.read_text())
    targets = MARKDOWN_LINK_RE.findall(text)
    targets += re.findall(r"^\s{0,3}\[[^\]]+\]:\s*(\S+)", text, re.MULTILINE)
    for raw_target in targets:
        resolved = resolve_link(doc_file, raw_target)
        if resolved is None:
            continue
        if not resolved.exists():
            errors.append(f"Broken link: {raw_target}")
        elif "#" in raw_target and resolved.suffix.lower() == ".md":
            fragment = unquote(raw_target.split("#", 1)[1].rstrip(">"))
            if fragment and fragment not in markdown_anchors(resolved.read_text()):
                errors.append(f"Broken heading anchor: {raw_target}")
    return errors


def check_markdown_links() -> list[str]:
    return [f"{doc.relative_to(REPO_ROOT)}: {error}"
            for doc in tracked_markdown_files()
            for error in markdown_link_errors(doc)]


def example_errors(text: str, repo_root: Path = REPO_ROOT) -> list[str]:
    """Compare marked excerpts with imports plus a named region of Lean source."""
    errors: list[str] = []
    for marker in re.finditer(r"<!--\s*lean-example:\s*(.*?)\s*-->", text):
        target = marker.group(1)
        source_path, separator, region = target.partition("#")
        source = (repo_root / source_path).resolve()
        if not separator or not region or not source.is_relative_to(repo_root.resolve()) or not source.is_file():
            errors.append(f"Invalid Lean example source: {target}")
            continue
        code = source.read_text()
        begin, end = f"-- BEGIN {region}", f"-- END {region}"
        if code.count(begin) != 1 or code.count(end) != 1 or code.index(begin) > code.index(end):
            errors.append(f"Missing or ambiguous Lean example region: {target}")
            continue
        imports = re.findall(r"^public (import [^\n]+)$", code, re.MULTILINE)
        body = code.split(begin, 1)[1].split(end, 1)[0].strip()
        expected = "\n".join(imports) + "\n\n" + body
        excerpt = re.match(r"\s*```lean\n(.*?)\n```", text[marker.end():], re.DOTALL)
        if excerpt is None or excerpt.group(1).strip() != expected.strip():
            errors.append(f"Lean excerpt differs from checked source: {target}")
    return errors


def check_examples() -> list[str]:
    return [f"{doc.relative_to(REPO_ROOT)}: {error}"
            for doc in tracked_markdown_files()
            for error in example_errors(doc.read_text(), REPO_ROOT)]


def expand_lean_path(expression: str) -> list[str]:
    """Expand one literal or single-brace repository-rooted Lean path."""
    if "{" not in expression:
        return [expression]
    prefix, choices_and_suffix = expression.split("{", 1)
    choices, suffix = choices_and_suffix.split("}", 1)
    return [prefix + choice.strip() + suffix for choice in choices.split(",")]


def lean_paths(text: str) -> Iterator[str]:
    """Yield every literal Lean path represented in documentation text."""
    for expression in LEAN_PATH_RE.findall(text):
        yield from expand_lean_path(expression)


def missing_lean_paths(text: str, repo_root: Path = REPO_ROOT) -> list[str]:
    """Return documented Lean paths that do not exist under ``repo_root``."""
    return sorted(
        rel_path
        for rel_path in set(lean_paths(text))
        if not (repo_root / rel_path).exists()
    )


def check_lean_paths() -> list[str]:
    errors: list[str] = []
    for doc_file in tracked_markdown_files():
        text = doc_file.read_text()
        for rel_path in missing_lean_paths(text):
            rel_doc = doc_file.relative_to(REPO_ROOT)
            errors.append(f"Missing Lean path in {rel_doc}: {rel_path}")
    return errors


def has_module_docstring(text: str) -> bool:
    """Check for a module docstring in the standard post-import prologue slot."""
    module_match = MODULE_COMMAND_RE.search(text)
    if module_match is None:
        return False

    offset = module_match.end()
    while True:
        whitespace = re.match(r"\s*", text[offset:])
        assert whitespace is not None
        offset += whitespace.end()
        if text.startswith("/-!", offset):
            return True
        import_match = IMPORT_COMMAND_RE.match(text, offset)
        if import_match is None:
            return False
        offset = import_match.end()


def check_module_docstrings() -> list[str]:
    errors: list[str] = []
    for root_name in ("PolyFun", "ToCslib", "ComplexityBackends", "PolyFunTest", "Examples",
                      "test/DocumentationConsumer", "test/ParliamentConsumer"):
        source_root = REPO_ROOT / root_name
        lean_files = [p for p in source_root.rglob("*.lean") if ".lake" not in p.parts]
        umbrella = REPO_ROOT / f"{root_name}.lean"
        # PolyFun.lean is a generated import index without a module docstring.
        if root_name != "PolyFun" and umbrella.is_file():
            lean_files.append(umbrella)
        for lean_file in lean_files:
            if not has_module_docstring(lean_file.read_text()):
                rel_path = lean_file.relative_to(REPO_ROOT)
                errors.append(f"Missing module docstring: {rel_path}")
    entry = REPO_ROOT / "PolyFunParliamentMain.lean"
    if entry.exists() and not has_module_docstring(entry.read_text()):
        errors.append("Missing module docstring: PolyFunParliamentMain.lean")
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

    print("Checking Lean documentation excerpts...")
    all_errors.extend(check_examples())

    if all_errors:
        print(f"\n{len(all_errors)} issue(s) found:\n")
        for err in all_errors:
            print(f"  - {err}")
        return 1

    print("\nAll documentation integrity checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
