#!/usr/bin/env python3
"""Check that PolyFunFrontier's pins agree with the cslib-frontier commit it requires.

cslib-frontier publishes no tags and pins CSLib by commit, with Mathlib coming through CSLib. A
package that requires it must use the same Lean toolchain and the same CSLib and Mathlib commits,
or Lake builds cslib-frontier against versions it was never checked with. This script compares,
offline, after `lake update` or `lake exe cache get` has materialized the dependencies:

* `lakefile.toml` revisions against `lake-manifest.json` (no drift between the two files);
* `lean-toolchain` against cslib-frontier's at the pinned commit;
* every package both manifests list (CSLib, Mathlib and Mathlib's own dependencies) against
  cslib-frontier's manifest.

Run from anywhere: paths are resolved from this file's location.
"""

import json
import re
import sys
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent.parent
FRONTIER = PACKAGE / ".lake" / "packages" / "cslib-frontier"
PINNED = ("cslib-frontier", "cslib", "mathlib")
# Packages this one owns and cslib-frontier does not list.
OWN = {"PolyFun", "cslib-frontier"}


def lakefile_revs(text):
    revs = {}
    for block in re.split(r"^\[\[require\]\]\s*$", text, flags=re.M)[1:]:
        name = re.search(r'^name\s*=\s*"([^"]+)"', block, flags=re.M)
        rev = re.search(r'^rev\s*=\s*"([^"]+)"', block, flags=re.M)
        if name and rev:
            revs[name.group(1)] = rev.group(1)
    return revs


def manifest_revs(path):
    # Lake writes names that are not Lean identifiers escaped, as in `«cslib-frontier»`.
    data = json.loads(path.read_text())
    return {p["name"].strip("«»"): p.get("rev") for p in data["packages"]}


def main():
    errors = []
    if not FRONTIER.is_dir():
        print(f"error: {FRONTIER} is missing; run `lake update` or `lake exe cache get` first.",
              file=sys.stderr)
        return 2

    declared = lakefile_revs((PACKAGE / "lakefile.toml").read_text())
    ours = manifest_revs(PACKAGE / "lake-manifest.json")
    theirs = manifest_revs(FRONTIER / "lake-manifest.json")

    for name in PINNED:
        if declared.get(name) != ours.get(name):
            errors.append(f"lakefile.toml pins {name} at {declared.get(name)}, "
                          f"but lake-manifest.json records {ours.get(name)}")

    toolchain = (PACKAGE / "lean-toolchain").read_text().strip()
    frontier_toolchain = (FRONTIER / "lean-toolchain").read_text().strip()
    if toolchain != frontier_toolchain:
        errors.append(f"lean-toolchain is {toolchain}, cslib-frontier's is {frontier_toolchain}")

    for name in sorted((set(ours) & set(theirs)) - OWN):
        if ours[name] != theirs[name]:
            errors.append(f"{name} is at {ours[name]}, cslib-frontier's manifest has {theirs[name]}")

    if errors:
        for e in errors:
            print(f"error: {e}", file=sys.stderr)
        print("Move the pins together with scripts/bump.sh <cslib-frontier commit>.", file=sys.stderr)
        return 1
    print(f"✓ PolyFunFrontier pins agree with cslib-frontier {ours['cslib-frontier'][:12]} "
          f"({toolchain}, {len(set(ours) & set(theirs) - OWN)} shared packages)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
