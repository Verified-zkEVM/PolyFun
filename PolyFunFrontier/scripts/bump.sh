#!/usr/bin/env bash

# Move PolyFunFrontier to another cslib-frontier commit, with the Lean toolchain and the CSLib and
# Mathlib commits that commit records, then check the result.
#
#   PolyFunFrontier/scripts/bump.sh <full cslib-frontier commit>
#
# Only these three packages move (`lake update cslib-frontier cslib mathlib`); a bare `lake update`
# would also move PolyFun's other pins.

set -euo pipefail

sha="${1:?usage: bump.sh <full cslib-frontier commit>}"
if [[ ! "$sha" =~ ^[0-9a-f]{40}$ ]]; then
  echo "ERROR: give a full 40-character commit, not '$sha'." >&2
  exit 1
fi

cd "$(dirname "$0")/.."
raw="https://raw.githubusercontent.com/cslib-community/cslib-frontier/$sha"
toolchain="$(curl -fsSL "$raw/lean-toolchain")"
manifest="$(curl -fsSL "$raw/lake-manifest.json")"

rev_of() {
  python3 -c 'import json, sys
m = json.load(sys.stdin)
print(next(p["rev"] for p in m["packages"] if p["name"] == sys.argv[1]))' "$1" <<< "$manifest"
}
cslib_rev="$(rev_of cslib)"
mathlib_rev="$(rev_of mathlib)"

python3 - "$sha" "$cslib_rev" "$mathlib_rev" <<'PY'
import re, sys
from pathlib import Path
path = Path("lakefile.toml")
text = path.read_text()
for name, rev in zip(("cslib-frontier", "cslib", "mathlib"), sys.argv[1:]):
    pattern = rf'(name = "{re.escape(name)}"\n(?:[^\[]*?\n)?rev = ")[0-9a-f]+(")'
    text, count = re.subn(pattern, rf"\g<1>{rev}\g<2>", text)
    if count != 1:
        sys.exit(f"could not find exactly one rev for {name} in lakefile.toml")
path.write_text(text)
PY
printf '%s\n' "$toolchain" > lean-toolchain

echo "cslib-frontier $sha: $toolchain, cslib $cslib_rev, mathlib $mathlib_rev"
lake update cslib-frontier cslib mathlib
python3 scripts/check-pins.py
