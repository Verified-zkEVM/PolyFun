"""Exact identities for the official frontend and the reviewed compatibility patch.

Build identification is an external provenance check, not a Lean theorem about
Haskell. Unknown edits and mismatches between source and exporter are rejected.
"""

import hashlib
import subprocess
from pathlib import Path

from pins import CRYPTOL, ROOT

PATCH = ROOT / "exporter/patches/case-binder-types.patch"


def frontend_patches(source):
    def git(*args):
        # The canonical diff abbreviates object names to seven characters; a large
        # clone would otherwise choose a longer abbreviation and change the identity.
        return subprocess.run(["git", "-C", str(source), "-c", "core.abbrev=7", *args],
                              check=True, capture_output=True, text=True).stdout

    if git("rev-parse", "HEAD").strip() != CRYPTOL:
        raise ValueError("wrong Cryptol base revision")
    diff = git("diff", "--binary", "HEAD", "--")
    if not diff:
        return []
    # Git accepts empty context lines without a space prefix. Keep the stored
    # patch free of trailing whitespace; identify the exact canonical Git diff.
    portable = "\n".join("" if line == " " else line for line in diff.splitlines()) + "\n"
    if portable != PATCH.read_text():
        raise ValueError("Cryptol source edits differ from the reviewed compatibility patch")
    return [hashlib.sha256(diff.encode()).hexdigest()]


def check_frontend(bundle, source):
    if bundle["cryptol_revision"] != CRYPTOL:
        raise ValueError("unsupported Cryptol base revision")
    if bundle.get("frontend_patches", []) != frontend_patches(source):
        raise ValueError("exporter compatibility identity differs from the linked source checkout")


if __name__ == "__main__":
    import argparse
    import json

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    args = parser.parse_args()
    print(json.dumps({"cryptol_revision": CRYPTOL, "frontend_patches": frontend_patches(args.source)}))
