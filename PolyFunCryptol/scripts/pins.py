"""Pinned external revisions and the shared helpers of the Cryptol tooling.

Every external comparison names its exact Cryptol, upstream evaluator and Foundation
revisions here. Downstream bridges import this module from the package checkout
instead of restating the pins.
"""

import hashlib
import json
import subprocess
from pathlib import Path

CRYPTOL = "61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b"
UPSTREAM = "51405420cb90cf9959ca4349eea0ae8b77487855"
FOUNDATION = "7d0528bd998682788f4e23661f2829298f9e47db"

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
LEAN = REPO / ".lake/build/bin/polyfun-cryptol"


def run(*args):
    return subprocess.run(args, check=True, text=True, capture_output=True).stdout


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def verify_checkout(path, revision):
    if run("git", "-C", str(path), "rev-parse", "HEAD").strip() != revision:
        raise ValueError(f"wrong source revision: {path}")
    if run("git", "-C", str(path), "status", "--porcelain", "--untracked-files=no").strip():
        raise ValueError(f"modified tracked source files: {path}")
