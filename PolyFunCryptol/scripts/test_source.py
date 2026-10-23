#!/usr/bin/env python3
"""Scope/kind acceptance, typed import, malformed-source rejection and case provenance."""

from copy import deepcopy
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from pins import CRYPTOL, FOUNDATION, LEAN, REPO, ROOT, verify_checkout

ARTIFACTS = ROOT / "artifacts/references"


def run(path, mode="inspect"):
    result = subprocess.run([str(LEAN), "source", mode, str(path)],
                            text=True, capture_output=True)
    return result.returncode, json.loads(result.stdout)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)

    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rejected(mutations, *, typing):
    """Malformed bundles fail scope checking; ill-typed ones pass it and fail elaboration."""
    with tempfile.TemporaryDirectory(prefix="cryptol-rejections-") as temporary:
        path = Path(temporary) / "mutated.json"
        for label, mutant in mutations:
            path.write_text(json.dumps(mutant))
            code, report = run(path)
            if typing:
                assert code == 0 and report["status"] == "scoped", (label, report)
                code, report = run(path, "elaborate")
            assert code != 0 and report["status"] == "rejected", (label, report)


def cases(manifest):
    numeric = json.loads((ARTIFACTS / "numeric-cases.json").read_text())
    classes = json.loads((ARTIFACTS / "class-cases.json").read_text())
    assert sha256(ARTIFACTS / "numeric-cases.json") == manifest["numeric_sha256"]
    assert sha256(ARTIFACTS / "class-cases.json") == manifest["class_sha256"]
    assert len(numeric) == manifest["numeric_cases"] and len(classes) == manifest["class_cases"]
    assert numeric == json.loads(subprocess.check_output([str(LEAN), "model", "numeric"]))
    assert classes == json.loads(subprocess.check_output([
        str(LEAN), "source", "constraints", str(ARTIFACTS / "class-cases.json")]))
    print(f"Reference cases: {len(numeric)} numeric and {len(classes)} class cases agree")


def canaries(manifest):
    path = ARTIFACTS / "import-canaries.json"
    assert sha256(path) == manifest["canaries"]["bundle_sha256"]
    assert sha256(REPO / "PolyFunCryptolTest/Translation/ImportedSource.lean") == \
        manifest["canaries"]["lean_sha256"]
    assert sha256(ROOT / "fixtures/ImportCanaries.cry") == manifest["canaries"]["source_sha256"]
    code, report = run(path, "elaborate")
    assert code == 0 and all(r["status"] == "typed" for r in report), report
    bundle = json.loads(path.read_bytes())

    def single(root, change):
        mutant = deepcopy(bundle)
        mutant["roots"] = [mutant["roots"][root]]
        change(mutant)
        return mutant

    def wrong_record(b):
        fields = b["roots"][0]["schema"]["body"]["args"][1][0]["args"][0]
        fields[1][0] = "wrong"

    def tuple_for_record(b):
        arg = b["roots"][0]["schema"]["body"]["args"][1][0]
        fields = arg["args"][0]
        arg.update(tag="tuple", args=[len(fields), [t for _, t in fields]])

    def first(b, predicate):
        return next(n for n in nodes(b["groups"]) if predicate(n))

    typing = [
        ("record labels", single(1, wrong_record)),
        ("tuple/record carrier collision", single(1, tuple_for_record)),
        ("comprehension length", single(4, lambda b: first(b, lambda n: n.get("tag") ==
            "comprehension")["args"].__setitem__(0, {"tag": "num", "args": ["2"]}))),
        ("local declaration annotation", single(0, lambda b: first(b, lambda n: n.get(
            "name", {}).get("text") == "saved")["schema"].update(
                body={"tag": "con", "args": ["TC TCBit", []]}))),
        ("root result type", single(3, lambda b: b["roots"][0]["schema"].update(
            body={"tag": "con", "args": ["TC TCInteger", []]}))),
        ("lambda annotation", single(3, lambda b: first(b, lambda n: n.get("tag") ==
            "abs")["args"].__setitem__(1, {"tag": "con", "args": ["TC TCBit", []]}))),
        ("unsupported primitive", single(6, lambda b: [n.update(text="unsupported",
            origin="Cryptol::unsupported") for n in nodes(b) if n.get("text") == "foldl"])),
        ("application argument", single(3, lambda b: b["roots"][0].update(expression={
            "tag": "app", "args": [deepcopy(b["roots"][0]["expression"]),
                                   deepcopy(b["roots"][0]["expression"])]}))),
    ]
    rejected(typing, typing=True)

    def add(label, change):
        altered = deepcopy(bundle)
        change(altered)
        malformed.append((label, altered))

    malformed = []
    add("format", lambda b: b.update(format="unversioned"))
    add("version", lambda b: b.update(version=2))
    add("frontend pin", lambda b: b.update(cryptol_revision="0" * 40))
    add("empty roots", lambda b: b.update(roots=[]))
    add("missing dependency", lambda b: b["groups"].pop(0))
    add("duplicate binding", lambda b: b["groups"].append(deepcopy(b["groups"][0])))
    add("reordered dependencies", lambda b: b["groups"].reverse())
    add("empty recursive group", lambda b: b["groups"].append({"tag": "recursive", "args": [[]]}))
    add("unbound root", lambda b: b["roots"][0].update(expression={"tag": "var", "args": [
        {"id": 99999999, "text": "missing", "origin": "missing"}]}))
    add("unknown constructor", lambda b: next(n for n in nodes(b) if n.get("tag") == "con")
        ["args"].__setitem__(0, "TC NotCryptol"))
    add("numeric underflow literal", lambda b: next(n for n in nodes(b) if n.get("tag") == "num"
        and n.get("args"))["args"].__setitem__(0, "-1"))
    add("source traversal", lambda b: b["modules"][0].update(path="../Cryptol.cry"))
    add("source digest", lambda b: b["modules"][0].update(sha256="not-a-digest"))
    rejected(malformed, typing=False)
    print(f"Importer canaries: {len(bundle['roots'])} typed roots, {len(malformed)} malformed "
          f"bundles and {len(typing)} ill-typed terms rejected")


def external_canaries(cryptol, foundation):
    from test_evaluators import observe

    verify_checkout(foundation, FOUNDATION)
    assert "Git commit " + CRYPTOL in subprocess.check_output([str(cryptol), "--version"], text=True)
    code, imported = run(ARTIFACTS / "import-canaries.json", "elaborate")
    assert code == 0
    observations = [
        (0, "4 5", "4 5", "9"),
        (1, "{flag=False, value=7}", "(False, (7, ()))", "7"),
        (2, "(9, False)", "(9, (False, ()))", "9"),
        (3, r"(\x -> x+1) (\x -> x*2) 10", r"(\x -> x+1) (\x -> x*2) 10", "21"),
        (4, "[1,2,3]", "[1,2,3]", "[2, 3, 4]"),
        (5, "([0...] : [inf]Integer) @ (12 : Integer)",
            "([0...] : [inf]Integer) @ (12 : Integer)", "13"),
        (6, "[1,2,3]", "[1,2,3]", "6"),
        (7, "[]", "[]", "0"),
        (8, "[4,5,6]", "[4,5,6]", "4"),
    ]
    for i, source_args, imported_args, expected in observations:
        for mode in ("normal", "reference"):
            for expression, args in ((imported[i]["root"], source_args),
                                     (imported[i]["source"], imported_args)):
                observe(cryptol, f"({expression}) {args}", expected, mode, foundation,
                        ROOT / "fixtures/ImportCanaries.cry")
    print("Imported canaries: 36 original/lowered normal/reference observations passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cryptol", type=Path)
    parser.add_argument("--foundation", type=Path)
    args = parser.parse_args()
    if bool(args.cryptol) != bool(args.foundation):
        parser.error("--cryptol and --foundation must be provided together")
    manifest = json.loads((ARTIFACTS / "manifest.json").read_text())
    assert sha256(ROOT / "exporter/Main.hs") == manifest["exporter_sha256"]
    cases(manifest)
    canaries(manifest)
    if args.cryptol:
        external_canaries(args.cryptol, args.foundation)


if __name__ == "__main__":
    main()
