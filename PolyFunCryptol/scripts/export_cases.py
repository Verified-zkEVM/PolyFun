#!/usr/bin/env python3
"""Export the language-level reference cases through the pinned typed-AST exporter.

The numeric and class cases compare Lean's numeric semantics and class resolution
with the pinned frontend. The importer canaries are a small Cryptol fixture whose
exact export is quoted for kernel-checked acceptance tests, and so is the
tutorial fixture. The module canaries are a two-module fixture for offline
whole-module checks and diagnoses. The committed files are inputs to Lean
validation, not typing certificates.
"""

import argparse
import json
import tempfile
from pathlib import Path

from pins import CRYPTOL, FOUNDATION, LEAN, REPO, ROOT, canonical, digest, run, verify_checkout
from frontend import frontend_patches, check_frontend
from quote_reference import quote_bundle

ARTIFACTS = ROOT / "artifacts" / "references"
CANARY_SOURCE = ROOT / "fixtures/ImportCanaries.cry"
CANARY_QUOTATION = REPO / "PolyFunCryptolTest/Translation/ImportedSource.lean"
TUTORIAL_SOURCE = ROOT / "fixtures/Tutorial.cry"
TUTORIAL_QUOTATION = REPO / "PolyFunCryptolTest/Tutorial/MixSource.lean"
MODULE_SOURCE = ROOT / "fixtures/ModuleCanaries.cry"
MODULE_BUNDLE = ROOT / "artifacts/modules/canaries.json"
CANARY_ROOTS = ("capture", "recordSelect", "tupleSelect", "higherOrder", "mapped", "streamMap",
                "folded", "(guarded : [0]Integer -> Integer)", "(guarded : [3]Integer -> Integer)")


def quote_canaries(canaries):
    return quote_bundle(canaries, namespace="Cryptol.Tests.ImportedCanariesSource",
                        artifact="PolyFunCryptol/artifacts/references/import-canaries.json",
                        title="Quoted importer canaries",
                        driver="PolyFunCryptol/scripts/export_cases.py")


def quote_tutorial(tutorial):
    return quote_bundle(tutorial, namespace="Cryptol.Tests.Tutorial.MixSource",
                        artifact="PolyFunCryptol/artifacts/references/tutorial.json",
                        title="Quoted tutorial source",
                        driver="PolyFunCryptol/scripts/export_cases.py")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", required=True, type=Path)
    parser.add_argument("--foundation", required=True, type=Path)
    parser.add_argument("--cryptol-source", required=True, type=Path)
    parser.add_argument("--lean", type=Path, default=LEAN)
    parser.add_argument("--check", action="store_true", help="require byte-identical committed artifacts")
    args = parser.parse_args()
    verify_checkout(args.foundation, FOUNDATION)
    patches = frontend_patches(args.cryptol_source)
    numeric = json.loads(run(str(args.exporter), "--numeric"))
    if numeric != json.loads(run(str(args.lean), "model", "numeric")):
        raise ValueError("Lean numeric semantics differs from pinned InfNat")
    with tempfile.TemporaryDirectory(prefix="cryptol-cases-") as temporary:
        classes = json.loads(run(str(args.exporter), "--classes"))
        case_file = Path(temporary) / "classes.json"
        case_file.write_bytes(canonical(classes))
        if classes != json.loads(run(str(args.lean), "source", "constraints", str(case_file))):
            raise ValueError("Lean class resolution differs from the pinned class solver")
        canaries = json.loads(run(str(args.exporter), str(args.foundation), str(CANARY_SOURCE),
                                  *CANARY_ROOTS))
        check_frontend(canaries, args.cryptol_source)
        if canaries["cryptol_revision"] != CRYPTOL:
            raise ValueError("exporter reports an unsupported Cryptol revision")
        canary_data = canonical(canaries)
        checked = Path(temporary) / "canaries.json"
        checked.write_bytes(canary_data)
        reports = json.loads(run(str(args.lean), "source", "elaborate", str(checked)))
        if not reports or any(r["status"] != "typed" for r in reports):
            raise ValueError("typed import failed: canaries")
        tutorial = json.loads(run(str(args.exporter), str(args.foundation), str(TUTORIAL_SOURCE),
                                  "mix", "clear"))
        check_frontend(tutorial, args.cryptol_source)
        tutorial_data = canonical(tutorial)
        checked.write_bytes(tutorial_data)
        reports = json.loads(run(str(args.lean), "source", "elaborate", str(checked)))
        if not reports or any(r["status"] != "typed" for r in reports):
            raise ValueError("typed import failed: tutorial")
        modules = json.loads(run(str(args.exporter), "--module-bundle", str(MODULE_SOURCE.parent),
                                 str(MODULE_SOURCE)))
        check_frontend(modules, args.cryptol_source)
        module_data = canonical(modules)
        checked.write_bytes(module_data)
        scopes = json.loads(run(str(args.lean), "source", "modules", str(checked)))
        if any(r["scope"]["status"] != "accepted" for r in scopes):
            raise ValueError("module canaries failed scope and kind validation")
    canary_lean = quote_canaries(canaries)
    tutorial_lean = quote_tutorial(tutorial)
    manifest = {
        "schema_version": 1, "cryptol_revision": CRYPTOL, "foundation_revision": FOUNDATION,
        "frontend_patches": patches,
        "exporter_sha256": digest((ROOT / "exporter/Main.hs").read_bytes()),
        "numeric_cases": len(numeric), "class_cases": len(classes),
        "numeric_sha256": digest(canonical(numeric)), "class_sha256": digest(canonical(classes)),
        "canaries": {"roots": len(canaries["roots"]), "bundle_sha256": digest(canary_data),
                     "lean_sha256": digest(canary_lean),
                     "source_sha256": digest(CANARY_SOURCE.read_bytes())},
        "tutorial": {"roots": len(tutorial["roots"]), "bundle_sha256": digest(tutorial_data),
                     "lean_sha256": digest(tutorial_lean),
                     "source_sha256": digest(TUTORIAL_SOURCE.read_bytes())},
        "module_canaries": {"bundle_sha256": digest(module_data),
                            "modules": [r["module"] for r in scopes],
                            "source_sha256": digest(MODULE_SOURCE.read_bytes())},
        "trust_boundary": ["Pinned Cryptol parser, renamer, type checker and module elaborator",
                           "Haskell typed-AST serialization and provenance collection"],
    }
    outputs = {ARTIFACTS / "numeric-cases.json": canonical(numeric),
               ARTIFACTS / "class-cases.json": canonical(classes),
               ARTIFACTS / "import-canaries.json": canary_data,
               ARTIFACTS / "cryptol-license.txt": (args.cryptol_source / "LICENSE").read_bytes(),
               ARTIFACTS / "manifest.json": (json.dumps(manifest, indent=2) + "\n").encode(),
               ARTIFACTS / "tutorial.json": tutorial_data,
               TUTORIAL_QUOTATION: tutorial_lean,
               MODULE_BUNDLE: module_data,
               CANARY_QUOTATION: canary_lean}
    for path, contents in outputs.items():
        if args.check:
            if not path.is_file() or path.read_bytes() != contents:
                raise ValueError(f"stale reference artifact: {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(contents)
    print(f"{len(numeric)} numeric cases; {len(classes)} class cases; "
          f"{len(canaries['roots'])} typed canaries; {len(scopes)} scoped canary modules")


if __name__ == "__main__":
    main()
