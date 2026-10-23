#!/usr/bin/env python3
"""Inventory every tracked Foundation module through the official Cryptol loader.

This is discovery, not a semantic coverage claim. In particular, public properties,
parameterized modules, nested functors and nominal types remain visible even when
Lean cannot yet import their definitions. No Cryptol source parser is implemented here.
"""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess

from pins import CRYPTOL, FOUNDATION, ROOT, canonical, run, verify_checkout

STAGES = ("lean_typing", "semantic_import", "native_view", "independent_equivalence",
          "property_proofs")


def tags(value):
    if isinstance(value, dict):
        if "tag" in value:
            yield value["tag"]
        for child in value.values():
            yield from tags(child)
    elif isinstance(value, list):
        for child in value:
            yield from tags(child)


def inspect(exporter, foundation, path):
    relative = path.relative_to(foundation).as_posix()
    record = {"path": relative, "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "stages": {stage: "not-attempted" for stage in STAGES}}
    try:
        result = subprocess.run([str(exporter), "--module", str(foundation), str(path)],
                                capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired:
        return record | {"frontend": "timeout", "export": "not-produced"}
    if result.returncode:
        # Preserve the diagnostic, but remove checkout-specific paths for reproducibility.
        return record | {"frontend": "rejected", "export": "not-produced",
                         "diagnostic": result.stderr.replace(str(foundation), "$foundation").strip()}
    bundle = json.loads(result.stdout)
    assert bundle["format"] == "cryptol-module-inventory" and bundle["version"] == 1
    all_modules = bundle["modules"] + [dict(m, interface=True, exports=[], nominal_exports=[],
        nested_functors=[], nested_signatures=[]) for m in bundle["interfaces"]]
    own = [m for m in all_modules if m["provenance"]["path"] == relative]
    if not own:
        raise ValueError(f"loader did not return the requested module: {relative}")
    record.update(frontend="accepted", export="exported", modules=[])
    for module in own:
        declarations = []
        for export in module["exports"]:
            d = export["declaration"]
            declarations.append({"name": d["name"]["origin"], "schema": d["schema"],
                "property": export["property"], "location": export["location"],
                "constructors": dict(sorted(Counter(tags(d["definition"])).items()))})
        record["modules"].append({"name": module["provenance"]["name"],
            "interface": module.get("interface", False),
            "type_parameters": module["type_parameters"],
            "value_parameters": module["value_parameters"],
            "constraints": module["constraints"], "exports": declarations,
            **{key: module[key] for key in ("type_exports", "nominal_exports",
                                            "nested_functors", "nested_signatures")}})
    record["dependencies"] = sorted(set(m["provenance"]["path"] for m in all_modules
                                        if m not in own))
    return record


def validate(data):
    """The census cannot silently promote exporter success to a semantic certificate."""
    assert data["schema_version"] == 1
    assert data["foundation_revision"] == FOUNDATION and data["cryptol_revision"] == CRYPTOL
    entries = data["entries"]
    paths = [e["path"] for e in entries]
    assert paths == sorted(set(paths)) and len(paths) == data["tracked_modules"]
    for entry in entries:
        path = Path(entry["path"])
        assert not path.is_absolute() and ".." not in path.parts and path.suffix == ".cry"
        assert entry["stages"] == {stage: "not-attempted" for stage in STAGES}
        assert entry["frontend"] in {"accepted", "rejected", "timeout"}
        assert (entry["export"] == "exported") == (entry["frontend"] == "accepted")
        assert len(entry["sha256"]) == 64 and all(c in "0123456789abcdef" for c in entry["sha256"])
    return {"modules": len(entries), "exported": sum(e["export"] == "exported" for e in entries),
            "public_values": sum(len(m["exports"]) for e in entries for m in e.get("modules", [])),
            "properties": sum(d["property"] for e in entries for m in e.get("modules", [])
                              for d in m["exports"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", required=True, type=Path)
    parser.add_argument("--foundation", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path, help="complete inventory to write")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--compare", type=Path, help="require byte-identity with this inventory")
    args = parser.parse_args()
    verify_checkout(args.foundation, FOUNDATION)
    files = sorted(p for p in run("git", "-C", str(args.foundation), "ls-files").splitlines()
                   if p.endswith(".cry"))
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        entries = list(pool.map(lambda p: inspect(args.exporter, args.foundation,
                                                  args.foundation / p), files))
    data = {"schema_version": 1, "foundation_revision": FOUNDATION, "cryptol_revision": CRYPTOL,
            "exporter_sha256": hashlib.sha256((ROOT / "exporter/Main.hs").read_bytes()).hexdigest(),
            "tracked_modules": len(files), "entries": entries}
    summary = validate(data)
    contents = canonical(data)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_bytes(contents)
    if args.compare and args.compare.read_bytes() != contents:
        raise ValueError(f"Foundation inventory differs from {args.compare}")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
