#!/usr/bin/env python3
"""Retain whole modules and report each import stage without conflating them.

The official exporter owns parsing and source elaboration. Lean recomputes value
dependencies and checks decoding, scopes, kinds and linking. This driver records their results
and a declaration graph; it does not infer semantic acceptance from either.

The complete report and the selected module bundles go to a report directory. The
committed status summary keeps, for every module instance, the independent blockers
of typed elaboration and the language features they require.
"""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

from pins import CRYPTOL, FOUNDATION, LEAN, ROOT, canonical, run, verify_checkout
from frontend import frontend_patches, check_frontend

SELECTED = {"shared/common/utils/List.cry": "list",
            "shared/CRC/Main.cry": "crc",
            "shared/algebra/Field/Zp/Test.cry": "matrix",
            "shared/common/properties.cry": "properties",
            "shared/algebra/Field/Operators/Scalar.cry": "field-scalar",
            "shared/algebra/Ring/Primitive/Functor.cry": "ring-primitive"}
STAGES = ("expression_typing", "semantic_import", "native_view", "execution",
          "source_correspondence", "property_proof")
OPEN_MODULES = [("list", name) for name in ["Cryptol::Reference"] + [
    "shared::common::utils::" + name for name in ["List", "Sort", "Imperative", "Enum"]]] + [
    ("crc", "shared::CRC::Main")]


def elaborate_module(lean, path, module, *, code=False):
    result = subprocess.run([str(lean), "source", "module-code" if code else "module-elaborate",
                             str(path), module], capture_output=True, text=True, timeout=120)
    report = json.loads(result.stdout)
    if result.returncode and report.get("status") != "rejected":
        raise ValueError(f"module elaborator failed without a diagnostic: {result.stderr}")
    return report


STATUS = ROOT / "artifacts/foundation-status.json"
ELABORATION = ROOT / "artifacts/elaboration.json"
TYPES = {"record": "type:record", "TC TCIntMod": "type:Z", "TC TCRational": "type:Rational",
         "TC TCFloat": "type:Float", "TC TCArray": "type:Array"}


def feature(message):
    """The language feature a diagnosis message asks for."""
    if "partial numeric evaluation" in message:
        return "partial-numeric"
    if "scheme mismatch" in message:
        return "scheme-equality"
    if "unresolved constraint entailment" in message:
        return "entailment"
    if m := re.search(r"unsupported open expression constructor (\w+)", message):
        return "expr:" + m.group(1)
    if m := re.search(r"value type (.+?) requires an aggregate", message):
        return "type:tuple" if m.group(1).endswith("-tuple") else TYPES.get(m.group(1), "type:nominal")
    if m := re.search(r"unsupported (?:structural class|open constraint) (.+)$", message):
        return "constraint:" + m.group(1).split()[-1]
    return "other"


def blockers(diagnosis):
    """Independent failures; dependents of a failed scheme are not counted again."""
    if diagnosis.get("status") != "diagnosed":
        return [{"declaration": "<module>", "message": diagnosis.get("message", "")}]
    failed = {p["name"] for p in diagnosis["primitives"] if p["failure"]}
    failed |= {n for g in diagnosis["groups"] if g["failure"] for n in g["declarations"]}
    found = [{"declaration": p["name"], "message": p["failure"]}
             for p in diagnosis["primitives"] if p["failure"]]
    for group in diagnosis["groups"]:
        message = group["failure"]
        if not message:
            continue
        if (m := re.search(r"unbound typed value (\S+)", message)) and m.group(1) in failed:
            continue
        found.append({"declaration": group["declarations"][0], "message": message})
    return found


def summarize(report):
    """Per-instance status, blockers and features, plus feature-level unblock counts."""
    instances, messages = [], {}
    for entry in report["entries"]:
        for attempt in entry.get("semantic_attempts", []):
            result = attempt["result"]
            found = blockers(attempt["diagnosis"])
            for b in found:
                messages.setdefault(b["declaration"], b["message"])
            record = {"path": entry["path"], "module": attempt["module"],
                      "status": result.get("expression_typing", "rejected"),
                      "features": sorted({feature(b["message"]) for b in found}),
                      "blockers": sorted({b["declaration"] for b in found})}
            if "semantic_import" in result:
                record["semantic_import"] = result["semantic_import"]
            instances.append(record)
    needs = Counter(f for i in instances for f in i["features"])
    order, have, remaining = [], set(), set(needs)
    while remaining:
        best = max(sorted(remaining), key=lambda f: (
            sum(set(i["features"]) <= have | {f} for i in instances), needs[f]))
        have.add(best)
        remaining.remove(best)
        order.append({"feature": best,
                      "accepted": sum(set(i["features"]) <= have for i in instances)})
    return {"schema_version": 1, "cryptol_revision": report["cryptol_revision"],
            "foundation_revision": report["foundation_revision"],
            "frontend_patches": report["frontend_patches"],
            "exporter_sha256": report["exporter_sha256"],
            "meaning": "Typed elaboration coverage; not semantic or source-preservation claims",
            "files": len(report["entries"]), "instances": len(instances),
            "accepted": sum(i["status"] == "accepted" for i in instances),
            "features": dict(sorted(needs.items(), key=lambda kv: (-kv[1], kv[0]))),
            "unblock_order": order,
            "blockers": {d: {"feature": feature(m), "message": m}
                         for d, m in sorted(messages.items())},
            "entries": instances}


def diagnose_module(lean, path, module):
    """Every independent blocker, continuing past failing primitive schemes and bodies."""
    result = subprocess.run([str(lean), "source", "module-diagnose", str(path), module],
                            capture_output=True, text=True, timeout=120)
    return json.loads(result.stdout)


def open_report(lean, artifacts):
    """Attempt every selected whole module, retaining each independent blocker."""
    return {"version": 1, "entries": [
        {"bundle": stem + ".json", "module": module,
         "result": elaborate_module(lean, artifacts / (stem + ".json"), module)}
        for stem, module in OPEN_MODULES]}


def declarations(group):
    return group["args"] if group["tag"] == "nonrecursive" else group["args"][0]


def source_id(module, info):
    """Diagnostic origin including the instantiated module; never a linking key."""
    return {"path": module["provenance"]["path"], "sha256": module["provenance"]["sha256"],
            "instance": module["provenance"]["name"],
            "qualified_name": info["name"]["origin"],
            **info["source_key"]}


def graph(bundle):
    """Resolve dependency edges in this bundle, preserving simultaneous groups."""
    if (bundle["format"], bundle["version"], bundle["cryptol_revision"]) != \
            ("cryptol-module-bundle", 3, CRYPTOL):
        raise ValueError("unsupported module bundle")
    nodes, identities, constructors, parameters = [], {}, {}, {}
    for module in bundle["modules"]:
        metadata = {d["name"]["id"]: d for d in module["declarations"]}
        exported = {e["declaration"]["name"]["id"] for e in module["exports"]}
        for group_index, group in enumerate(module["groups"]):
            for d in declarations(group):
                i = d["name"]["id"]
                if i in identities:
                    raise ValueError(f"duplicate declaration identity: {i}")
                info = metadata[i]
                identity = source_id(module, info)
                identities[i] = identity
                nodes.append({"bundle_id": i, "source": identity, "name": d["name"]["origin"],
                    "module": module["provenance"]["name"], "group": group_index,
                    "recursive_group": group["tag"] == "recursive", "public": i in exported,
                    "property": info["property"], "schema": d["schema"],
                    "definition": d["definition"]["tag"],
                    "dependencies": [n["id"] for n in info["dependencies"]],
                    "stages": {stage: "not-attempted" for stage in STAGES}})
        for nominal in module["nominal_types"]:
            tag, args = nominal["definition"]["tag"], nominal["definition"]["args"]
            names = ([args[0]] if tag == "struct" else
                     [c["name"] for c in args[0]] if tag == "enum" else [])
            for name in names:
                constructors[name["id"]] = name["origin"]
        for parameter in module["value_parameters"]:
            parameters[parameter["name"]["id"]] = parameter["name"]["origin"]
    known = identities.keys() | constructors.keys() | parameters.keys()
    for node in nodes:
        node["unresolved_dependencies"] = sorted(set(node["dependencies"]) - known)
    redirects = {a["id"]: b["id"] for a, b in bundle["primitive_fallbacks"]}
    if any(i not in identities or j not in identities for i, j in redirects.items()):
        raise ValueError("unresolved primitive fallback")
    for node in nodes:
        if node["bundle_id"] in redirects:
            node["reference_fallback"] = redirects[node["bundle_id"]]
    return {"declarations": nodes, "constructors": constructors, "parameters": parameters}


def inspect(exporter, lean, foundation, cryptol, relative):
    path = foundation / relative
    record = {"path": relative, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    try:
        result = subprocess.run([str(exporter), "--module-bundle", str(foundation), str(path)],
                                capture_output=True, text=True, timeout=120)
        if result.returncode:
            return record | {"frontend": "rejected", "diagnostic": result.stderr.replace(
                str(foundation), "$foundation").strip()}, None
        bundle = json.loads(result.stdout)
        check_frontend(bundle, cryptol)
        for module in bundle["modules"] + bundle["interfaces"]:
            provenance = module["provenance"]
            source = provenance["path"]
            if source.startswith("$builtin/"):
                actual = cryptol / "lib" / (source[9:].replace("::", "/") + ".cry")
            elif source.startswith("$") or Path(source).is_absolute() or ".." in Path(source).parts:
                raise ValueError(f"unaccounted source path: {source}")
            else:
                actual = foundation / source
            if hashlib.sha256(actual.read_bytes()).hexdigest() != provenance["sha256"]:
                raise ValueError(f"source digest mismatch: {source}")
        # Interfaces can be entry points too; they are retained, not promoted to definitions.
        if not any(m["provenance"]["path"] == relative
                   for m in bundle["modules"] + bundle["interfaces"]):
            raise ValueError("requested module disappeared from the loaded environment")
        data = graph(bundle)
        own = {m["provenance"]["name"] for m in bundle["modules"]
               if m["provenance"]["path"] == relative}
        # Each source owns its declarations. Referenced modules are represented
        # by stable origins, avoiding 135 copies of the entire Prelude graph.
        all_declarations = data["declarations"]
        data["declarations"] = [d for d in all_declarations if d["module"] in own]
        needed = {i for d in data["declarations"] for i in d["dependencies"]}
        data["dependency_origins"] = {d["bundle_id"]: d["source"] for d in all_declarations
                                      if d["bundle_id"] in needed}
        data["constructors"] = {i: n for i, n in data["constructors"].items() if i in needed}
        data["parameters"] = {i: n for i, n in data["parameters"].items() if i in needed}
        with tempfile.TemporaryDirectory(prefix="cryptol-module-") as temporary:
            artifact = Path(temporary) / "module.json"
            artifact.write_bytes(canonical(bundle))
            checked = subprocess.run([str(lean), "source", "modules", str(artifact)],
                                     capture_output=True, text=True, timeout=120)
            linked, attempts = [], []
            if checked.returncode == 0:
                for module in sorted(own):
                    result = subprocess.run([str(lean), "source", "module-link", str(artifact), module],
                                            capture_output=True, text=True, timeout=120)
                    linked.append(json.loads(result.stdout))
                    attempts.append({"module": module,
                                     "result": elaborate_module(lean, artifact, module),
                                     "diagnosis": diagnose_module(lean, artifact, module)})
        report = json.loads(checked.stdout)
        record.update(frontend="accepted", body_retention="exported", graph=data,
                      lean_report=report, lean_exit=checked.returncode,
                      link_reports=linked, semantic_attempts=attempts)
        for attempt in attempts:
            if attempt["result"].get("expression_typing") == "accepted":
                for declaration in data["declarations"]:
                    if declaration["module"] == attempt["module"]:
                        declaration["stages"].update(expression_typing="accepted",
                            semantic_import=attempt["result"]["semantic_import"])
        if isinstance(report, list):
            record["own_modules"] = sorted(own)
            record["body_retention"] = "decoded"
            record["scope_blockers"] = [r for r in report if r["scope"]["status"] != "accepted"]
        return record, bundle
    except (subprocess.TimeoutExpired, ValueError, KeyError) as error:
        return record | {"pipeline": "failed", "diagnostic": str(error)}, None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", required=True, type=Path)
    parser.add_argument("--foundation", required=True, type=Path)
    parser.add_argument("--cryptol-source", required=True, type=Path)
    parser.add_argument("--lean", type=Path, default=LEAN)
    parser.add_argument("--out", required=True, type=Path,
                        help="directory receiving the complete report and selected module bundles")
    parser.add_argument("--all", action="store_true", help="continue across every tracked source")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--compare", type=Path,
                        help="require byte-identical outputs with an existing report directory")
    parser.add_argument("--check", action="store_true",
                        help="require the committed status summary and open report to be current")
    args = parser.parse_args()
    verify_checkout(args.foundation, FOUNDATION)
    patches = frontend_patches(args.cryptol_source)
    files = sorted(p for p in run("git", "-C", str(args.foundation), "ls-files").splitlines()
                   if p.endswith(".cry")) if args.all else sorted(SELECTED)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda p: inspect(args.exporter, args.lean, args.foundation,
                                                  args.cryptol_source, p), files))
    output = args.out
    output.mkdir(parents=True, exist_ok=True)
    written = []

    def write(path, data):
        path.write_bytes(canonical(data))
        written.append(path.name)

    for path, (record, bundle) in zip(files, results):
        if path in SELECTED and bundle is not None:
            write(output / (SELECTED[path] + ".json"), bundle)
    report = {"version": 1, "cryptol_revision": CRYPTOL, "foundation_revision": FOUNDATION,
              "frontend_patches": patches,
              "exporter_sha256": hashlib.sha256((ROOT / "exporter/Main.hs").read_bytes()).hexdigest(),
              "entries": [r for r, _ in results]}
    write(output / ("corpus.json" if args.all else "selected.json"), report)
    write(output / "elaboration.json", open_report(args.lean, output))
    if args.all:
        committed = {STATUS: summarize(report), ELABORATION: json.loads(
            (output / "elaboration.json").read_text())}
        for path, data in committed.items():
            contents = (json.dumps(data, indent=1, sort_keys=True) + "\n").encode()
            if args.check:
                if path.read_bytes() != contents:
                    raise ValueError(f"stale committed corpus summary: {path}")
            else:
                path.write_bytes(contents)
    if args.compare:
        stale = [name for name in written
                 if (args.compare / name).read_bytes() != (output / name).read_bytes()]
        if stale:
            raise ValueError(f"outputs differ from {args.compare}: {stale}")
    failed = [path for path, (record, _) in zip(files, results)
              if path in SELECTED and record.get("lean_exit") != 0]
    if failed:
        raise ValueError(f"required utility/CRC closure failed: {failed}; corpus report was retained")
    print(json.dumps({"files": len(files), "decoded": sum(r.get("body_retention") == "decoded"
        for r, _ in results), "scoped": sum(r.get("lean_exit") == 0 for r, _ in results)}, sort_keys=True))


if __name__ == "__main__":
    main()
