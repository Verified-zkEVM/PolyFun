#!/usr/bin/env python3
"""Whole-module retention, diagnosis and scope mutations.

The committed module canaries run everywhere. With `--report`, the actual utility,
CRC, matrix, property and ring exports from an external corpus run are checked too.
"""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from pins import LEAN, REPO, ROOT
from corpus import STAGES, STATUS, blockers, diagnose_module, elaborate_module, graph, open_report
from test_source import nodes


def check_materialized(checked):
    """Kernel-check all emitted bodies, including constraint-proof replay."""
    source = """module
public import PolyFunCryptol.Translation.ModuleElaboration
import PolyFunCryptol.Model.Types
import PolyFunCryptol.Model.Numeric
import PolyFunCryptol.Model.Length
import PolyFunCryptol.Model.Scheme
public section
open Cryptol Cryptol.Polymorphic Cryptol.Translation
"""
    for index, body in enumerate(checked["bodies"]):
        source += (f"def body{index} : Term {body['scope']} ({body['context_schemes']}) "
                   f"({body['scheme']}) := {body['term']}\n")
    with tempfile.TemporaryDirectory(prefix="cryptol-materialized-") as temporary:
        path = Path(temporary) / "Materialized.lean"
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=REPO,
                                capture_output=True, text=True, timeout=120)
        assert result.returncode == 0, result.stdout + result.stderr
        assert "warning:" not in result.stdout, result.stdout


def scope_check(lean, bundle):
    with tempfile.TemporaryDirectory(prefix="cryptol-module-") as temporary:
        path = Path(temporary) / "module.json"
        path.write_text(json.dumps(bundle))
        result = subprocess.run([str(lean), "source", "modules", str(path)],
                                capture_output=True, text=True)
        return result.returncode, json.loads(result.stdout)


def with_file(bundle, action):
    with tempfile.TemporaryDirectory(prefix="cryptol-module-") as temporary:
        path = Path(temporary) / "module.json"
        path.write_text(json.dumps(bundle))
        return action(path)


def check_mutations(lean, mutations):
    for original, mutate in mutations:
        mutant = deepcopy(original)
        mutate(mutant)
        code, report = scope_check(lean, mutant)
        assert code != 0, report
        if isinstance(report, list):
            assert len(report) == len(mutant["modules"]) + len(mutant["interfaces"]), \
                "validation stopped at first failure"


def canaries(lean):
    """Offline whole-module checks on the committed two-module fixture."""
    path = ROOT / "artifacts/modules/canaries.json"
    manifest = json.loads((ROOT / "artifacts/references/manifest.json").read_text())
    assert hashlib.sha256(path.read_bytes()).hexdigest() == \
        manifest["module_canaries"]["bundle_sha256"]
    assert hashlib.sha256((ROOT / "fixtures/ModuleCanaries.cry").read_bytes()).hexdigest() == \
        manifest["module_canaries"]["source_sha256"]
    bundle = json.loads(path.read_text())
    code, report = scope_check(lean, bundle)
    assert code == 0 and all(r["scope"]["status"] == "accepted" for r in report), report
    assert not any(d["unresolved_dependencies"] for d in graph(bundle)["declarations"])
    loops = elaborate_module(lean, path, "ModuleLoops", code=True)
    assert loops["expression_typing"] == "accepted", loops
    assert loops["semantic_import"] == "conditional-model" and loops["shared_declarations"] == 3
    assert {p["name"] for p in loops["primitive_requirements"]} >= {"(Cryptol::-)", "(Cryptol::>)"}
    check_materialized(loops)
    rejected = elaborate_module(lean, path, "ModuleCanaries")
    assert rejected["status"] == "rejected", rejected
    diagnosis = diagnose_module(lean, path, "ModuleCanaries")
    assert diagnosis["status"] == "diagnosed", diagnosis
    assert not any(p["failure"] for p in diagnosis["primitives"]), diagnosis
    found = {b["declaration"]: b["message"] for b in blockers(diagnosis)}
    expected = {"ModuleCanaries::swap": "value type 2-tuple",
                "ModuleCanaries::small": "constructor list",
                "ModuleCanaries::field": "value type record",
                "ModuleCanaries::bump": "constructor comprehension"}
    assert found.keys() == expected.keys(), found
    assert all(expected[d] in m for d, m in found.items()), found
    passed = {g["declarations"][0] for g in diagnosis["groups"] if not g["failure"]}
    # A failed body keeps its declared scheme, so its dependents remain checkable.
    assert {"ModuleLoops::loop", "ModuleCanaries::settle", "ModuleCanaries::smallFirst"} <= passed

    def mutate_loop(type_preserving):
        mutant = deepcopy(bundle)
        module = next(m for m in mutant["modules"] if m["provenance"]["name"] == "ModuleLoops")
        condition = next(n for n in nodes(module["groups"]) if n.get("tag") == "if")
        if type_preserving:
            # Returning the state has the loop's type but removes its self call.
            replacement = deepcopy(condition["args"][2])
            condition.clear()
            condition.update(replacement)
            next(d for d in module["declarations"]
                 if d["name"]["text"] == "loop")["dependencies"] = []
        else:
            # A type parameter cannot be used as Bit; this still passes scope checking.
            condition["args"][0] = deepcopy(condition["args"][2])
        assert scope_check(lean, mutant)[0] == 0
        return with_file(mutant, lambda p: elaborate_module(lean, p, "ModuleLoops", code=True))

    failed = mutate_loop(False)
    assert failed["status"] == "rejected" and "scheme mismatch" in failed["message"], failed
    changed = mutate_loop(True)
    assert changed["expression_typing"] == "accepted" and changed["bodies"] != loops["bodies"]
    mutations = [
        (bundle, lambda b: b["primitive_fallbacks"][0][1].update(id=99999999)),
        (bundle, lambda b: b.update(cryptol_revision="untrusted")),
        (bundle, lambda b: b["modules"][0]["provenance"].update(path="../escape.cry")),
        (bundle, lambda b: b["modules"][0].update(declarations=[])),
        (bundle, lambda b: b.update(frontend_patches=["unreviewed"])),
        (bundle, lambda b: b["modules"][1]["declarations"][0].update(dependencies=[])),
        (bundle, lambda b: b["modules"].append(deepcopy(b["modules"][0]))),
    ]
    check_mutations(lean, mutations)
    return len(mutations)


def foundation(lean, report):
    """Checks on actual Foundation exports retained by an external corpus run."""
    corpus = json.loads((report / "corpus.json").read_text())
    assert corpus["exporter_sha256"] == hashlib.sha256((ROOT / "exporter/Main.hs").read_bytes()).hexdigest()
    census_path = report / "foundation-inventory.json"
    if census_path.is_file():
        census = json.loads(census_path.read_text())
        assert [e["path"] for e in corpus["entries"]] == [e["path"] for e in census["entries"]]
        public = [d for e in corpus["entries"] for d in e["graph"]["declarations"] if d["public"]]
        expected = [d for e in census["entries"] for m in e.get("modules", []) for d in m["exports"]]
        assert len(public) == len(expected)
        assert sum(d["property"] for d in public) == sum(d["property"] for d in expected)
    assert all(d["stages"][s] == "not-attempted"
               for e in corpus["entries"] for d in e["graph"]["declarations"]
               for s in STAGES if s not in {"expression_typing", "semantic_import"})
    assert all(e["lean_exit"] == 0 for e in corpus["entries"])
    assert all(r["link"] == "accepted" for e in corpus["entries"] for r in e["link_reports"])
    assert all(len(e["semantic_attempts"]) == len(e["own_modules"]) for e in corpus["entries"])
    accepted = {s["module"] for e in corpus["entries"] for s in e["semantic_attempts"]
                if s["result"].get("expression_typing") == "accepted"}
    assert {"shared::algebra::Ring::Primitive::Functor",
            "shared::algebra::Ring::Integer::Test"} <= accepted
    # Accepted modules have no diagnosed blockers, and rejected ones have at least one.
    for e in corpus["entries"]:
        for s in e["semantic_attempts"]:
            assert bool(blockers(s["diagnosis"])) != (s["module"] in accepted), s["module"]
    status = json.loads(STATUS.read_text())
    assert status["instances"] == sum(len(e["semantic_attempts"]) for e in corpus["entries"])
    assert status["accepted"] == len(accepted)
    utility, crc = [json.loads((report / (name + ".json")).read_text()) for name in ["list", "crc"]]
    for bundle in (utility, crc):
        code, scopes = scope_check(lean, bundle)
        assert code == 0 and all(r["scope"]["status"] == "accepted" for r in scopes), scopes
        assert all(r["semantic_import"] == "not-attempted" for r in scopes)
        assert not any(d["unresolved_dependencies"] for d in graph(bundle)["declarations"])
        reference = next(m for m in bundle["modules"]
                         if m["provenance"]["name"] == "Cryptol::Reference")
        assert {"pmult", "pdiv", "pmod", "foldl", "foldWhile", "scanl", "iterate"} <= {
            e["declaration"]["name"]["text"] for e in reference["exports"]}
    assert json.loads((ROOT / "artifacts/elaboration.json").read_text()) == open_report(lean, report)
    imperative = elaborate_module(lean, report / "list.json",
                                  "shared::common::utils::Imperative", code=True)
    assert imperative["expression_typing"] == "accepted" and imperative["shared_declarations"] == 2
    assert imperative["source_correspondence"] == "not-established"
    modules = {m["provenance"]["name"]: m for m in utility["modules"]}
    assert all("shared::common::utils::" + name in modules
               for name in ["List", "Sort", "Enum", "Imperative"])
    assert any(n.get("tag") == "case" for n in nodes(utility))
    crc_module = next(m for m in crc["modules"] if m["provenance"]["name"] == "shared::CRC::Main")
    assert len(crc_module["type_parameters"]) == 1 and len(crc_module["value_parameters"]) == 7
    assert {"CRCUpdate", "CRCRunning"} <= {
        e["declaration"]["name"]["text"] for e in crc_module["exports"]}

    def remove_parameter(bundle):
        next(m for m in bundle["modules"] if m["provenance"]["name"] ==
             "shared::CRC::Main")["value_parameters"] = []

    def corrupt_body(bundle):
        # Mutate retained groups, not the redundant export display copy.
        module = next(m for m in bundle["modules"] if m["provenance"]["name"] ==
                      "shared::common::utils::Enum")
        node = next(n for n in nodes(module["groups"]) if n.get("tag") == "case")
        node["args"][1].append(deepcopy(node["args"][1][0]))

    def nominal_in_body(bundle):
        module = next(m for m in bundle["modules"] if m["provenance"]["name"] ==
                      "shared::common::utils::List")
        node = next(n for n in nodes(module["groups"]) if n.get("tag") == "nominal")
        node["args"][0]["id"] = 99999999

    check_mutations(lean, [(utility, nominal_in_body), (utility, corrupt_body),
                           (crc, remove_parameter)])
    matrix = json.loads((report / "matrix.json").read_text())
    assert scope_check(lean, matrix)[0] == 0
    old = json.loads((ROOT / "artifacts/regressions/case-binder-unpatched.json").read_text())
    module = next(m for m in matrix["modules"] if m["provenance"] == old["module"])
    target = old["declaration"]["name"]
    for group in module["groups"]:
        ds = group["args"] if group["tag"] == "nonrecursive" else group["args"][0]
        for index, declaration in enumerate(ds):
            if declaration["name"] == target:
                ds[index] = old["declaration"]
    code, scopes = scope_check(lean, matrix)
    assert code != 0 and any("unbound type parameter 5177" in r["scope"].get("message", "")
                             for r in scopes), scopes
    # Interface contracts are checked even when they are not the selected entry module.
    matrix = json.loads((report / "matrix.json").read_text())
    interface = next(i for i in matrix["interfaces"] if i["type_parameters"])
    interface["type_parameters"] = []
    assert scope_check(lean, matrix)[0] != 0
    properties = elaborate_module(lean, report / "properties.json",
                                  "shared::common::properties", code=True)
    assert properties["semantic_import"] == "conditional-model"
    assert properties["shared_declarations"] == 8
    check_materialized(properties)
    assert {p["name"] for p in properties["primitive_requirements"]} == {
        "(Cryptol::==)", "(Cryptol::!=)", "Cryptol::True"}
    ring = elaborate_module(lean, report / "ring-primitive.json",
                            "shared::algebra::Ring::Primitive::Functor", code=True)
    assert ring["semantic_import"] == "conditional-model" and ring["shared_declarations"] == 7
    assert ring["module_type_parameters"] == 1 and len(ring["primitive_requirements"]) == 7
    check_materialized(ring)
    scalar = elaborate_module(lean, report / "field-scalar.json",
                              "shared::algebra::Field::Operators::Scalar")
    assert scalar["semantic_import"] == "parameterized-model"
    assert scalar["shared_declarations"] == 5 and not scalar["primitive_requirements"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, default=LEAN)
    parser.add_argument("--report", type=Path,
                        help="external corpus report directory written by corpus.py --all")
    args = parser.parse_args()
    mutations = canaries(args.lean)
    print(f"Module canaries: 2 modules, kernel-replayed loop bodies, 4 diagnosed blockers, "
          f"{mutations} scope mutations and 2 typing/meaning mutations")
    if args.report:
        foundation(args.lean, args.report)
        print("Foundation modules: corpus/census agreement, diagnoses, utility/CRC retention, "
              "Imperative typing, 8 property and 7 ring bodies with kernel-replayed constraints")


if __name__ == "__main__":
    main()
