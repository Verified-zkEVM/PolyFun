#!/usr/bin/env python3
"""Recurring black-box checks for the read-only Pipeline executable."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / "Examples/Pipeline/.lake/build/bin/polyfun-pipeline"


def run(*args, code=0):
    result = subprocess.run([str(EXE), *map(str, args)], cwd=ROOT, capture_output=True,
                            text=True, timeout=30)
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    return result


def readme_session():
    """Run the README commands from the repository root, including the non-success case."""
    path = "Examples/Pipeline/lean-toolchain"
    before = (ROOT / path).read_bytes()
    expected = f"{path}: 25 bytes, 1 LF bytes\n"
    assert run("report", path).stdout == expected
    assert run("report", "--split-at", "3", path).stdout == expected
    paused = run("report", "--fuel", "3", path, code=2)
    assert paused.stdout == ""
    assert "Paused after 3 activations; report incomplete." in paused.stderr
    assert (ROOT / path).read_bytes() == before
    print("Pipeline README session: report, continuation and explicit pause: ok")


readme_session()
assert "report" in run("--help").stdout
assert "split-at" in run("report", "--help").stdout
for args in [("unknown",), ("report", "--fuel", "no"),
             ("report", "--unknown"), ("report", "--split-at", "-1")]:
    result = subprocess.run([str(EXE), *args], capture_output=True, text=True, timeout=30)
    assert result.returncode != 0, (args, result.stdout, result.stderr)
assert run("report").stdout == ""

with tempfile.TemporaryDirectory(prefix="pipeline-cli-") as temporary:
    directory = Path(temporary)
    empty = directory / "empty"
    unicode = directory / "unicode α"
    binary = directory / "binary"
    missing = directory / "missing"
    payloads = {empty: b"", unicode: "α\nβ\n".encode(), binary: b"\xff\x00\n"}
    for path, payload in payloads.items():
        path.write_bytes(payload)
    paths = [unicode, empty, unicode, binary]
    expected = "".join(f"{path}: {len(payloads[path])} bytes, "
                       f"{payloads[path].count(bytes([10]))} LF bytes\n" for path in paths)
    assert run("report", *paths).stdout == expected
    for cut in range(37):
        assert run("report", "--split-at", cut, *paths).stdout == expected, cut
    for fuel in [0, 1, 3, 8, 35]:
        paused = run("report", "--fuel", fuel, *paths, code=2)
        assert paused.stdout == "" and f"Paused after {fuel} activations" in paused.stderr
    failed = run("report", unicode, missing, empty, code=1)
    assert f"{missing}: ERROR:" in failed.stdout and f"{empty}: 0 bytes" in failed.stdout
    for path, payload in payloads.items():
        assert path.read_bytes() == payload, f"Pipeline modified {path}"
    assert set(directory.iterdir()) == set(payloads), "Pipeline created files"

print("Pipeline CLI: ordered byte reports, read errors, every split, no filesystem writes: ok")
