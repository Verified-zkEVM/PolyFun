#!/usr/bin/env python3
"""Black-box local Notes CLI checks; every directory belongs to this test."""
import json
from pathlib import Path
import subprocess
import tempfile
from cli_test_support import conversation

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / "Examples/Notes/.lake/build/bin/polyfun-notes"


def run(*args, text="", success=True):
    result = subprocess.run([str(EXE), *map(str, args)], input=text,
                            text=True, capture_output=True, timeout=30)
    assert (result.returncode == 0) == success, result.stdout + result.stderr
    return result


def readme_session(directory):
    """The README's first session, followed by reopen and a cancelled preview."""
    output = conversation([EXE, "new", directory], [
        ("notes> ", "new"), ("Text (one line, preserved exactly): ", "buy tea"),
        ("notes> ", "edit"), ("Note ID: ", "0"), ("Expected version: ", "0"),
        ("Replacement text: ", "buy green tea"),
        ("notes> ", "list"), ("notes> ", "back"), ("notes> ", "live"),
        ("notes> ", "quit")]).replace("\r\n", "\n")
    for expected in ["Saved revision 1.", "Saved revision 2.",
                     "Revision 2\n[0 v1] buy green tea",
                     "Revision 1 (history; use live to edit)\n[0 v0] buy tea"]:
        assert expected in output, (expected, output)
    path = directory / "journal.json"
    assert json.loads(path.read_text())["commands"] == [
        {"create": {"text": "buy tea"}},
        {"edit": {"id": 0, "expectedVersion": 0, "text": "buy green tea"}}]
    before = path.read_bytes()
    output = conversation([EXE, "open", directory], [
        ("notes> ", "preview"), ("Note ID: ", "0"), ("Expected version: ", "1"),
        ("Replacement text: ", "buy oolong tea"), ("save / cancel: ", "cancel"),
        ("notes> ", "list"), ("notes> ", "quit")]).replace("\r\n", "\n")
    assert "Original:\nbuy green tea\nProposed:\nbuy oolong tea" in output, output
    assert "Cancelled; no command submitted." in output, output
    assert "Revision 2\n[0 v1] buy green tea" in output, output
    assert path.read_bytes() == before, "README preview changed the saved notebook"
    print("Notes README session: create, edit, browse, reopen and cancel: ok")


with tempfile.TemporaryDirectory(prefix="notes-cli-") as temporary:
    readme_session(Path(temporary) / "readme")
    assert "preview" in run("--help").stdout
    assert "directory" in run("new", "--help").stdout
    for args in [("unknown",), ("new",), ("open", "--unknown"), ("demo", "edit")]:
        run(*args, success=False)
    terminal_directory = Path(temporary) / "terminal"
    conversation([EXE, "new", terminal_directory], [
        ("notes> ", "new"), ("Text (one line, preserved exactly): ", "original"),
        ("notes> ", "preview"), ("Note ID: ", "0"), ("Expected version: ", "0"),
        ("Replacement text: ", "proposed"), ("save / cancel: ", "cancel"),
        ("notes> ", "quit")])
    assert len(json.loads((terminal_directory / "journal.json").read_text())["commands"]) == 1
    for model in ["free", "indexed", "system", "machine", "resumption", "tree"]:
        result = run("demo", model, text="  exact α  \nunused\n")
        assert result.stdout == "Note:   exact α  \n", (model, result.stdout)
        result = run("demo", "edit", model, text="0\n0\n  proposed α  \nsave\n")
        assert "First local note" in result.stdout and "demo does not persist" in result.stdout
    directory = Path(temporary) / "notebook"
    output = run("new", directory, text="new\n  first α  \nedit\n0\n0\nsecond\n"
                 "edit\n0\n0\nstale\nedit\n7\n0\nunknown\nback\nnew\nblocked\n"
                 "forward\nlive\nlist\nquit\n").stdout
    assert "Stale edit" in output and "No note has ID 7" in output
    assert "[0 v0]   first α  " in output and "[0 v1] second" in output
    path = directory / "journal.json"
    wire = json.loads(path.read_text())
    assert len(wire["commands"]) == 2
    assert wire["commands"][0]["create"]["text"] == "  first α  "
    before = path.read_bytes()
    for text in ["preview\n", "preview\n0\n1\nreplacement\n",
                 "preview\n0\n1\nreplacement\ncancel\nquit\n",
                 "preview\n0\n0\nstale\nquit\n", "preview\ninvalid\nquit\n"]:
        run("open", directory, text=text)
        assert path.read_bytes() == before, "unsaved preview changed journal bytes"
    run("open", directory, text="list\nhistory\n0\nforward\nlive\nedit\n0\n")
    assert path.read_bytes() == before, "browsing or incomplete input wrote data"
    run("new", directory, success=False)
    assert path.read_bytes() == before
    pending = directory / "journal.json.pending"
    pending.mkdir()
    result = run("open", directory, text="new\nfailed\n", success=False)
    assert "Save failed" in result.stdout and path.read_bytes() == before
    pending.rmdir()
    command = {"edit": {"id": 0, "expectedVersion": 1, "text": "a\nb\n  c  "}}
    run("open", directory, text=json.dumps(command) + "\nquit\n")
    assert len(json.loads(path.read_text())["commands"]) == 3
    # Unknown schemas and illegal commands are errors, not repair opportunities.
    wire["version"] = 99
    path.write_text(json.dumps(wire))
    run("open", directory, success=False)
    wire["version"] = 1
    wire["commands"].append({"edit": {"id": 99, "expectedVersion": 0, "text": "bad"}})
    path.write_text(json.dumps(wire))
    run("open", directory, success=False)

print("Notes CLI/filesystem: ok")
