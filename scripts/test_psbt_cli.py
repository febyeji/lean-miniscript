#!/usr/bin/env python3
"""Exercise the built PSBT CLI against the repository's pinned BIP vectors."""

import ast
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / ".lake/build/bin/psbt_cli"
FIXTURES = (ROOT / "LeanMiniscript/Psbt/Fixtures.lean").read_text()


def vectors(name):
    block = re.search(rf"^def {name} .*? := \[(.*?)^\]", FIXTURES, re.M | re.S)
    assert block is not None, f"missing fixture group: {name}"
    return ast.literal_eval("[" + block.group(1) + "]")


checks = 0


def run(*args, stdin=None, error=None):
    global checks
    result = subprocess.run(
        [str(CLI), *args], input=stdin, text=True, capture_output=True, timeout=60
    )
    checks += 1
    if error is None:
        assert result.returncode == 0, (args[0], result.returncode, result.stderr)
        assert result.stderr == "", result.stderr
    else:
        assert result.returncode == 2, (args[0], result.returncode, result.stderr)
        assert result.stdout == "", result.stdout
        assert error in result.stderr, result.stderr
    return result.stdout.strip()


roles = vectors("bip174Roles")
legacy = "sh(multi(2,029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f,02dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d7))"
witness = "sh(wsh(multi(2,03089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc,023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e73)))"

assert "usage:" in run("--", "--help")
assert "usage:" in run("finalize", "--help")
initial = run("inspect", roles[5][2])
assert "psbt_version: 0" in initial
assert "inputs: 2\noutputs: 2\nfinalized_inputs: 0" in initial
assert run("inspect", "--encoding", "hex", roles[5][1]) == initial
assert run("inspect", "-", stdin=roles[5][2] + "\n") == initial
assert "psbt_version: 2" in run("inspect", vectors("bip370Valid")[0][2])
assert run("extract", roles[6][2]) == roles[7][1]
assert run("extract", "--encoding", "hex", "-", stdin=roles[6][1] + "\n") == roles[7][1]

# Both real signatures are checked; the output reproduces the BIP174 final PSBT.
finalized = run("finalize", roles[5][2], "0=" + legacy, "1=" + witness)
assert finalized == roles[6][2]
assert run("extract", finalized) == roles[7][1]
partial = run("finalize", "--encoding", "hex", roles[5][1], "0=" + legacy)
status = run("inspect", partial)
assert "finalized_inputs: 1\ninput[0]: finalized\ninput[1]: unfinalized" in status
run("extract", partial, error="notFinalized")
assert run("finalize", "-", "1=" + witness, stdin=partial + "\n") == finalized
assert run("finalize", finalized, "0=" + legacy) == finalized

run("inspect", error="missing PSBT")
run("inspect", "--encoding", error="missing encoding")
run("inspect", "--encoding", "raw", roles[5][2], error="unknown encoding")
run("inspect", "%%%", error="PSBT parse error")
run("inspect", "--encoding", "hex", "0", error="invalid hex")
run("inspect", "--encoding", "hex", "zz", error="invalid hex")
run("inspect", roles[5][2], "extra", error="unexpected arguments")
run("finalize", roles[5][2], error="at least one INDEX=DESCRIPTOR")
run("finalize", roles[5][2], "bad", error="expected INDEX=DESCRIPTOR")
run("finalize", roles[5][2], "-1=" + legacy, error="invalid input index")
run("finalize", roles[5][2], "0=", error="missing descriptor")
run("finalize", roles[5][2], "0=invalid", error="input 0:")
run("finalize", roles[5][2], "2=" + legacy, error="index out of range")
run("finalize", roles[5][2], "0=" + legacy, "00=" + legacy, error="duplicate descriptor")
run("finalize", roles[5][2], "0=" + witness, error="input 0: finalization error")
run("extract", roles[5][2], error="notFinalized")
run("unknown", roles[5][2], error="unknown command")
print(f"PSBT CLI: {checks} subprocess checks passed")
