#!/usr/bin/env python3
"""Rebuild the two-module Atkinson proof and audit all requested declarations.

Prerequisite: run `lake update` and `lake exe cache get` in lean/ using the
pinned toolchain. This script always rebuilds both local proof modules.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
OUT = LEAN / ".lake" / "fredholm_atkinson_20261119"
OUT.mkdir(parents=True, exist_ok=True)
PIN = "0272bbe1c093d038d7257ab15306abd58245f9ff"
assert (LEAN / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc3"
mathlib_head = subprocess.check_output(
    ["git", "-C", str(LEAN / ".lake/packages/mathlib"), "rev-parse", "HEAD"], text=True).strip()
assert mathlib_head == PIN, (mathlib_head, PIN)
version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=LEAN, text=True).strip()
assert "4.35.0-rc3" in version, version
allowed = {"propext", "Classical.choice", "Quot.sound"}
modules = ["SharedCore.FredholmCompactParametrix", "SharedCore.FredholmAtkinson"]
audit = {"lean": version, "mathlib_commit": mathlib_head, "modules": {}, "axioms": {}}
for module in modules:
    source = LEAN.joinpath(*module.split(".")).with_suffix(".lean")
    output = LEAN / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    log = OUT / (module + ".log")
    start = time.monotonic()
    print("Compiling", module, flush=True)
    with log.open("w") as stream:
        result = subprocess.run(["lake", "env", "lean", "-j1", "-M8192", "-o", str(output), str(source)],
                                cwd=LEAN, stdout=stream, stderr=subprocess.STDOUT)
    text = log.read_text()
    if result.returncode:
        print(text)
        sys.exit(result.returncode)
    assert "sorryAx" not in text and "Lean.ofReduceBool" not in text, module
    found = {}
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]|'([^']+)' does not depend on any axioms", text):
        name = match.group(1) or match.group(3)
        axioms = {x.strip() for x in (match.group(2) or "").split(",") if x.strip()}
        found[name] = axioms
    requested = re.findall(r"^#print axioms (\S+)", source.read_text(), re.M)
    assert requested, module
    for name in requested:
        candidates = [(full, axioms) for full, axioms in found.items()
                      if full == name or full.endswith("." + name)]
        assert len(candidates) == 1, (name, candidates)
        full, axioms = candidates[0]
        assert axioms <= allowed, (full, axioms)
        audit["axioms"][full] = sorted(axioms)
        print("success:", full)
    audit["modules"][module] = {
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "olean_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
        "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
        "elapsed_seconds": time.monotonic() - start,
    }
(OUT / "audit.json").write_text(json.dumps(audit, indent=2) + "\n")
print("success:", len(audit["axioms"]), "declarations checked; standard axioms only.")
