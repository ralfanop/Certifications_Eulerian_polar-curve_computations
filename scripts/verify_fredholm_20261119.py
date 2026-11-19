#!/usr/bin/env python3
"""Compile the exact local dependency closure, one Lean process at a time.

Run after `cd lean; lake update; lake exe cache get`, with the pinned toolchain
on PATH. Outputs and a hash-based incremental ledger stay under lean/.lake.
No source placeholders or untrusted native arithmetic are accepted in the
new theorem axiom reports.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1] / "lean"
AUDIT = ROOT / ".lake" / "fredholm_audit_20261119"
AUDIT.mkdir(parents=True, exist_ok=True)
TARGETS = sys.argv[1:] or [
    "SpecialImaginaryPoint.FredholmCauchyEstimates",
    "SpecialImaginaryPoint.V14119Priority3UniversalFredholmDerivativeVariation",
]
LEDGER = AUDIT / "build_ledger.json"
ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT, text=True).strip()
order, seen, dependencies = [], set(), {}

def source(module):
    return ROOT.joinpath(*module.split(".")).with_suffix(".lean")

def visit(module):
    if module in seen or not source(module).exists():
        return
    seen.add(module)
    imports = re.findall(r"^(?:public )?import\s+([\w.]+)", source(module).read_text(), re.M)
    dependencies[module] = [name for name in imports if source(name).exists()]
    for name in imports:
        visit(name)
    order.append(module)

for module in TARGETS:
    visit(module)

print(version, flush=True)
print(f"Dependency closure: {len(order)} modules; one process; 8192 MB limit.", flush=True)
for i, module in enumerate(order, 1):
    digest = hashlib.sha256(source(module).read_bytes()).hexdigest()
    deps = {name: ledger[name]["fingerprint"] for name in dependencies[module]}
    fingerprint = hashlib.sha256(json.dumps([version, digest, deps], sort_keys=True).encode()).hexdigest()
    out = ROOT / ".lake" / "build" / "lib" / "lean" / Path(*module.split(".")).with_suffix(".olean")
    log = AUDIT / (module + ".log")
    if out.exists() and log.exists() and ledger.get(module, {}).get("fingerprint") == fingerprint:
        print(f"[{i}/{len(order)}] verified cache {module}", flush=True)
        continue
    out.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    print(f"[{i}/{len(order)}] compiling {module}", flush=True)
    with log.open("w") as stream:
        result = subprocess.run(["lake", "env", "lean", "-j1", "-M8192", "-o", str(out), str(source(module))],
                                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - started
    if result.returncode:
        print(log.read_text(), flush=True)
        print(f"FAILED {module}: exit {result.returncode}, {elapsed:.1f}s", flush=True)
        sys.exit(result.returncode)
    ledger[module] = {"fingerprint": fingerprint, "source_sha256": digest,
                      "elapsed_seconds": elapsed, "lean_version": version,
                      "olean_sha256": hashlib.sha256(out.read_bytes()).hexdigest()}
    LEDGER.write_text(json.dumps(ledger, indent=2) + "\n")
    print(f"[{i}/{len(order)}] compiled {module} ({elapsed:.1f}s)", flush=True)

allowed = {"propext", "Classical.choice", "Quot.sound"}
reports = {}
for module in TARGETS:
    log = (AUDIT / (module + ".log")).read_text()
    names = re.findall(r"^#print axioms (\S+)", source(module).read_text(), re.M)
    found = {}
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]|'([^']+)' does not depend on any axioms", log):
        name = match.group(1) or match.group(3)
        axioms = {x.strip() for x in (match.group(2) or "").split(",") if x.strip()}
        found[name] = axioms
    for name in names:
        matches = [(full, axioms) for full, axioms in found.items()
                   if full == name or full.endswith("." + name)]
        assert len(matches) == 1, f"Missing or ambiguous axiom report: {name}"
        full, axioms = matches[0]
        assert axioms <= allowed, f"Unexpected axioms for {full}: {axioms - allowed}"
        reports[full] = sorted(axioms)
    assert "sorryAx" not in log and "Lean.ofReduceBool" not in log, module

(AUDIT / "axiom_audit.json").write_text(json.dumps(reports, indent=2) + "\n")
print(f"success: {len(reports)} requested theorem reports; standard axioms only.", flush=True)
