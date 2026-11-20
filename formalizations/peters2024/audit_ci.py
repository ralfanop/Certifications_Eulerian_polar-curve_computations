"""Reject missing declarations and any nonstandard axioms."""
import pathlib
import re
import sys

mode, log_path = sys.argv[1:]
log = pathlib.Path(log_path).read_text()
names = ["Peters2024", "BorsukCore", "BisectionRepairs", "HomotopyRealization", "WoodhouseContinuity", "SurfaceHomotopy", "FeynmanKernelContinuity", "WoodhouseIncidence", "WoodhouseJadczyk", "JadczykNullGeodesic"] if mode == "base" else ["BorsukBridge", "PetersApplications"]
expected = set()
for name in names:
    expected.update(re.findall(r"^#print axioms ([\w.]+)\s*$", pathlib.Path(name + ".lean").read_text(), re.M))
observed = {}
for match in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log):
    observed[match.group(1)] = {a.strip() for a in (match.group(2) or "").split(",") if a.strip()}
assert expected, "no audit declarations found"
assert expected <= observed.keys(), f"missing audit declarations: {expected - observed.keys()}"
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name in expected:
    assert observed[name] <= allowed, (name, observed[name] - allowed)
assert "sorryAx" not in log
print(f"PASS: {len(expected)} exact declarations; standard axioms only")
