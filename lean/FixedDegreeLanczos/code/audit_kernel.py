"""Validate complete declaration audits against the shipped Lean audit sources."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def check(source_name, log_name):
    source = (ROOT / "lean" / source_name).read_text()
    expected = re.findall(r"^#print axioms (\S+)", source, re.M)
    log = (ROOT / "results" / log_name).read_text()
    if re.search(r"error:|sorryAx|Lean\.ofReduceBool", log):
        raise RuntimeError(f"Forbidden dependency or compiler error in {log_name}")
    found = {}
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
        name, axioms = match.groups()
        found[name] = {s.strip() for s in axioms.split(",") if s.strip()}
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", log):
        found[match.group(1)] = set()
    if set(expected) != set(found):
        raise RuntimeError({"missing": sorted(set(expected)-set(found)),
                            "unexpected": sorted(set(found)-set(expected))})
    for name, axioms in found.items():
        if not axioms <= ALLOWED:
            raise RuntimeError(f"Unexpected axiom in {name}: {axioms - ALLOWED}")
    return {"source": source_name, "log": log_name, "declarations": len(found),
            "axioms_used": sorted(set().union(*found.values()))}


if __name__ == "__main__":
    results = [check("V033Verification.lean", "V033Verification.log"),
               check("V033FullVerification.lean", "V033FullVerification.log")]
    report = {"status": "passed", "audits": results,
              "total_declarations": sum(r["declarations"] for r in results),
              "allowed_axioms": sorted(ALLOWED)}
    (ROOT / "results" / "KERNEL_AUDIT_SUMMARY.json").write_text(
        json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))
