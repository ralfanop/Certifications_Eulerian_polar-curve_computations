"""Package checked sources, reports and logs; omit caches and temporary renders."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT.parent / "V033_FULL_THEOREM_LEAN_PACKAGE_2026-10-21.zip"


def digest(data):
    return hashlib.sha256(data).hexdigest()


if __name__ == "__main__":
    audit = json.loads((ROOT / "results/KERNEL_AUDIT_SUMMARY.json").read_text())
    assert audit["status"] == "passed" and audit["total_declarations"] == 631
    assert "All modules compiled." in (ROOT / "results/full_rebuild.log").read_text()
    selected = []
    for path in sorted(ROOT.rglob("*")):
        rel = path.relative_to(ROOT)
        if not path.is_file() or any(p.startswith(".") for p in rel.parts):
            continue
        if rel.parts[0] == "tmp" or "__pycache__" in rel.parts:
            continue
        if path.suffix in {".olean", ".ilean", ".aux", ".out", ".toc", ".synctex", ".gz"}:
            continue
        if rel.as_posix() == "SHA256SUMS.txt":
            continue
        selected.append(path)
    data = {p.relative_to(ROOT).as_posix(): p.read_bytes() for p in selected}
    hashes = "".join(f"{digest(blob)}  {name}\n" for name, blob in data.items())
    (ROOT / "SHA256SUMS.txt").write_text(hashes)
    data["SHA256SUMS.txt"] = hashes.encode()
    required = {"README.txt", "FORMAL_THEOREM_MAP.txt", "lean/V033UniformIntegrals.lean",
                "lean/V033AllDegreeTheorem.lean", "lean/V033FullVerification.lean",
                "code/verify_lean_portable.sh", "results/KERNEL_AUDIT_SUMMARY.json",
                "V033_INDEPENDENT_ADVERSARIAL_REVIEW.pdf"}
    assert required <= data.keys()
    with zipfile.ZipFile(OUTPUT, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name, blob in data.items():
            z.writestr(f"{ROOT.name}/{name}", blob)
    with zipfile.ZipFile(OUTPUT) as z:
        assert z.testzip() is None
        for name, blob in data.items():
            assert z.read(f"{ROOT.name}/{name}") == blob, name
    proof_sources = sum(name.startswith("lean/") and name.endswith(".lean") for name in data)
    assert proof_sources == 56
    print(json.dumps({"path": str(OUTPUT), "bytes": OUTPUT.stat().st_size,
                      "members": len(data), "lean_sources": proof_sources,
                      "sha256": digest(OUTPUT.read_bytes()), "checksums_verified": len(data)-1}, indent=2))
