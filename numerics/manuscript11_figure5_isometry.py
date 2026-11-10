#!/usr/bin/env python3
"""Manuscript 11 Figure 5: verify equal physical x/y units in the author's TikZ.

Run:
  python numerics/manuscript11_figure5_isometry.py \
    path/to/Figure5_Eulerian_Isometric_TikZ.tex

This *source-level* check is independent of the exact Lean proof of the
angle from the Eulerian recurrence. There is no need for Arb numerics.
The input, SHA-256 0e001405d2165a29602964b5d890337d52667c3029f5f5d83fe0bce684935cc1,
was supplied in Manuscript_11_Figure5_EDGE_TO_EDGE_20261110(1).zip.
"""
from decimal import Decimal, getcontext
from pathlib import Path
import hashlib
import re
import sys

getcontext().prec = 60
if len(sys.argv) != 2:
    raise SystemExit("Usage: python manuscript11_figure5_isometry.py FIGURE5.tex")
path = Path(sys.argv[1])
raw = path.read_bytes()
expected = "0e001405d2165a29602964b5d890337d52667c3029f5f5d83fe0bce684935cc1"
assert hashlib.sha256(raw).hexdigest() == expected, "input file differs from inspected figure"
s = raw.decode("utf-8")
assert r"\begin{tikzpicture}[x=1pt,y=1pt]" in s
pattern = r"\\pgfpath(?:moveto|lineto)\{\\pgfpoint\{([-0-9.]+)pt\}\{([-0-9.]+)pt\}\}"
matches = re.findall(pattern, s)
assert len(matches) >= 3
A, V, B = [(Decimal(x), Decimal(y)) for x, y in matches[:3]]
eps = Decimal("0.00002")
sx = (V[0] - A[0]) / Decimal("0.25")
sy = (V[1] - A[1]) / Decimal("0.5")
assert abs(sx - sy) <= eps, ("not isometric", sx, sy)
assert abs(A[1] - B[1]) <= eps
assert abs((V[0] - A[0]) - (B[0] - V[0])) <= eps
assert sx == Decimal("512.5") and sy == Decimal("512.5")
print("PASS: Figure 5 (n=3) physical x/y scale 512.5 pt per data unit")
print("PASS: bilateral symmetry and flat base of the n=3 apex")
print("PASS: input TikZ file sha256", expected)
