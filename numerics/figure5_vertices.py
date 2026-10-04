"""V478 Figure 5: the polylines pass through every exact point (x_{n,k}, p_{n,k}), n = 3..670.

V478 says Figure 5 joins the points x_{n,k} = k/(n+1), p_{n,k} = E(n,k-1)/n! (Eq. (76)) by straight
segments. This script reads the figure PDF itself (standard library only: zlib + re) and checks,
with exact rational arithmetic, that
  (a) every point drawn on curve n is one of its exact vertices, to the 10^-6 pt print precision, and
  (b) every exact vertex inside the plot box is drawn.
matplotlib's default path simplification drops vertices that lie within 1/9 pt of a straight
continuation; run on the superseded file, the script lists the vertices that were dropped.

    python3 figure5_vertices.py                                  # the V478 figure (must pass)
    python3 figure5_vertices.py ../figures/superseded/Figure5_V478_matplotlib_simplified.pdf
"""
import re, sys, zlib
from collections import defaultdict
from fractions import Fraction as Fr

NMAX = 670
HEADER = re.compile(rb"q 53\.3 91\.155 210\.445 420\.89 re W n 2 J 0\.3 w /DeviceRGB cs")
X0, Y0, SCALE = Fr("53.3"), Fr("91.155"), Fr("2104.45")      # pt = X0 + (x - 0.45) SCALE, Y0 + y SCALE
BOX = (Fr("53.3"), Fr("91.155"), Fr("263.745"), Fr("512.045"))  # the plot's clip rectangle, in pt
TOL = Fr(1, 10**6)                                               # print precision of the PDF, in pt


def eulerian_rows(nmax):
    rows, row, fact = {}, [1], 1
    for n in range(1, nmax + 1):
        fact *= n
        if n > 1:
            m = n - 1
            row = [(k + 1) * (row[k] if k < len(row) else 0) + (m + 1 - k) * (row[k - 1] if k >= 1 else 0)
                   for k in range(n)]
        rows[n] = [Fr(e, fact) for e in row]
    return rows


def curve_blocks(path):
    raw = open(path, "rb").read()
    for s in re.findall(rb"stream\r?\n(.*?)endstream", raw, re.S):
        try:
            t = zlib.decompress(s)
        except zlib.error:
            continue
        hits = list(HEADER.finditer(t))
        if hits:
            out = []
            for h in hits:
                body = t[h.end():t.index(b"\nS\nQ", h.end())].decode("latin1")
                out.append([(Fr(a), Fr(b)) for a, b in re.findall(r"(-?[\d.]+) (-?[\d.]+) [ml]\n", body)])
            return out
    raise SystemExit("no Figure 5 plot block found in " + path)


def main(path):
    rows = eulerian_rows(NMAX)
    blocks = curve_blocks(path)
    assert len(blocks) == NMAX - 2, f"expected {NMAX - 2} curve blocks, found {len(blocks)}"
    x0, y0, x1, y1 = BOX
    n_inbox = n_drawn = n_missing = n_foreign = 0
    runs = defaultdict(list)
    for idx, pts in enumerate(blocks):
        n = idx + 3
        N = n + 1
        exact = [(X0 + (Fr(k, N) - Fr("0.45")) * SCALE, Y0 + rows[n][k - 1] * SCALE) for k in range(1, n + 1)]
        drawn = set()
        for (px, py) in pts:
            n_drawn += 1
            k = round((px - X0) / SCALE * N + Fr("0.45") * N)      # nearest abscissa k/(n+1)
            if 1 <= k <= n and abs(px - exact[k - 1][0]) <= TOL and abs(py - exact[k - 1][1]) <= TOL:
                drawn.add(k)
            else:
                n_foreign += 1
        for k in range(1, n + 1):
            ex, ey = exact[k - 1]
            if x0 <= ex <= x1 and y0 <= ey <= y1:
                n_inbox += 1
                if k not in drawn:
                    n_missing += 1
                    if rows[n][k - 1] >= Fr(5, 10**4):
                        runs[Fr(2 * k - N, 2)].append(n)
    print(f"file: {path}")
    print(f"curves n = 3..{NMAX}: {len(blocks)}; points drawn: {n_drawn}")
    print(f"drawn points that are not an exact vertex (tolerance 1e-6 pt): {n_foreign}")
    print(f"exact vertices inside the plot box: {n_inbox}; not drawn: {n_missing}")
    if runs:
        print("not drawn, with p_{n,k} >= 0.0005, grouped by the offset j = k - (n+1)/2:")
        for j in sorted(runs, key=lambda t: (abs(t), t)):
            ns = sorted(runs[j])
            print(f"  j = {float(j):+5.1f}: {len(ns):3d} curves, n = {ns[0]}..{ns[-1]}   (12 j^2 - 1 = {12 * j * j - 1})")
    ok = n_foreign == 0 and n_missing == 0
    print("RESULT:", "every exact vertex drawn, and nothing else" if ok else "VERTICES MISSING OR WRONG")
    return ok


if __name__ == "__main__":
    p = sys.argv[1] if len(sys.argv) > 1 else "../figures/Figure5_Eulerian_distribution_cartesian_x045_055_y00_02_BW_labels.pdf"
    sys.exit(0 if main(p) else 1)
