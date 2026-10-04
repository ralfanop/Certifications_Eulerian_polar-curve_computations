"""Flajolet & Sedgewick, Figure IX.14 field (x in [0,1], y in [0,0.7]), n = 3..670, as a pure vector PDF.

Only the formulas of F&S are used:
  (75), p. 209:   A(z,u) = (u-1) / (u - e^{z(u-1)}),   A_{n,k} = n! [z^n u^k] A(z,u)  (k rises);
  p. 658:         F(z,u) = u(1-u) / (e^{(u-1)z} - u) = u A(z,u),  so  [z^n u^k] F(z,u) = A_{n,k-1}/n!;
  p. 695:         Figure IX.14, "the histogram of the Eulerian distribution scaled to (n+1) on the
                  horizontal axis": the points (k/(n+1), [z^n u^k] F(z,u)), k = 1..n, joined by segments.
Coefficient extraction from (75): dividing numerator and denominator by -e^{z(u-1)},
  A(z,u) = (1-u) e^{z(1-u)} / (1 - u e^{z(1-u)}) = (1-u) sum_{j>=0} u^j e^{(j+1)(1-u)z},
so n![z^n] A = (1-u)^{n+1} sum_{j>=0} (j+1)^n u^j and, exactly in integers,
  A_{n,k} = sum_{i=0}^{k} (-1)^i C(n+1,i) (k+1-i)^n.
Nothing else is drawn: no axes, ticks, labels or frame. The page is the field itself, S pt per unit
on both axes, every vertex written (no simplification), coordinates to 1e-4 pt.
"""
import sys, zlib
from math import comb, factorial

NMIN, NMAX = 3, 670
S = 14400                     # pt per unit: page 14400 x 10080 pt (200 x 140 in), the PDF maximum side
LW0 = 0.3 / 2104.45 * S       # reference line width: 1.4255e-4 in data units (2.05279 pt on this page)


def fs_row(n):
    """A_{n,k}, k = 0..n-1, from the expansion of F&S (75)."""
    P = [j ** n for j in range(n + 2)]
    C = [comb(n + 1, i) for i in range(n + 2)]
    return [sum((-1) ** i * C[i] * P[k + 1 - i] for i in range(k + 1)) for k in range(n)]


def main(out, factor=1):
    LW = LW0 / factor           # factor 100 gives the published file (0.02053 pt)
    rows = {n: fs_row(n) for n in range(1, NMAX + 1)}
    # checks against F&S's printed expansion of (75) and the total mass n!
    assert rows[2] == [1, 1] and rows[3] == [1, 4, 1] and rows[4] == [1, 11, 11, 1]
    assert all(sum(rows[n]) == factorial(n) for n in rows)
    ops = [f"1 j 2 J {LW:.5f} w 0 G"]
    npts = 0
    for n in range(NMIN, NMAX + 1):
        f, N = factorial(n), n + 1
        for k in range(1, n + 1):
            x = S * k / N                       # exact rational -> correctly rounded double
            y = rows[n][k - 1] * S / f
            ops.append(f"{x:.4f} {y:.4f} {'m' if k == 1 else 'l'}")
            npts += 1
        ops.append("S")
    content = zlib.compress(("\n".join(ops) + "\n").encode(), 9)
    W, H = S, round(0.7 * S)
    objs = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {W} {H}] /Contents 4 0 R /Resources << >> >>".encode(),
        f"<< /Length {len(content)} /Filter /FlateDecode >>\nstream\n".encode() + content + b"\nendstream",
        b"<< /Title (Eulerian distribution, n = 3..670, field of Flajolet-Sedgewick Figure IX.14) "
        b"/Author (Roberto Alfano) /Subject (points \\(k/\\(n+1\\), [z^n u^k] F\\(z,u\\)\\), "
        b"F = u\\(1-u\\)/\\(e^{\\(u-1\\)z}-u\\); x in [0,1], y in [0,0.7]; every vertex) >>",
    ]
    pdf = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")
    offs = []
    for i, o in enumerate(objs, 1):
        offs.append(len(pdf))
        pdf += f"{i} 0 obj\n".encode() + o + b"\nendobj\n"
    xref = len(pdf)
    pdf += f"xref\n0 {len(objs) + 1}\n0000000000 65535 f \n".encode()
    pdf += b"".join(f"{o:010d} 00000 n \n".encode() for o in offs)
    pdf += f"trailer\n<< /Size {len(objs) + 1} /Root 1 0 R /Info 5 0 R >>\nstartxref\n{xref}\n%%EOF\n".encode()
    open(out, "wb").write(pdf)
    print(f"{out}: {npts} vertices on {NMAX - NMIN + 1} polylines, page {W} x {H} pt, line width {LW:.5f} pt, "
          f"{len(pdf)} bytes")


if __name__ == "__main__":
    # python3 fs_ix14_vector.py Eulerian_distribution_FS_IX14_field_n3_670_vector_thin100.pdf 100
    main(sys.argv[1] if len(sys.argv) > 1 else "Eulerian_distribution_FS_IX14_field_n3_670_vector.pdf",
         int(sys.argv[2]) if len(sys.argv) > 2 else 1)
