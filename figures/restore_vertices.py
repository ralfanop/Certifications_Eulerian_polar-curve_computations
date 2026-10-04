"""Restore every exact vertex in matplotlib PDFs of the Eulerian polylines (k/(n+1), E(n,k-1)/n!).

matplotlib (path.simplify = True, its default) drops vertices that lie within 1/9 pt of a straight
continuation. This script rewrites only the polyline operators inside the plot's clip block(s):
fonts, ticks, labels, frame and page geometry stay byte-identical. Each curve n is written as the
maximal runs of its segments that meet the (slightly enlarged) clip box, using the exact values.
"""
import re, sys, zlib
from fractions import Fraction
import pikepdf

NMAX = 670


def eulerian_rows(nmax):
    """Exact y_{n,k} = E(n,k-1)/n! as Fractions, k = 1..n, for n = 1..nmax."""
    rows, row, fact = {}, [1], 1
    for n in range(1, nmax + 1):
        fact *= n
        if n > 1:
            m = n - 1
            row = [(k + 1) * (row[k] if k < len(row) else 0) + (m + 1 - k) * (row[k - 1] if k >= 1 else 0)
                   for k in range(n)]
        rows[n] = [Fraction(e, fact) for e in row]
    return rows


ROWS = eulerian_rows(NMAX)


def fmt(v):
    s = f"{v:.6f}".rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def seg_meets_box(p, q, box):
    """Liang-Barsky: does segment pq meet the closed box (x0, y0, x1, y1)?"""
    x0, y0, x1, y1 = box
    t0, t1 = 0.0, 1.0
    dx, dy = q[0] - p[0], q[1] - p[1]
    for pp, qq in ((-dx, p[0] - x0), (dx, x1 - p[0]), (-dy, p[1] - y0), (dy, y1 - p[1])):
        if pp == 0:
            if qq < 0:
                return False
        else:
            r = qq / pp
            if pp < 0:
                t0 = max(t0, r)
            else:
                t1 = min(t1, r)
            if t0 > t1:
                return False
    return True


def curve_ops(n, xmap, ymap, box, margin=2.0):
    """PDF path operators for curve n: every exact vertex of every segment meeting the box."""
    N = n + 1
    pts = [(float(xmap(Fraction(k, N))), float(ymap(ROWS[n][k - 1]))) for k in range(1, n + 1)]
    big = (box[0] - margin, box[1] - margin, box[2] + margin, box[3] + margin)
    keep = [seg_meets_box(pts[i], pts[i + 1], big) for i in range(len(pts) - 1)]
    out, i = [], 0
    while i < len(keep):
        if not keep[i]:
            i += 1
            continue
        j = i
        while j + 1 < len(keep) and keep[j + 1]:
            j += 1
        out.append(f"{fmt(pts[i][0])} {fmt(pts[i][1])} m")
        out += [f"{fmt(pts[k][0])} {fmt(pts[k][1])} l" for k in range(i + 1, j + 2)]
        i = j + 1
    return out


def rewrite_blocks_per_curve(text, header_re, xmap, ymap, box):
    """Figure 5 layout: one clip block per curve, n = 3..670 in order."""
    hits = list(re.finditer(header_re, text))
    assert len(hits) == NMAX - 2, len(hits)
    pieces, last = [], 0
    for idx, h in enumerate(hits):
        n = idx + 3
        hdr_end = text.index("\n", h.start())
        blk_end = text.index("\nS\nQ", hdr_end) + len("\nS\nQ")
        pieces.append(text[last:hdr_end + 1])
        ops = curve_ops(n, xmap, ymap, box)
        pieces.append("\n" + "".join(o + "\n" for o in ops) + "\nS\nQ")
        last = blk_end
    pieces.append(text[last:])
    return "".join(pieces), len(hits)


def rewrite_single_block(text, header_re, xmap, ymap, box):
    """Full-field layout: one clip block holding the 668 curve paths, n = 3..670 in order."""
    h = re.search(header_re, text)
    hdr_end = text.index("\n", h.start())
    blk_end = text.index("\nQ", hdr_end)
    body = text[hdr_end + 1:blk_end]
    assert body.count("\nS\n") + (1 if body.endswith("\nS") else 0) == NMAX - 2
    new = "".join("".join(o + "\n" for o in curve_ops(n, xmap, ymap, box)) + "\nS\n" for n in range(3, NMAX + 1))
    return text[:hdr_end + 1] + new.rstrip("\n") + text[blk_end:], NMAX - 2


def process(src, dst, header_re, mode, xmap, ymap, box):
    pdf = pikepdf.open(src)
    done = 0
    for obj in pdf.objects:
        if not isinstance(obj, pikepdf.Stream):
            continue
        try:
            raw = obj.read_bytes()
        except Exception:
            continue
        text = raw.decode("latin1")
        if not re.search(header_re, text):
            continue
        fn = rewrite_blocks_per_curve if mode == "per_curve" else rewrite_single_block
        new, k = fn(text, header_re, xmap, ymap, box)
        obj.write(zlib.compress(new.encode("latin1"), 9), filter=pikepdf.Name.FlateDecode)
        done += 1
        print(f"{src}: rewrote {k} curves in one stream")
    assert done >= 1
    pdf.save(dst, deterministic_id=True)


FIG5 = dict(header_re=r"q 53\.3 91\.155 210\.445 420\.89 re W n 2 J 0\.3 w /DeviceRGB cs", mode="per_curve",
            xmap=lambda x: 53.3 + (float(x) - 0.45) * 2104.45, ymap=lambda y: 91.155 + float(y) * 2104.45,
            box=(53.3, 91.155, 263.745, 512.045))
FULL = dict(header_re=r"q 41\.6085 40\.867875 501\.12 438\.48 re W n 0 j 0\.24 w /DeviceRGB cs", mode="single",
            xmap=lambda x: 41.6085 + (float(x) - 0.1) * 626.4, ymap=lambda y: 40.867875 + float(y) * 626.4,
            box=(41.6085, 40.867875, 542.7285, 479.347875))

if __name__ == "__main__":
    kind, src, dst = sys.argv[1:4]
    process(src, dst, **(FIG5 if kind == "fig5" else FULL))
