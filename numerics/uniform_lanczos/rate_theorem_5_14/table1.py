import sys, time, numpy as np
from lanczos_bspline import recurrence
from profile_F import F
ts = [0.25, 0.5, 1, 2, 4]
Fv = {t: F(t) for t in ts}
for M in [int(m) for m in sys.argv[1].split(',')]:
    for N in [int(n) for n in sys.argv[2].split(',')]:
        t0 = time.time(); a, b, tot = recurrence(M, 4*M, N)
        row = []
        for t in ts:
            j = int(round(t*M)); E = float(a[j-1]**2) - Fv[t]
            row.append("%.7f" % (M*E))
        print(M, N, "%.1fs" % (time.time()-t0), " ".join(row), flush=True)
