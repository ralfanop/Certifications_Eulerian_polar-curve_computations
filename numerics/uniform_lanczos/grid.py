import sys, time
import numpy as np
from beta_bspline import betas
F = {0.25:'0.017843171552976253987', 0.5:'0.03037681808122836024', 1:'0.044536148060769199264',
     2:'0.054809110906575878003', 4:'0.059837175377715549072'}
Ms = [int(m) for m in sys.argv[1:]]
for M in Ms:
    t0=time.time()
    res = betas(M, 4*M)
    for t in [0.25,0.5,1,2,4]:
        N = int(round(t*M))
        bN = res[N-1][1]
        val = bN/np.longdouble(M*M); Fv = np.longdouble(F[t])
        print(f"M={M:4d} N={N:5d} t={t:<5} beta/M^2={float(val):.15f} F={float(Fv):.15f} diff={float(val-Fv):+.6e} M*diff={float(M*(val-Fv)):+.6f} |alpha|max={float(max(abs(r[0]) for r in res[:N])):.1e}", flush=True)
    print(f"# M={M} time {time.time()-t0:.1f}s", flush=True)
