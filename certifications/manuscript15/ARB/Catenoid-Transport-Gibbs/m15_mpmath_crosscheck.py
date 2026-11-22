#!/usr/bin/env python3
"""Third-library cross-check (mpmath, non-interval): recompute the fourteen
constants at 20,050 significant digits and compare their first 20,000 decimals
with the Arb-certified files in digits/.  This is a consistency check only;
the certification itself is the Arb run."""
import json
import os
import sys

import mpmath as mp

OUT = sys.argv[1] if len(sys.argv) > 1 else "out"
N = 20000
mp.mp.dps = N + 50

u = mp.findroot(lambda x: x * mp.tanh(x) - 1, mp.mpf("1.1996786402577338"))
lam = 1 / mp.sinh(u)
alpha = 2 * mp.acot(lam)
q = 2 / mp.pi
xa, xb = 1 / mp.sqrt(8), 1 / mp.sqrt(2)


def W1m(x):
    return 1 - mp.tanh(x / 2) / x


def W2m(x):
    return mp.sqrt(1 - 2 * (mp.coth(x) - 1 / x) / x)


vals = {
    "u_star": u, "lambda_CL": lam, "alpha_CL_rad": alpha,
    "alpha_CL_deg": alpha * 180 / mp.pi, "Lstar_over_a": 2 / lam,
    "W1_mu1_nu1": q - mp.mpf(1) / 2, "W2_mu1_nu1": mp.sqrt(mp.mpf(5) / 6 - 2 * q * q),
    "Winf_mu1_nu1": mp.sqrt(1 - q * q) - q * mp.acos(q),
    "W2sq_mu1_nu1": mp.mpf(5) / 6 - 2 * q * q,
    "D5": mp.mpf(62) / 75 * mp.zeta(3) - 8 / mp.pi ** 2,
    "W1_rho_a": W1m(xa), "W2_rho_a": W2m(xa), "W1_rho_b": W1m(xb), "W2_rho_b": W2m(xb),
}
res = {}
ok = True
for k, v in vals.items():
    s = mp.nstr(v, N + 40, strip_zeros=False)
    ip, fp = s.split(".")
    ref = open(os.path.join(OUT, "digits", k + ".txt")).read().strip()
    rip, rfp = ref.split(".")
    # compare the first N - 2 decimals (the last two may differ by rounding of nstr)
    agree = (ip == rip) and (fp[:N - 2] == rfp[:N - 2])
    res[k] = agree
    ok = ok and agree
    print(k, agree)
json.dump({"mpmath": mp.__version__, "decimals_compared": N - 2, "results": res, "ALL_AGREE": ok},
          open(os.path.join(OUT, "mpmath_crosscheck.json"), "w"), indent=1)
print("ALL_AGREE", ok)
