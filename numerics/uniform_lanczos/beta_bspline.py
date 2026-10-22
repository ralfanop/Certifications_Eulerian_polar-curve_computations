#!/usr/bin/env python3
"""Recurrence coefficients beta_N^{[M]} of the centred cardinal B-spline weight
(density of X_M = U_1+...+U_M, U_j ~ Uniform[-1/2,1/2]).

Method: the weight is a polynomial of degree M-1 on each knot interval [k,k+1]
(Milovanovic's phi_M on [0,M]).  Gauss-Legendre with ng nodes on every knot
interval integrates p(x)^2 phi_M(x) exactly as long as 2*ng-1 >= 2*Nmax + M - 1,
so the discrete measure has the same recurrence coefficients beta_1..beta_Nmax
as phi_M.  Values phi_M(k+tau) come from the stable B-spline recurrence
    phi_r(x) = [x phi_{r-1}(x) + (r-x) phi_{r-1}(x-1)]/(r-1),
all positive terms, in numpy long double (64-bit mantissa, exponent to 1e-4931).
The discretised Stieltjes procedure (orthonormal form) then gives beta_N.
"""
import numpy as np
LD = np.longdouble

def gauss_legendre01(n):
    """Nodes/weights on [0,1] in long double by Newton on P_n."""
    i = np.arange(1, n + 1, dtype=LD)
    x = np.cos(LD(np.pi) * (i - LD(0.25)) / (n + LD(0.5)))
    for _ in range(100):
        p0 = np.ones_like(x); p1 = x.copy()
        for k in range(2, n + 1):
            p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
        dp = n * (x * p1 - p0) / (x * x - 1)
        dx = p1 / dp
        x = x - dx
        if np.max(np.abs(dx)) < LD(1e-21):
            break
    p0 = np.ones_like(x); p1 = x.copy()
    for k in range(2, n + 1):
        p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
    dp = n * (x * p1 - p0) / (x * x - 1)
    w = 2 / ((1 - x * x) * dp * dp)
    return (x + 1) / 2, w / 2

def bspline_values(M, tau):
    """v[j,k] = phi_M(k + tau_j), k = 0..M-1 (order-M cardinal B-spline on [0,M])."""
    v = np.ones((len(tau), 1), dtype=LD)          # phi_1 = 1 on [0,1)
    t = tau[:, None]
    for r in range(2, M + 1):
        k = np.arange(r, dtype=LD)[None, :]
        left = np.concatenate([v, np.zeros((len(tau), 1), dtype=LD)], axis=1)   # phi_{r-1}(k+tau)
        right = np.concatenate([np.zeros((len(tau), 1), dtype=LD), v], axis=1)  # phi_{r-1}(k-1+tau)
        v = ((k + t) * left + (r - k - t) * right) / (r - 1)
    return v

def betas(M, Nmax, extra=8):
    ng = (2 * Nmax + M) // 2 + extra
    tau, w = gauss_legendre01(ng)
    v = bspline_values(M, tau)                    # (ng, M)
    x = (np.arange(M, dtype=LD)[None, :] + tau[:, None]).ravel() - LD(M) / 2   # centred
    wt = (w[:, None] * v).ravel()
    keep = wt > 0
    x, wt = x[keep], wt[keep]
    # Stieltjes, orthonormal vectors q_k = p_k(x) sqrt(wt)
    q_prev = np.zeros_like(x)
    q = np.sqrt(wt) / np.sqrt(np.sum(wt))
    b_prev = LD(0)
    out = []
    for n in range(Nmax):
        a = np.sum(x * q * q)
        r = (x - a) * q - b_prev * q_prev
        b = np.sqrt(np.sum(r * r))
        out.append((a, b * b))                    # beta_{n+1} = b^2
        q_prev, q, b_prev = q, r / b, b
    return out                                    # out[n] = (alpha_n, beta_{n+1})

if __name__ == "__main__":
    import sys
    M = int(sys.argv[1]); N = int(sys.argv[2])
    res = betas(M, N)
    for n in [1, 2, 3, N]:
        print(n, repr(res[n - 1][1]), repr(res[n-1][0]))
