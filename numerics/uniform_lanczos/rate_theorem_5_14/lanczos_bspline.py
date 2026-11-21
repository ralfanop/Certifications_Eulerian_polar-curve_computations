"""Monic recurrence coefficients beta_j^{[M]} of the centred cardinal B-spline weight w_M
(law of S_M = U_1+...+U_M, U_i uniform on [-1/2,1/2]), computed by the Stieltjes procedure
on a piecewise Gauss-Legendre discretisation (N_per nodes on each knot interval), in
80-bit extended precision (numpy.longdouble) to cover the dynamic range of w_M.
Returns a_k = sqrt(beta_k^{[M]})/M, k = 1..kmax  (recurrence coefficients of g_M = M w_M(Mx))."""
import numpy as np
from numpy.polynomial.legendre import leggauss

LD = np.longdouble

def bspline_values(M, u):
    # B[k,l] = N_M(k+u_l), k = 0..M-1, cardinal B-spline of order M on [0,M]; positive recursion
    u = u.astype(LD)
    B = np.ones((1, u.size), dtype=LD)
    for m in range(1, M):
        k = np.arange(m + 1, dtype=LD)[:, None]
        left = np.vstack([B, np.zeros((1, u.size), dtype=LD)])      # N_m(k+u), N_m(m+u)=0
        right = np.vstack([np.zeros((1, u.size), dtype=LD), B])     # N_m(k-1+u), N_m(-1+u)=0
        B = ((k + u) * left + (m + 1 - k - u) * right) / LD(m)
    return B

def recurrence(M, kmax, N_per=64):
    xg, wg = leggauss(N_per)
    u = (np.asarray(xg, dtype=LD) + 1) / 2
    om = np.asarray(wg, dtype=LD) / 2
    B = bspline_values(M, u)                                      # (M, N_per)
    k = np.arange(M, dtype=LD)[:, None]
    x = ((k + u[None, :]) - LD(M) / 2) / LD(M)                    # scaled abscissae in [-1/2,1/2]
    W = B * om[None, :]                                           # weights (sum = 1)
    x = x.ravel(); W = W.ravel()
    v_prev = np.zeros_like(W)
    v = np.sqrt(W); v /= np.sqrt(np.sum(v * v))
    a = np.zeros(kmax + 1, dtype=LD); b = np.zeros(kmax + 1, dtype=LD)
    for j in range(kmax):
        r = x * v
        b[j] = np.sum(r * v)
        r = r - b[j] * v - a[j] * v_prev
        a[j + 1] = np.sqrt(np.sum(r * r))
        v_prev, v = v, r / a[j + 1]
    return a[1:], b, float(np.sum(W))

if __name__ == "__main__":
    import sys
    M = int(sys.argv[1]); kmax = int(sys.argv[2]); N = int(sys.argv[3]) if len(sys.argv) > 3 else 64
    a, b, tot = recurrence(M, kmax, N)
    beta = (a * M) ** 2
    print("mass", tot, "max|b|", float(np.max(np.abs(b))))
    print("beta1", float(beta[0]), "exact", M / 12)
    print("beta2", float(beta[1]), "exact", (M / 3 - 0.2) / 2)
