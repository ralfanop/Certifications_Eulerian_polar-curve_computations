"""Numerical sanity checks of the ingredients of Theorem 5.14 (not part of the proof).
(a) Freud's identity k/a_k = int p_k' p_{k-1} g_M dx  (Lemma 5.11);
(b) the residual G_k(a) = M int_{|x|<=r} I' p_k p_{k-1} g_M dx - k/a_k stays bounded as M grows (proof of Thm 5.14);
(c) M |a_k - xi_{k/M}/2| stays bounded (Thm 5.14)."""
import numpy as np
from numpy.polynomial.legendre import leggauss
from lanczos_bspline import bspline_values, LD
from profile_F import Ip, xi

def nodes(M, N_per=48):
    xg, wg = leggauss(N_per)
    u = (np.asarray(xg, dtype=LD) + 1) / 2
    om = np.asarray(wg, dtype=LD) / 2
    B = bspline_values(M, u)
    k = np.arange(M, dtype=LD)[:, None]
    x = (((k + u[None, :]) - LD(M) / 2) / LD(M)).ravel()
    W = (B * om[None, :]).ravel()
    return x, W

def run(M, ks, r=0.49):
    x, W = nodes(M)
    kmax = max(ks) + 1
    # orthonormal polynomial values and derivatives at the nodes, by the recurrence
    p_prev = np.zeros_like(x); p = np.ones_like(x) / np.sqrt(np.sum(W))
    d_prev = np.zeros_like(x); d = np.zeros_like(x)
    a = [LD(0)]
    P = {0: p}; D = {0: d}
    for j in range(kmax):
        r_ = x * p - a[j] * p_prev
        a_next = np.sqrt(np.sum(W * r_ * r_))
        dr = p + x * d - a[j] * d_prev
        p_prev, p = p, r_ / a_next
        d_prev, d = d, dr / a_next
        a.append(a_next); P[j + 1] = p; D[j + 1] = d
    Ipx = np.asarray(Ip(np.asarray(x, float)), dtype=LD)
    inner = np.abs(x) <= r
    out = []
    for k in ks:
        freud = np.sum(W * D[k] * P[k - 1])
        G = M * np.sum((W * Ipx * P[k] * P[k - 1])[inner]) - k / a[k]
        dev = M * (a[k] - LD(xi(k / M)) / 2)
        out.append((k, float(k / a[k]), float(freud), float(G), float(dev)))
    return out

if __name__ == "__main__":
    for M in [50, 100, 200]:
        for k, ka, fr, G, dev in run(M, [M // 4, M // 2, M]):
            print("M=%4d k=%4d  k/a_k=%.12f  Freud=%.12f  G_k(a)=%+.5f  M(a_k-xi/2)=%+.5f" % (M, k, ka, fr, G, dev))
