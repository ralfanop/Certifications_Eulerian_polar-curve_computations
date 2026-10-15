#!/usr/bin/env python3
"""Check of the relations on p. 355 of W. A. Hepner, The inhomogeneous Lorentz group
and the conformal group, Nuovo Cimento 26 (1962) 351-368, with explicit Euclidean
(Pauli-metric) Dirac matrices gamma_1..gamma_4, gamma_k gamma_l + gamma_l gamma_k = 2 delta_kl,
gamma_5 = gamma_1 gamma_2 gamma_3 gamma_4, and the six-dimensional M_{mu nu} of (1), p. 354,
read with the index convention under which the angular-momentum relations (2) hold.
"""
import itertools
import numpy as np
s1 = np.array([[0, 1], [1, 0]]); s2 = np.array([[0, -1j], [1j, 0]]); s3 = np.array([[1, 0], [0, -1]])
I2 = np.eye(2); Z = np.zeros((2, 2)); I4 = np.eye(4)
g = [None] + [np.block([[Z, -1j*s], [1j*s, Z]]) for s in (s1, s2, s3)] + [np.block([[I2, Z], [Z, -I2]])]
g5 = g[1] @ g[2] @ g[3] @ g[4]; g.append(g5)
C = lambda A, B: A @ B - B @ A
gp = lambda k: 0.5 * (I4 + g5) @ g[k]
gm = lambda k: 0.5 * (I4 - g5) @ g[k]
def M(m, n):
    # (1): 2M_{mu nu} has gamma_mu gamma_nu (mu, nu <= 5), i gamma_mu in column 6, -i gamma_nu in row 6
    if m == n: return np.zeros((4, 4))
    if m <= 5 and n <= 5: return 0.5 * g[m] @ g[n]
    if n == 6: return 0.5j * g[m]
    return -0.5j * g[n]
R = range(1, 5); ok = True
def rep(name, val):
    global ok; ok &= val if 'printed' not in name else True
    print(f"{name:60s} {val}")
rep("(1)-(2) angular momentum relations in six dimensions",
    all(np.allclose(C(M(a, b), M(c, d)), -(a == c)*M(b, d) - (b == d)*M(a, c) + (a == d)*M(b, c) + (b == c)*M(a, d))
        for a, b, c, d in itertools.product(range(1, 7), repeat=4)))
rep("(4) iM_6k +- M_5k = (1 +- g5) g_k / 2",
    all(np.allclose(1j*M(6, k) + M(5, k), gp(k)) and np.allclose(1j*M(6, k) - M(5, k), gm(k)) for k in R))
rep("(2a) g_i^(+-) g_k^(+-) = 0", all(np.allclose(gp(i) @ gp(k), 0) and np.allclose(gm(i) @ gm(k), 0) for i in R for k in R))
rep("(2b) [M_ik, g_l^(+-)] = d_kl g_i^(+-) - d_il g_k^(+-)",
    all(np.allclose(C(M(i, k), f(l)), (k == l)*f(i) - (i == l)*f(k)) for f in (gp, gm) for i in R for k in R for l in R))
rep("(2c) [g_i^(+), g_i^(-)] = -2i M_56", all(np.allclose(C(gp(i), gm(i)), -2j*M(5, 6)) for i in R))
rep("(2c) [g_i^(+), g_k^(-)] = 2 M_ik (i != k)  [corrected]",
    all(np.allclose(C(gp(i), gm(k)), 2*M(i, k)) for i in R for k in R if i != k))
rep("(2c) as printed: [g_i^(+), g_k^(-)] = 4 M_ik (i != k)",
    all(np.allclose(C(gp(i), gm(k)), 4*M(i, k)) for i in R for k in R if i != k))
rep("(2d) [M_56, g_k^(+-)] = +- i g_k^(+-)",
    all(np.allclose(C(M(5, 6), gp(k)), 1j*gp(k)) and np.allclose(C(M(5, 6), gm(k)), -1j*gm(k)) for k in R))
rep("(2d) [M_56, M_ik] = 0", all(np.allclose(C(M(5, 6), M(i, k)), 0) for i in R for k in R))
rep("footnote (5): g_i^(+) g_i^(-) + g_i^(-) g_i^(+) = 1",
    all(np.allclose(gp(i) @ gm(i) + gm(i) @ gp(i), I4) for i in R))
print("ALL CHECKS PASSED (printed 4 M_ik is false; the correct coefficient is 2)" if ok else "FAILURE")
