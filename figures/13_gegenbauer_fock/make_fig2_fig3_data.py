"""Data for Figures 2 and 3 of manuscript 13.
Fig. 2(b): densities of nu_lambda, c_lambda (1-u^2)^(lambda-1/2), c_lambda = Gamma(lambda+1)/(sqrt(pi) Gamma(lambda+1/2)).
Fig. 3(b): normalised Gram matrix <F_m,F_n>/(|F_m||F_n|), F_n = C P_n, lambda = 1/2 (Legendre), alpha = 1/16 (c = 4):
  <F_m,F_n> = sum_k c^k/k! M_k(P_m) M_k(P_n), M_k(P) = int u^k P dnu_{1/2}, exact rationals, truncated at K = 90
  with tail <= c^K e^c/K! (|M_k| <= 1)."""
import numpy as np
from scipy.special import jv, gamma
from fractions import Fraction as Fr
import math

u = np.linspace(-1, 1, 6001)
for d in (2, 3, 4, 6, 12):
    lam = (d - 2) / 2
    c = gamma(lam + 1) / (np.sqrt(np.pi) * gamma(lam + 0.5))
    with np.errstate(all='ignore'):
        w = c * (1 - u ** 2) ** (lam - 0.5)
    m = np.isfinite(w) & (w <= 3.0)
    np.savetxt(f'fig2_density_d{d}.dat', np.column_stack([u[m], w[m]]), header='u w', comments='', fmt='%.8f')

# Legendre polynomials P_n = Gegenbauer C_n^{1/2}, exact coefficients
def legendre(n):
    P = [[Fr(1)], [Fr(0), Fr(1)]]
    for k in range(1, n):
        a = [Fr(0)] + [Fr(2 * k + 1, k + 1) * x for x in P[k]]
        b = P[k - 1] + [Fr(0)] * 2
        P.append([a[i] - Fr(k, k + 1) * b[i] for i in range(k + 2)])
    return P[:n + 1]
def mom(j):  # int u^j dnu_{1/2} = 1/(j+1) for even j
    return Fr(1, j + 1) if j % 2 == 0 else Fr(0)
N, K, c = 12, 90, Fr(4)
P = legendre(N - 1)
M = [[sum(a * mom(i + k) for i, a in enumerate(P[n])) for k in range(K)] for n in range(N)]
G = [[sum(c ** k / math.factorial(k) * M[m][k] * M[n][k] for k in range(K)) for n in range(N)] for m in range(N)]
tail = float(c ** K * Fr(55) / math.factorial(K))  # e^4 < 55
with open('fig3_gram.dat', 'w') as f:
    f.write('m n g\n')
    for m in range(N):
        for n in range(N):
            g = float(G[m][n]) / math.sqrt(float(G[m][m]) * float(G[n][n]))
            f.write(f'{n} {m} {g:.10f}\n')
        f.write('\n')
print('tail bound per entry', tail)
print('min', min(float(G[m][n])/math.sqrt(float(G[m][m]*G[n][n])) for m in range(N) for n in range(N)))
print('max |offdiag|', max(abs(float(G[m][n]))/math.sqrt(float(G[m][m]*G[n][n])) for m in range(N) for n in range(N) if m != n))
