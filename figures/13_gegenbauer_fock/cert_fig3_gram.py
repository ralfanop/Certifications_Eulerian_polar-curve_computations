"""Certificate for Figure 3(b) of manuscript 13: normalized Gram matrix of F_n = C_{1/2,alpha} P_n,
alpha = 1/16 (c = 4), 0 <= m, n <= 11, P_n Legendre (= Gegenbauer P_n^{(1/2)}), nu_{1/2} = uniform on (-1,1).

<F_m, F_n> = sum_{k>=0} c^k/k! M_k(P_m) M_k(P_n),  M_k(P) = int u^k P(u) dnu_{1/2}(u)   (from eq. (gram)).
Exact rational partial sums S_{mn} over 0 <= k < K; since |P_n| <= 1 on [-1,1], |M_k(P)| <= 1, so the tail is
bounded by T = sum_{k>=K} c^k/k! <= (c^K/K!) e^c <= 55 c^K/K!  (e^4 < 55).
Entries with m+n odd: every term vanishes exactly (M_k(P_m) M_k(P_n) = 0 by parity), so the entry is exactly 0.
Normalized entries g_{mn} are enclosed with rational square-root bounds (scaling 10^80)."""
from fractions import Fraction as Fr
from math import factorial, isqrt

N, K, c = 12, 90, Fr(4)
def legendre(n):
    P = [[Fr(1)], [Fr(0), Fr(1)]]
    for k in range(1, n):
        a = [Fr(0)] + [Fr(2 * k + 1, k + 1) * x for x in P[k]]
        b = P[k - 1] + [Fr(0)] * 2
        P.append([a[i] - Fr(k, k + 1) * b[i] for i in range(k + 2)])
    return P[:n + 1]
mom = lambda j: Fr(1, j + 1) if j % 2 == 0 else Fr(0)
P = legendre(N - 1)
for n in range(N):  # sanity: P_n(1) = 1
    assert sum(P[n]) == 1
M = [[sum(a * mom(i + k) for i, a in enumerate(P[n])) for k in range(K)] for n in range(N)]
T = Fr(55) * c**K / factorial(K)
S = [[sum(c**k / factorial(k) * M[m][k] * M[n][k] for k in range(K)) for n in range(N)] for m in range(N)]
SC = 10**80
def sqrt_lo(x): return Fr(isqrt(x.numerator * SC * SC // x.denominator), SC)
def sqrt_hi(x): return Fr(isqrt(-(-x.numerator * SC * SC // x.denominator)) + 1, SC)
lines, enc = [], {}
for m in range(N):
    for n in range(N):
        if (m + n) % 2 == 1:
            assert all(M[m][k] * M[n][k] == 0 for k in range(K))
            enc[(m, n)] = (Fr(0), Fr(0)); continue
        lo, hi = S[m][n], S[m][n] + T
        assert lo > 0
        dlo = S[m][m] * S[n][n]; dhi = (S[m][m] + T) * (S[n][n] + T)
        glo, ghi = lo / sqrt_hi(dhi), hi / sqrt_lo(dlo)
        if m == n: glo, ghi = min(glo, Fr(1)), max(ghi, Fr(1))
        enc[(m, n)] = (glo, ghi)
for m in range(N):
    for n in range(N):
        a, b = enc[(m, n)]
        lines.append(f'm={m:2d} n={n:2d}  g in [{float(a):.15f}, {float(b):.15f}]  width {float(b-a):.1e}')
off = {k: v for k, v in enc.items() if k[0] != k[1]}
best = max(off, key=lambda k: off[k][0])
blo, bhi = off[best]
assert all(v[1] < blo for k, v in off.items() if k not in (best, best[::-1])), 'maximum not unique up to symmetry'
assert all(v[0] > 0 for k, v in off.items() if (k[0] + k[1]) % 2 == 0)
assert all(enc[(m, n + 2)][1] <= enc[(m, n)][0] for m in range(N) for n in range(m, N - 2) if (m + n) % 2 == 0), 'decay'
summary = [f'tail bound per unnormalized entry: T <= {float(T):.3e}',
           'entries with m+n odd: exactly 0 (all terms vanish by parity)',
           'entries with m+n even: certified positive',
           f'largest off-diagonal entry: (m,n)={best} and its transpose, g in [{float(blo):.12f}, {float(bhi):.12f}]',
           'along each row, to the right of the diagonal, the even entries decrease (certified)']
open('fig3_gram_certificate.txt', 'w').write('\n'.join(summary) + '\n\n' + '\n'.join(lines) + '\n')
print('\n'.join(summary))
