"""Exact Taylor coefficients of F(alpha) at 0 and comparison with the top-degree (in k)
parts of the coefficients in Milovanovic's Conjecture 2 (formal consistency check only)."""
from fractions import Fraction as Fr
from math import comb, factorial
K = 6
def bernoulli(n):
    B = [Fr(1)]
    for m in range(1, n+1):
        B.append(-sum(comb(m+1, j)*B[j] for j in range(m))/Fr(m+1))
    return B
B = bernoulli(2*K+2)
# Lambda'(s) = sum_{n>=1} B_{2n} s^{2n-1}/(2n)!  -> coefficients of s^(2n-1)
lp = {2*n-1: B[2*n]/factorial(2*n) for n in range(1, K+1)}
# invert x = Lambda'(s): s = sum c_{2j-1} x^{2j-1}; solve order by order (odd series)
def compose(series_s, upto):   # returns Lambda'(s(x)) as dict up to x^upto
    # power series multiplication helpers
    def mul(a, b):
        r = {}
        for i, u in a.items():
            for j, v in b.items():
                if i+j <= upto: r[i+j] = r.get(i+j, 0) + u*v
        return r
    res = {}; p = dict(series_s)
    for e in range(1, upto+1, 2):
        if e in lp:
            for k, v in p.items(): res[k] = res.get(k, 0) + lp[e]*v
        p = mul(p, mul(series_s, series_s))
    return res
c = {1: 1/lp[1]}
for j in range(2, K+1):
    e = 2*j-1; c[e] = Fr(0)
    val = compose(c, e).get(e, 0)          # coefficient of x^e with c_e = 0
    c[e] = -val / lp[1]
print("I'(x) = s(x) coefficients:", {k: str(v) for k, v in c.items()})
# H(a) = sum_j c_{2j-1} a^{2j} * (1/2) * (2j-1)!!/(2j)!!
def dfrac(j):  # (2j-1)!!/(2j)!!
    return Fr(factorial(2*j), (2**j*factorial(j))**2)
h = {j: c[2*j-1]*dfrac(j)/2 for j in range(1, K+1)}   # H = sum h_j A^j, A = a^2
print("H(a) = sum h_j a^(2j):", {k: str(v) for k, v in h.items()})
# invert alpha = sum h_j A^j  ->  A = sum d_k alpha^k
def pmul(a, b, n):
    r = [Fr(0)]*(n+1)
    for i in range(n+1):
        for j in range(n+1-i): r[i+j] += a[i]*b[j]
    return r
n = K
d = [Fr(0)]*(n+1)
for k in range(1, n+1):
    # compute sum_j h_j A^j with current d, coefficient of alpha^k must equal [k==1]
    d[k] = Fr(0)
    A = d[:]; total = [Fr(0)]*(n+1); P = [Fr(1)] + [Fr(0)]*n
    for j in range(1, n+1):
        P = pmul(P, A, n)
        for i in range(n+1): total[i] += h[j]*P[i]
    target = Fr(1) if k == 1 else Fr(0)
    d[k] = (target - total[k]) / h[1]
F = [x/4 for x in d]
print("F(alpha) coefficients:", [str(x) for x in F[1:]])
conj = [Fr(1,12), Fr(-1,20), Fr(4,525), Fr(2*5,2625), Fr(2*552,1010625)]
print("Conj.2 top-degree   :", [str(x) for x in conj])
print("match:", [F[i+1] == conj[i] for i in range(5)])
