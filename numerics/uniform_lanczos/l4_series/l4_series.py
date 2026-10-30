#!/usr/bin/env python3
"""Exact series arithmetic for Task L4 (UniformLanczos higher profile coefficients).

Lp(s)  = 1/2 + 1/(e^s-1) - 1/s = sum_{k>=1} B_{2k} s^{2k-1}/(2k)!
Ip     = inverse of Lp (odd series in x)
Phi(a) = H(a) = (1/pi) int_0^{pi/2} a sin t Ip(a sin t) dt  = sum c_k W_{k+1} a^{k+1}, Ip = sum c_k x^k,
         W_m = (1/pi) int_0^{pi/2} sin^m = (1/2) * (m-1)!!/m!! for m even
F(alpha) = a^2/4 as a series in alpha = Phi(a)
"""
from fractions import Fraction as Fr
from math import factorial

N = 20  # truncation order in s/x

def bernoulli(n):
    A = [Fr(0)] * (n + 1)
    for m in range(n + 1):
        A[m] = Fr(1, m + 1)
        for j in range(m, 0, -1):
            A[j - 1] = j * (A[j - 1] - A[j])
    return A[0]  # B_n with B_1 = +1/2 convention; even n unaffected

def mul(p, q, n=N):
    r = [Fr(0)] * (n + 1)
    for i, a in enumerate(p):
        if a == 0: continue
        for j, b in enumerate(q):
            if i + j > n: break
            r[i + j] += a * b
    return r

def compose(p, q, n=N):
    """p(q(x)) truncated, q(0)=0"""
    r = [Fr(0)] * (n + 1)
    qpow = [Fr(1)] + [Fr(0)] * n
    for k, a in enumerate(p):
        if k > 0: qpow = mul(qpow, q, n)
        if a != 0:
            for i in range(n + 1): r[i] += a * qpow[i]
    return r

def invert(p, n=N):
    """series inverse of p with p(0)=0, p'(0)!=0"""
    q = [Fr(0)] * (n + 1)
    q[1] = 1 / p[1]
    for m in range(2, n + 1):
        c = compose(p, q, n)
        q[m] -= c[m] / p[1]
    return q

Lp = [Fr(0)] * (N + 1)
for k in range(1, N // 2 + 1):
    if 2 * k - 1 <= N:
        Lp[2 * k - 1] = bernoulli(2 * k) / factorial(2 * k)
Ip = invert(Lp)

def W(m):  # (1/pi) int_0^{pi/2} sin^m, m even
    num, den = Fr(1), Fr(1)
    for j in range(1, m + 1):
        if j % 2 == 1: num *= j
        else: den *= j
    return num / den / 2

Phi = [Fr(0)] * (N + 2)
for k in range(1, N + 1):
    if Ip[k] != 0 and k + 1 <= N + 1:
        Phi[k + 1] = Ip[k] * W(k + 1)
# Phi as series in A = a^2: Phi = sum phi_j A^j
phiA = [Phi[2 * j] for j in range((N + 1) // 2 + 1)]
# invert: A = G(alpha)
G = invert(phiA, len(phiA) - 1)
F = [g / 4 for g in G]

if __name__ == '__main__':
    print('Lp  :', [str(c) for c in Lp[:16]])
    print('Ip  :', [str(c) for c in Ip[:16]])
    print('PhiA:', [str(c) for c in phiA[:9]])
    print('F   :', [str(c) for c in F[:9]])
