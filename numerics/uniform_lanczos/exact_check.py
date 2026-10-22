"""Exact rational beta_N^{[M]} via moments + Chebyshev (Hankel) algorithm, small M,N."""
from fractions import Fraction as Fr
from math import comb
import sys
def moments(M, K):
    mu = [Fr(1,(k+1)*2**k) if k%2==0 else Fr(0) for k in range(K+1)]  # E U^k, U~U[-1/2,1/2]
    cur = [Fr(1)] + [Fr(0)]*K
    for _ in range(M):
        cur = [sum(comb(k,j)*cur[j]*mu[k-j] for j in range(k+1)) for k in range(K+1)]
    return cur
def betas_from_moments(mu, N):
    # Chebyshev algorithm (Gautschi), exact
    n = N+1
    sig_prev = [Fr(0)]*(2*n)
    sig = mu[:2*n]
    a = [mu[1]/mu[0]]; b = [mu[0]]
    for k in range(1, n):
        new = [Fr(0)]*(2*n)
        for l in range(k, 2*n-k):
            new[l] = sig[l+1] - a[k-1]*sig[l] - b[k-1]*sig_prev[l]
        a.append(new[k+1]/new[k] - sig[k]/sig[k-1])
        b.append(new[k]/sig[k-1])
        sig_prev, sig = sig, new
    return a, b
M=int(sys.argv[1]); N=int(sys.argv[2])
a,b = betas_from_moments(moments(M, 2*N+2), N)
for k in range(1,N+1): print(k, b[k], float(b[k]))
