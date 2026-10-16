# Equation (4) of the KKD print: the right-hand side as printed, for several n. Requires mpmath.
from mpmath import mp, mpf, pi, log, sqrt, gamma, hyp2f1, nstr
mp.dps = 20
K = pi/(2*log(1 + sqrt(2)))
for n in (1, 2, 5, 10, 100, 1000):
    r = K*gamma((n+1)/mpf(2))**2*hyp2f1(0.5, 0.5, n/mpf(2) + 1, -1)/(gamma(n/mpf(2))*gamma((n+1)/mpf(2)))
    print(n, nstr(r, 10))
