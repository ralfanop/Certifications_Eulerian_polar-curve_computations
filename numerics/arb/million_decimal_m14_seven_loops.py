"""Seven ideal open LC resonators: dimensionless coupling benchmark.
The manuscript does not give measured L,C,M. kappa=1/2 is a test case,
not a fitted physical value. Exact zero mode is handled symbolically.
"""
from fractions import Fraction as Q
from flint import arb, ctx
from million_decimal_common import record, finish, exact, WORK, MIN

assert ctx.prec == WORK == 3600000 and MIN == 3400000
pi = arb.pi()
mu = (2+arb(2).sqrt()).sqrt()
kappa = exact(Q(1,2))
lambdas = []
ratios = []
freqs = []
for j in range(1,8):
    theta = j*pi/8
    trig = 2*theta.cos()
    if j == 4:
        assert trig.contains(0)
        lam = arb(0)
    else:
        lam = trig
        assert not lam.contains(0)
        assert (lam*(lam**2-2)*(lam**4-4*lam**2+2)).contains(0)
        record(f'mode {j} adjacency eigenvalue',lam)
    ratio = 1+kappa*lam/2
    assert ratio > 0
    freq = 1/ratio.sqrt()
    assert (freq**2*ratio).contains(1)
    lambdas.append(lam)
    ratios.append(ratio)
    freqs.append(freq)
    record(f'mode {j} squared f0/f ratio',ratio)
    record(f'mode {j} f/f0',freq)
assert lambdas[0].overlaps(mu)
assert lambdas[6].overlaps(-mu)
for j in range(6):
    assert lambdas[j] > lambdas[j+1]
    assert freqs[j] < freqs[j+1]
for j in range(3):
    assert (lambdas[j]+lambdas[6-j]).contains(0)
    assert (ratios[j]+ratios[6-j]).contains(2)
assert freqs[3].contains(1)
record('extreme frequency ratio f7/f1',freqs[6]/freqs[0])
finish('m14sevenloops')
