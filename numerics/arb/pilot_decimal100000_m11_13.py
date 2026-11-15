#!/usr/bin/env python3
"""Independent high-accuracy certificates, M11–13, first upgrade tranche.

Mathematical formulas are from the existing manuscript-specific records.
No figure generation, no old certificate edits, no inference of analytic
identities from overlapping intervals. Root candidates are only proposals;
strict outward-rounded endpoint signs certify the actual uniquely defined
roots using the monotonicity proved in the cited manuscript/Lean modules.
"""
from fractions import Fraction as Q
from math import factorial
import sys
from pilot_decimal100000_common import arb, ctx, WORK, MIN, exact, record, finish

def certificate(name, x, printed=None, trunc=False):
    assert x.is_finite() and not x.contains(0), (name, x)
    bits = x.rel_accuracy_bits()
    assert bits >= MIN, (name, bits)
    if printed is not None:
        d = Q(printed)
        unit = Q(1, 10**len(printed.split('.')[1]))
        lo, hi = (d, d+unit) if trunc else (d-unit/2, d+unit/2)
        assert exact(lo) < x < exact(hi), (name, printed, x)
    record(name,x)


def root_bracket(f, derivative, start, name, domain):
    # Newton is just a candidate generator. Discard all heuristic radii;
    # the final two CERTAIN sign inequalities are the certificate.
    x = arb(start)
    for _ in range(20):
        x = (x - f(x) / derivative(x)).mid()
    r = arb(2)**(-348000)
    lo, hi = x-r, x+r
    assert domain[0] < lo < hi < domain[1], name
    assert f(lo) < 0 and f(hi) > 0, name
    y = arb(x, 2*r)
    assert y.lower() <= lo.lower() and hi.upper() <= y.upper(), name
    certificate(name, y)
    return y


def m11():
    # V001: numerics/arb/v001_arb_decimals.py, Theorem 3.12.
    pi = arb.pi()
    certificate('pi', pi)
    certificate('r_E(pi)', 2/pi)
    certificate('p_gamma = arctan(1/2)/pi', (arb(1)/2).atan()/pi)
    certificate('alpha_3 radians', 2*(arb(1)/2).atan())
    s1, s3, sp = (pi/2).si(), (3*pi/2).si(), pi.si()
    a0, bE, aE = 4*s1/pi, 2*s1/pi, 2*(s3-s1)/pi
    err = bE-aE-2/pi
    etot = 4*sp/pi-8/pi**2
    rms = ((etot-a0*a0/2-aE*aE)/2).sqrt()
    values = [
        ('Eq (6) A0', a0, '1.745308598921205431531889'),
        ('Eq (27) bE', bE, '0.872654299460602715765944'),
        ('Eq (28) aE', aE, '0.151267597043819514429948'),
        ('Eq (29) radial error', err, '0.08476693004920185826'),
        ('Eq (33) vertex degrees', 360*(1/pi).atan()/pi, '35.3135743'),
        ('Eq (47) RMS', rms, '0.026991490844990871037657'),
        ('Eq (48) relative endpoint error percent', 50*pi*err, '13.315158235496622430663396'),
        ('Table 1 row 1', 100*a0*a0/(2*etot), '98.427'),
        ('Table 1 row 2', 100*(a0*a0+2*aE*aE)/(2*etot), '99.906'),
        ('Table 1 row 3', 100*aE*aE/(etot-a0*a0/2), '94.013'),
    ]
    for name, x, d in values:
        certificate(name, x, d)
    c, m = arb(1)/2+1/pi, arb(1)/2-1/pi
    def S(t):
        return (2*(t/2).sin()-t*(t/2).cos())/(t*t*t.sin())-m
    def dS(t):
        n = 2*(t/2).sin()-t*(t/2).cos()
        d = t*t*t.sin()
        return (t/2)*(t/2).sin()/d - n*(2*t*t.sin()+t*t*t.cos())/d**2
    theta = root_bracket(S, dS, '2.1', 'Eq (59) theta_star', (arb(2), arb('2.2')))
    # Unique zero from Thm 3.12; the bracket is a new >340000-bit enclosure.
    assert arb('2.102583094665093763925') < theta < arb('2.102583094665093763935')
    delta = 2*(theta/2).sin()/theta-c-m*theta.cos()
    eps = delta/2
    certificate('Eq (60) Delta', delta, '0.09953351643838914835807')
    certificate('Eq (60) eps_rad', eps, '0.04976675821919457417904')
    certificate('Eq (61) b_rad', c+eps, '0.86807664440298524572')
    x = 1/arb(2).sqrt()
    zcoth = x*x.cos()/x.sin()
    certificate('Sec 3.11 C_MT', arb(1)/2+zcoth, '1.3274992963', True)
    certificate('Sec 3.11 3/2-zcoth', arb(3)/2-zcoth, '0.6725007', True)
    row, fact = [1], 1
    ratios = {}
    for n in range(2, 672):
        fact *= n
        row = [(k+1)*(row[k] if k < len(row) else 0) +
               (n-k)*(row[k-1] if k else 0) for k in range(n)]
        if n in (669, 671):
            assert sum(row) == fact and row == row[::-1]
            j = (n-1)//2
            ratios[n] = Q(fact, (n+1)*(row[j]-row[j-1]))
    assert ratios[669] < Q(333,106) and Q(355,113) < ratios[671]
    assert exact(Q(333,106)) < pi < exact(Q(355,113))
    certificate('Eq (93) c669', exact(ratios[669]), '3.13914926973', True)
    certificate('Eq (93) c671', exact(ratios[671]), '3.14377888960', True)
    assert 670 < 216*pi-arb(15)/2 < 672
    print('OPEN: independent high-accuracy h_star and D_kappa/length enclosures; old 80-place/finite Taylor certificates are not upgraded by this script.')


def m12():
    # Bridge/Decimals.lean and Bridge/EtaQuarter.lean, original six scalars.
    pi = arb.pi()
    for name, val, printed, trunc in [
        ('Eq (4) rE(pi)', 2/pi, '0.6366197723675813', False),
        ('Eq (5) joining point', -2/pi, '-0.6366197723675813', False),
        ('Eq (6) angle degrees', 360*(1/pi).atan()/pi, '35.3135743028257170', False),
        ('Eq (12) dE', 8/pi**3, '0.2580122754655959', False),
        ('Eq (13) beta(3)', pi**3/32, '0.9689461462593694', False),
        ('Eq (31) C_B', (pi/arb(1).exp()).sqrt().sqrt(), '1.0368450238583971902741679669', True),
    ]:
        certificate(name, val, printed, trunc)
    def components(s):
        g = 1/(s.exp()-1)
        h = g+g*g
        return (arb(1)/2+g-1/s, 1/s**2-h,
                h*(1+2*g)-2/s**3, 6/s**4-h*((1+2*g)**2+2*h))
    s = root_bracket(lambda t: components(t)[0]-arb(1)/4,
                     lambda t: components(t)[1], '3.5935',
                     's(1/4) unique saddlepoint', (arb(3), arb(4)))
    _, v, k3, k4 = components(s)
    assert v > 0
    eta = (k4/v**2-5*k3*k3/(3*v**3))/8
    certificate('Eq (114) eta(1/4)', eta, '-0.184391')
    print('OPEN: high-accuracy validated profile quadrature and all 25 Table 1 error intervals.')


def m13():
    pi = arb.pi()
    # V007 original inputs are untouched. Independent high-precision sums.
    K = 30000
    term = lambda n: Q(1,4**n*factorial(n)*(2*n+1))
    s15 = sum(term(n) for n in range(15))
    err15 = Q(4,3)/(4**15*factorial(15))
    assert s15 == Q(337212679483569969430703669,309376751206532288348160000)
    assert err15 == Q(1,1053078495820775424000)
    assert (arb(1)/4).exp() < exact(Q(4,3))
    lo, hi = Q('1.089974208367244447324816'), Q('1.089974208367244447325767')
    assert lo < s15 < s15+err15 < hi
    I = pi.sqrt()*(arb(1)/2).erfi()
    # Recurrence for 1/(4^n n!), carrying a rigorous Arb radius.
    base, s = arb(1), arb(0)
    for n in range(K):
        s += base/(2*n+1)
        base /= 4*(n+1)
    Iseries = s+arb(0,(exact(Q(4,3))*base).upper())
    assert exact(lo) < I < exact(hi) and I.overlaps(Iseries)
    certificate('Prop 6.5 erfi integral', I)
    certificate('Prop 6.5 independently bounded series', Iseries)
    print('CONSISTENCY only: two enclosures overlap; identity comes from manuscript.')
    printed = {3:(4,1),4:(16,1),5:(24,2),6:(128,2),7:(240,3),8:(1536,3),9:(3360,4),10:(24576,4),11:(60480,5),12:(491520,5)}
    for d,(coef,p) in printed.items():
        # exact Gamma half-integer recurrence, rational coefficient and pi power
        if d%2:
            g=Q(1)
            for k in range(1,d,2): g*=Q(k,2)
            rat=4*g*2**(d-2)
            power=Q(d-1,2)
        else:
            rat=4*factorial(d//2-1)*4**((d-2)//2)
            power=Q(d-2,2)
        assert rat==coef and power==p
        a=4*exact(Q(d,2)).gamma()*(4*pi)**exact(Q(d-2,2))
        assert a.overlaps(coef*pi**p)
        certificate('Table 1 normalised factor d='+str(d),a)
    certificate('Cor 4.2 8pi',8*pi)
    K2=15000
    t=lambda k: Q(1,16**k*factorial(2*k)*(2*k+1)**2)
    base, ss = arb(1), arb(0)
    for k in range(K2):
        ss += base/(2*k+1)**2
        base /= 16*(2*k+1)*(2*k+2)
    bound=2*base
    series=ss+arb(0,bound.upper())
    shi=4*(arb(1)/4).shi()
    assert shi.overlaps(series)
    certificate('Prop 6.6 4 Shi(1/4)',shi)
    certificate('Prop 6.6 independently bounded series',series)
    # The finite Figure 5 tail claims, with genuinely tighter remainders;
    # no image/data writes. For c<=1, the remainder <= exp(c)c^K/K!.
    for c in (arb(1),arb(1)/4,arb(1)/16):
        K=30000
        # Backward recurrence avoids retaining K high-precision balls.
        term = c**K / arb(factorial(K))
        expc = c.exp()
        tail=arb(0, (expc*term).upper())
        for n in range(K-1,-1,-1):
            term = term*(n+1)/c
            tail=tail+term/(2*n+1)
            if n<=20:
                majorant=expc*term
                assert 0 < tail < majorant
                certificate(f'Thm 8.1 finite tail c={c.str(5)} N={n}',tail)
                certificate(f'Thm 8.1 bound c={c.str(5)} N={n}',majorant)
    print('OPEN: high-accuracy normalized 12x12 Gram matrix; exact zero parity and rational endpoints do not require relative bits.')


if __name__ == '__main__':
    assert len(sys.argv)==2 and sys.argv[1] in ('11','12','13')
    print('working precision',ctx.prec,flush=True)
    {'11':m11,'12':m12,'13':m13}[sys.argv[1]]()
    finish('m'+sys.argv[1])
