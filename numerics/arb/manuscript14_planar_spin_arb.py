#!/usr/bin/env python3
"""Manuscript 14, display (52) at lambda = 0 (the planar spin): Arb certificate at 2000 bits.

(52): int_{-1}^{1} e^{xu} d nu_lambda(u) = Gamma(lambda+1) (2/x)^lambda I_lambda(x)
      = sum_k (x^2/4)^k / (k! (lambda+1)_k).
At lambda = 0, nu_0 is the arcsine law (density 1/(pi sqrt(1-u^2))), (1)_k = k!, and the value is
I_0(x), the single-spin partition function of the planar (n = 2) spin.

  (A) exact rationals: (1)_k = k!; the series coefficients 1/(k!)^2 = C(2k,k)/(4^k (2k)!), i.e.
      the even moments C(2k,k)/4^k of nu_0 times the exponential coefficients 1/(2k)!, k <= 60;
      the moments of nu_0 equal (1/2)_k/(1)_k.
  (B) the series with a rigorous tail bound against Arb's I_0, at eight real points (including
      a = 1/sqrt8 and |z0| = 1/sqrt2) and at the complex points z0 = i/sqrt2 and 1 + i, where
      I_0(z0) = J_0(1/sqrt2);
  (C) the series against the integrals (1/pi) int_0^pi e^{x cos t} dt and
      (1/(2 pi)) int_0^{2 pi} e^{x cos t} dt computed by acb.integral;
  (D) the moments (1/pi) int_0^pi cos^m t dt for m <= 12 against C(m/2, .)/2^m and 0;
  (E) the n-vector family at the three Gegenbauer indices -1/2, 0, 1/2 at x = a: the planar
      partition function I_0(a) lies strictly between cosh a (Ising) and sinh(a)/a (Heisenberg).

Every Arb quantity is a ball; comparisons are certified ball inequalities.
Requires python-flint 0.9.0.
"""
from fractions import Fraction as Q
from math import comb, factorial
import sys
import flint
from flint import arb, acb, ctx

ctx.prec = 2000
failures = []
count = 0


def check(desc, cond):
    global count
    ok = bool(cond)
    count += 1
    print(f"{'PASS' if ok else 'FAIL'} {count:03d}: {desc}")
    if not ok:
        failures.append(desc)


def qball(q):
    q = Q(q)
    return arb(q.numerator) / arb(q.denominator)


TINY = arb(2) ** (-1900)


def is_zero_ball(x):
    if isinstance(x, acb):
        return is_zero_ball(x.real) and is_zero_ball(x.imag)
    return x.contains(0) and abs(x).upper() < TINY


print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, "
      f"Arb precision {ctx.prec} bits")
pi = arb.pi()
s2 = arb(2).sqrt()
a = 1 / arb(8).sqrt()
b = 1 / s2

# (A) exact rationals
def poch(c, k):
    p = Q(1)
    for i in range(k):
        p *= c + i
    return p


check("(A) (1)_k = k!, k <= 60", all(poch(Q(1), k) == factorial(k) for k in range(61)))
check("(A) 1/(k! (1)_k) = [C(2k,k)/4^k] x [4^k/(2k)!], k <= 60",
      all(Q(1, factorial(k) ** 2) == Q(comb(2 * k, k), 4 ** k) * Q(4 ** k, factorial(2 * k)) for k in range(61)))
check("(A) moments of nu_0: C(2k,k)/4^k = (1/2)_k/(1)_k, k <= 60",
      all(Q(comb(2 * k, k), 4 ** k) == poch(Q(1, 2), k) / poch(Q(1), k) for k in range(61)))


def series(x, K=400):
    """sum_{k<=K} (x^2/4)^k/(k!)^2 and a rigorous bound on the modulus of the tail."""
    y = x * x / 4
    t = acb(1) if isinstance(x, acb) else arb(1)
    s = t
    for k in range(1, K + 1):
        t = t * y / (k * k)
        s += t
    ay = abs(y)
    tnext = abs(t) * ay / ((K + 1) ** 2)
    q = ay / ((K + 2) ** 2)
    assert q < 1
    return s, tnext / (1 - q)


reals = [a, b, arb(1), s2, arb(2), qball(Q(-3, 2)), arb(5), qball(Q(1, 10))]
names = ["1/sqrt8", "1/sqrt2", "1", "sqrt2", "2", "-3/2", "5", "1/10"]
ok_bes = True
ok_int = True
ok_circ = True
for x, nm in zip(reals, names):
    s, tail = series(x)
    ok_bes = ok_bes and tail < TINY and is_zero_ball(s - x.bessel_i(0))
    I = acb.integral(lambda t, analytic, x=x: (x * t.cos()).exp(), acb(0), acb(pi)) / pi
    ok_int = ok_int and is_zero_ball(I - s)
    Ic = acb.integral(lambda t, analytic, x=x: (x * t.cos()).exp(), acb(0), acb(2 * pi)) / (2 * pi)
    ok_circ = ok_circ and is_zero_ball(Ic - s)
check("(B) (52) at lambda = 0: the series sum (x^2/4)^k/(k!)^2 (tail < 2^-1900) equals Arb's I_0(x) "
      "at x = 1/sqrt8, 1/sqrt2, 1, sqrt2, 2, -3/2, 5, 1/10", ok_bes)
check("(C) (1/pi) int_0^pi e^{x cos t} dt equals the series at the same eight points", ok_int)
check("(C) (1/(2pi)) int_0^{2pi} e^{x cos t} dt (uniform unit vector of R^2) equals the series", ok_circ)
z0 = acb(0, b)
s, tail = series(z0)
check("(B) at the special point: I_0(z0) = sum (z0^2/4)^k/(k!)^2 = J_0(1/sqrt2)",
      tail < TINY and is_zero_ball(s - b.bessel_j(0)) and is_zero_ball(s - z0.bessel_i(0)))
check("(B) I_0(z0) = sum (-1/8)^k/(k!)^2 is real, between 0.87 and 0.88",
      is_zero_ball(s.imag) and qball(Q(87, 100)) < s.real < qball(Q(88, 100)))
zc = acb(1, 1)
s, tail = series(zc)
check("(B) complex point 1 + i: series equals Arb's I_0", tail < TINY and is_zero_ball(s - zc.bessel_i(0)))
Iz = acb.integral(lambda t, analytic: (z0 * t.cos()).exp(), acb(0), acb(pi)) / pi
check("(C) (1/pi) int_0^pi e^{z0 cos t} dt = I_0(z0) = J_0(1/sqrt2)", is_zero_ball(Iz - b.bessel_j(0)))
# (D) moments
ok = True
for m in range(0, 13):
    M = acb.integral(lambda t, analytic, m=m: t.cos() ** m, acb(0), acb(pi)) / pi
    target = qball(Q(comb(m, m // 2), 2 ** m)) if m % 2 == 0 else arb(0)
    ok = ok and is_zero_ball(M - target)
check("(D) moments of nu_0: (1/pi) int_0^pi cos^m = C(m, m/2)/2^m for even m, 0 for odd m, m <= 12", ok)
check("(D) normalisation of nu_0: (1/pi) int_0^pi dt = 1",
      is_zero_ball(acb.integral(lambda t, analytic: acb(1), acb(0), acb(pi)) / pi - 1))
# (E) the three members of the n-vector family at x = a
s0, _ = series(a)
check("(E) n-vector partition functions at x = 1/sqrt8: cosh x > I_0(x) > sinh(x)/x "
      "(Ising n = 1, planar n = 2, Heisenberg n = 3)",
      a.cosh() > s0 and s0 > a.sinh() / a)
print("I_0(1/sqrt8)   =", s0.str(60, radius=False))
print("I_0(z0)        =", series(z0)[0].real.str(60, radius=False))
if failures:
    print(f"FAILED {len(failures)} of {count} checks")
    for f_ in failures:
        print("  FAIL:", f_)
    sys.exit(1)
print(f"ALL {count} PLANAR-SPIN CHECKS PASSED (precision {ctx.prec} bits)")
