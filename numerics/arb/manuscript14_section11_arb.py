#!/usr/bin/env python3
"""Manuscript 14.10 Theorem 11.1: 256-bit Arb + exact rational checks.

Certifies positive Taylor enclosure, Parry trinomial signs, root isolations,
and discontinuity defect; it does not formalize analytic, transcendence
or Perron-Frobenius operator claims.
"""
from fractions import Fraction as Q
from math import factorial
from flint import arb, ctx
import flint

ctx.prec = 256
checks = 0
def check(label, condition):
    global checks
    assert bool(condition), f"FAIL: {label}"
    checks += 1
    print(f"PASS {checks:02d}: {label}")

def ball(q):
    q = Q(q)
    return arb(str(q.numerator)) / arb(str(q.denominator))

def a(k):
    return Q(1, 2**k * factorial(2*k + 1))

def F(n, x):
    return x**(n-1) * (x-1) - 1

print(f"python-flint {flint.__version__}; {ctx.prec}-bit Arb")
N=18
s=sum((a(k) for k in range(N+1)), Q(0))
next_term=a(N+1)
ratio=Q(1,2*(2*N+5)*(2*N+4))
sup=s+next_term/(1-ratio)
check("positive tail and geometric factor", 0 < ratio < 1 and s < sup)
b=arb(2).rsqrt()
xe=b.sinh()/b
check("Eulerian x_E inside exact rational Taylor bounds", ball(s) < xe < ball(sup))
check("12-decimal Eulerian interval from exact fractions", Q("1.085441641272") < s < sup < Q("1.085441641273"))
l,u=Q("1.0854"),Q("1.085445")
check("x_E bracket", l < s < sup < u)
check("F_32(l)>0.01 exact", F(32,l)>Q(1,100))
check("F_31(u)<-0.0001 exact", F(31,u)<-Q(1,10000))
check("F_32(x_E)>0 Arb", xe**31*(xe-1)-1>0)
check("F_31(x_E)<0 Arb", xe**30*(xe-1)-1<0)
root31lo,root31hi=Q("1.08544960455699888475"),Q("1.08544960455699888476")
root32lo,root32hi=Q("1.08342156036341780580"),Q("1.08342156036341780581")
check("beta_31 exact rational isolation", F(31,root31lo)<0<F(31,root31hi))
check("beta_32 exact rational isolation", F(32,root32lo)<0<F(32,root32hi))
check("beta_32 < x_E < beta_31 by enclosures", root32hi < s < sup < root31lo)
defect_lo=1-sup**30*(sup-1)
defect_hi=1-s**30*(s-1)
check("defect strict interval rational", Q("0.000313240") < defect_lo < defect_hi < Q("0.000313241"))
delta=1-xe**30*(xe-1)
check("defect in Arb interval", ball(defect_lo) < delta < ball(defect_hi))
check("31st iterate strictly below one", 0 < xe**30*(xe-1) < 1)
check("first post-initial one at position 32", xe**30*(xe-1)<1<xe**31*(xe-1))
check("Mersenne integer identity", (2**5-1)==31)
# Manuscript 14.10 printed proof uses the *seven-term* s_6 enclosure,
# with a_7 as first omitted term and ratio <= 1/544 for every k >= 7.
# These rational tests match the TeX proof rather than relying on N=18.
s6 = sum((a(k) for k in range(7)), Q(0))
a7 = a(7)
ratio7 = a(8) / a7
s6hi = s6 + Q(544, 543) * a7
check("14.10: omitted-term ratio a8/a7 is exactly 1/544",
      ratio7 == Q(1, 544))
check("14.10: ratio monotonicity sample k=7..40",
      all(a(k + 1) / a(k) <= ratio7 for k in range(7, 41)))
check("14.10: exact s6 enclosure contains tighter 18-term enclosure",
      s6 < s < sup < s6hi)
check("14.10: s6 rational 12-decimal enclosure",
      Q(1085441641272, 10**12) < s6 < s6hi <
      Q(1085441641273, 10**12))
check("14.10: Arb scalar enclosed by printed s6 bound",
      ball(s6) < xe < ball(s6hi))
check("14.10: root signs follow from printed s6 endpoints",
      F(32, s6) > 0 and F(31, s6hi) < 0)
s6dlo = 1 - s6hi**30 * (s6hi - 1)
s6dhi = 1 - s6**30 * (s6 - 1)
check("14.10: defect enclosure follows from s6 bounds",
      Q(313240, 10**9) < s6dlo < s6dhi < Q(313241, 10**9))
check("14.10: Arb defect enclosed by s6 rational interval",
      ball(s6dlo) < delta < ball(s6dhi))
check("14.10: every precritical greedy remainder is inside [0,1)",
      all(0 <= xe**k * (xe-1) < 1 for k in range(31)))
check("14.10: 32nd greedy digit is 1, not 0 or 2",
      1 < xe**31 * (xe-1) < 2)
print("Eulerian Arb:", xe.str(65))
print("Defect Arb:", delta.str(65))
print(f"ALL {checks} SECTION 11 ARB/RATIONAL CHECKS PASSED")
