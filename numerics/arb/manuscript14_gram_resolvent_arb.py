#!/usr/bin/env python3
"""Manuscript 14.1 §§6–7: rigorous Arb/ℚ checks.

Only special-value scalars and absolutely convergent trace *series* are
numerically enclosed. This does not prove trace-classness, equality of
operator spectra, or the global Fredholm/zeta determinant identities.

For k≥0 let c_m = ζ(2m)/π^(2m), expressed by Bernoulli numbers. Because
ζ(2m)<2 and π²>9, c_m<2/9^m. For a²=1/8, expansion of 1/(π²n²+a²)
leads to two absolutely convergent rational series. Their tails are
bounded by a geometric majorant with ratio 1/72. All inequalities
apart from the Arb elementary-function evaluations use exact ℚ.
"""
from fractions import Fraction as Q
from math import factorial
from flint import arb, ctx
import flint

ctx.prec = 256
checks = 0

def check(label, condition):
    global checks
    assert bool(condition), 'FAIL: ' + label
    checks += 1
    print(f'PASS {checks:02d}: {label}')

def ball(q):
    q = Q(q)
    return arb(str(q.numerator)) / arb(str(q.denominator))

# Akiyama--Tanigawa recurrence, exact even Bernoulli numbers.
N = 34
work = [Q(0)] * (2*(N+2)+1)
even_b = {}
for m in range(len(work)):
    work[m] = Q(1,m+1)
    for j in range(m,0,-1):
        work[j-1] = j*(work[j-1]-work[j])
    if m % 2 == 0:
        even_b[m] = work[0]

def c(m):
    return (-1)**(m+1) * Q(2**(2*m-1),factorial(2*m)) * even_b[2*m]

check('Bernoulli/zeta coefficient c1 = 1/6',c(1)==Q(1,6))
check('Bernoulli/zeta coefficient c2 = 1/90',c(2)==Q(1,90))
check('Bernoulli/zeta coefficient c3 = 1/945',c(3)==Q(1,945))
check('Bernoulli/zeta coefficient c5 = 1/93555',c(5)==Q(1,93555))

tr1 = sum(((-1)**k * c(k+1) / 8**k for k in range(N)),Q(0))
tr2 = sum(((-1)**k * (k+1)*c(k+2)/8**k for k in range(N)),Q(0))
r = Q(1,72)
err1 = Q(2,9)*r**N/(1-r)
err2 = Q(2,81)*r**N*(Q(N+1)/(1-r)+r/(1-r)**2)
check('exact rational error majorants positive and below 1e-60',
      0<err1<Q(1,10**60) and 0<err2<Q(1,10**60))

# Independently evaluated real analytical expressions at a=1/sqrt(8).
a = arb(8).rsqrt()
h = a.sinh()
co = a.cosh()
T1 = (a*co/h-1)/(2*a*a)
Lp = 1/(a*a)-1/(h*h)
T2 = (2*T1-Lp)/(4*a*a)
check('Arb Langevin trace inside exact Bernoulli ℚ-series bound',
      ball(tr1-err1)<T1<ball(tr1+err1))
check('Arb Hilbert--Schmidt square trace inside exact ℚ-series bound',
      ball(tr2-err2)<T2<ball(tr2+err2))

p1=Q('0.16529410806639939866550278088492457407260894951106')
p2=Q('0.010851438958259306738743595838021377587594790570479')
check('manuscript trace correctly rounded at 50 decimal places',
      p1-Q(1,2*10**50)<tr1-err1 and tr1+err1<p1+Q(1,2*10**50))
check('manuscript HS trace correctly rounded at 51 decimal places',
      p2-Q(1,2*10**51)<tr2-err2 and tr2+err2<p2+Q(1,2*10**51))

# Eulerian endpoint: S1(±1) = sinh(a)/a, via rational Taylor enclosure.
M=18
s=sum((Q(1,8**k*factorial(2*k+1)) for k in range(M)),Q(0))
nextterm=Q(1,8**M*factorial(2*M+1))
ratio=Q(1,10000)  # strictly above the true next-term ratio 1/[8(2M+2)(2M+3)]
check('sinh tail ratio majorant valid for all k≥M',Q(1,8*(2*M+2)*(2*M+3))<ratio)
sup=s+nextterm/(1-ratio)
val=h/a
check('Eulerian Gram endpoint value in positive exact Taylor enclosure',
      ball(s)<val<ball(sup))
check('Eulerian endpoint within 50-decimal printed value',
      Q('1.02096392986501951047866463518042110194620432666987')-Q(1,2*10**50)<s and
      sup<Q('1.02096392986501951047866463518042110194620432666987')+Q(1,2*10**50))

# The Gram diagonal trace is a separate value:
# (1/2)integral[-1,1] exp(a u²) du = ∑ a^k/(k!(2k+1)).
K=51
gsum=arb(0)
for k in range(K):
    gsum += a**k/(factorial(k)*(2*k+1))
gtail=Q(1,factorial(K))/(1-Q(1,K+1))
check('Gram trace Taylor tail exact bound below 1e-60',0<gtail<Q(1,10**60))
check('Gram trace separated from Eulerian endpoint (strict Arb)',
      val<gsum and ball(Q(11,10))<gsum<ball(Q(6,5)))
check('Gram trace in certified 30-place decimal interval',
      ball(Q('1.1314801136193295536394646491348')) < gsum and
      gsum+ball(gtail) < ball(Q('1.1314801136193295536394646491350')))

print('python-flint',flint.__version__,'precision',ctx.prec)
print('R(a) trace:',T1.str(67))
print('R(a)^2 trace:',T2.str(67))
print('Gram diagonal trace partial:',gsum.str(67))
print('Eulerian endpoint:',val.str(67))
print(f'ALL {checks} SECTION 6/7 GRAM AND RESOLVENT CHECKS PASSED')
