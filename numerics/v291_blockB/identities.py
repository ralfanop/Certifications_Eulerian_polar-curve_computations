# V291 Block B: numerical checks of the identities in Sections 4.8-4.10, 6.2-6.4 and Appendix A (mpmath, 40 digits).
from mpmath import mp  # requires mpmath
from mpmath import mp, mpf, sqrt, log, cot, pi, atan, mpc, binomial, nsum, inf, hyp2f1, catalan, polyroots
mp.dps = 40
def leg(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
def h_direct(p):  # h(-p) = -(1/p) sum k (k/p), p=3 mod 4, p>3
    return -sum(k*leg(k,p) for k in range(1,p))//p
print('(1) class-number cot formula, p = 3 mod 4')
for p in [7,11,19,23,31,43,47,67,163]:
    s = sum(leg(k,p)*cot(k*pi/p) for k in range(1,p))/(2*sqrt(p))
    print('  p=%3d  cot-formula=%s  h(-p)=%d' % (p, mp.nstr(s,15), h_direct(p)))
print('(2) arctan(i/sqrt2) =', atan(mpc(0,1/sqrt(2))), ' i*log(1+sqrt2)=', log(1+sqrt(2)))
# (3) Khrushchev E.31 continued fraction, evaluated backwards
def cf(depth):
    t = mpf(0)
    for k in range(depth,0,-1):
        t = (2*k)*(2*k+1)/(1+t)
    return t   # = 2*3/(1+4*5/(1+...))
for d in [10,100,1000,10000]:
    X = cf(d)
    print('  depth %5d: 1/(2+X)=%s  1+1/(1+X)=%s' % (d, mp.nstr(1/(2+X),12), mp.nstr(1+1/(1+X),12)))
print('  targets 1-1/sqrt2 =', mp.nstr(1-1/sqrt(2),12), ' sqrt2=', mp.nstr(sqrt(2),12))
# (4) Lehmer-Mathar
s = nsum(lambda n: (-1)**(n-1)/(n*binomial(2*n,n)), [1,inf])
print('(4) sum (-1)^(n-1)/(n C(2n,n)) =', s, ' (2/sqrt5)log(phi)=', 2/sqrt(5)*log((1+sqrt(5))/2))
# (5) 2^47-1
print('(5) 2^47-1 =', 2**47-1, ' product =', 2351*4513*13264529)
# (6) Zhat zeros: (1-4q)^(-1/2) = 1+2q  <=> 12q^2+16q^3=0 after squaring
print("(6) 1-(1+2q)^2(1-4q) = 4q^2(3+4q): zeros 0,0,-3/4; Zhat(-3/4) check:", ((1+3)**-0.5 - 1 + 1.5)/(0.5625))
# (7) 2u^4-4u^2+1 and T4(u/sqrt2)
u = sqrt(1-1/sqrt(2)); print('(7) 2u^4-4u^2+1 =', 2*u**4-4*u**2+1, ' T4(u/sqrt2)=', 8*(u/sqrt(2))**4-8*(u/sqrt(2))**2+1)
# (8) Fagnano: abscissa of arc-bisecting point of lemniscate
r = sqrt(sqrt(2)-1); x = r*sqrt((1+r**2)/2); print('(8) lemniscate bisection abscissa =', x, ' u+ =', u)
# (9) Apery lambda
print('(9) (1+sqrt2)^4 =', (1+sqrt(2))**4, ' 17+12sqrt2 =', 17+12*sqrt(2), ' norm =', 17**2-2*12**2)
# (10) R00 series vs 2F1 at z=0.1
z=mpf('0.1'); print('(10) sum C(2n,n)^2 z^2n =', nsum(lambda n: binomial(2*n,n)**2*z**(2*n),[0,inf]), ' 2F1 =', hyp2f1(0.5,0.5,1,16*z*z))
# (11) Riesz Mellin check: numerical sanity via Ramanujan master theorem is formal; skip
# (12) perimeter coefficient
print('(12) (1/2)log(sqrt2-1) =', log(sqrt(2)-1)/2, ' 4C/pi =', 4*catalan/pi)
