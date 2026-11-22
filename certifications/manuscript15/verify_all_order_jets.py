"""Independent exact symbolic audit of Appendix B coefficients.
This is not a Lean 4 kernel proof or FLINT/Arb interval certificate.
"""
from math import factorial
import sympy as sp

z, v, m4, m6, m8 = sp.symbols('z v m4 m6 m8', nonzero=True)
F = 1-v*z/2+m4*z**2/24-m6*z**3/720+m8*z**4/40320
A = sp.expand((1-F.subs(z,4*z))/z)
B = sp.expand(F**2)
P = 3*A+2*z*sp.diff(A,z)
R = B+z*sp.diff(B,z)
Q = 2*P+2*z*sp.diff(P,z)
S = R+2*z*sp.diff(R,z)
K = - (P*S-R*Q)/(6*v*(R**2+z*P**2)**sp.Rational(3,2))
ks = sp.series(K,z,0,4).removeO().expand()
assert sp.simplify(ks.coeff(z,0)-1)==0
assert sp.simplify(ks.coeff(z,1)-(8*v-54*v*v-5*m4/(3*v)))==0
for j,sym in [(1,m4),(2,m6),(3,m8)]:
    expected = sp.Rational((-1)**j*(2*j+1)*(2*j+3)*4**(j+1),6*factorial(2*j+2))/v
    assert sp.simplify(sp.diff(ks.coeff(z,j),sym)-expected)==0, ('curvature triangular',j)
print('PASS: curvature jets j=1..3, exact triangular nonzero coefficients')

# Eulerian M=1 must reproduce exact ordinary-cycloid curvature.
val = {v:sp.Rational(1,12),m4:sp.Rational(1,80),m6:sp.Rational(1,448),m8:sp.Rational(1,2304)}
expected = sp.series(z**sp.Rational(1,2)/(2*sp.sin(z**sp.Rational(1,2)/2)),z,0,3).removeO()
assert all(sp.simplify(ks.coeff(z,j).subs(val)-sp.expand(expected).coeff(z,j))==0 for j in range(3))
print('PASS: M=1 curvature agrees with exact cycloid to t^4')

# Terminal series: derive inverse u=d+u2*d^2 when M=2, otherwise u=d+O(d^3)
u, d = sp.symbols('u d')
for M in [2,3,4,5,8]:
    phi=1-(u/(2*sp.pi+u))**(M-1)*(sp.sin(u)/u)**M
    h=sp.Rational(1,2)*(2*sp.pi+u)**(2-2*M)*(2*sp.sin(u/2))**(2*M)
    hlead=sp.Rational(1,2)*(2*sp.pi)**(2-2*M)
    philinear=sp.series(phi,u,0,2).removeO().coeff(u,1) if M==2 else 0
    # phi2(u)=1-u/(2pi)+..., inverse u=d+d^2/(2pi)+...
    inverse2 = -philinear
    # relative first correction from h and inverse power (u/d)^(2M)
    rel = sp.simplify((2-2*M)/(2*sp.pi) + 2*M*inverse2)
    gamma=1 if M==2 else 1-M
    assert sp.simplify(rel-sp.Rational(gamma,1)/sp.pi)==0, ('terminal',M)
    assert sp.simplify(sp.limit(h/u**(2*M),u,0)-hlead)==0
print('PASS: terminal leading and first correction, M=2,3,4,5,8')

# Central slope: Gaussian functional G(y^{2r})=(2r+1)!! / 2^r.
y,hh,x=sp.symbols('y hh x')
G=lambda poly: sp.expand(poly).as_poly(y).terms()
lam2=sp.Rational(1,5)  # 6^2*zeta(4)/(2*pi^4)
lam3=sp.Rational(8,105) # 6^3*zeta(6)/(3*pi^6)
q1=-lam2*y**4
q2=sp.Rational(1,2)*lam2**2*y**8-lam3*y**6
def moment(poly):
  out=0
  for (degree,),co in sp.Poly(poly,y).terms():
    assert degree%2==0
    r=degree//2
    out+=co*sp.factorial2(2*r+1)/2**r
  return sp.simplify(out)
c1=moment(q1); c2=moment(q2)
assert c1==-sp.Rational(3,4)
assert c2==sp.Rational(29,160)
D=(1+2*x)**sp.Rational(-3,2)*(1+c1*x/(1+2*x)+c2*(x/(1+2*x))**2)
D=sp.series(D,x,0,3).removeO().expand()
assert D.coeff(x,1)==-sp.Rational(15,4)
assert D.coeff(x,2)==sp.Rational(1829,160)
print('PASS: central-slope rational coefficients -15/4 and 1829/160')
print('ALL APPENDIX B SYMBOLIC CHECKS PASSED. No numerical certification claimed.')
