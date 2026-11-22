#!/usr/bin/env python3
"""Independent exact-rational/symbolic checks for the sixth-moment cusp formulas.

Requires SymPy. This checks the finite sixth-order coefficients, not a Lean 4
kernel proof, numerical FLINT/Arb certificate, or the all-order theorem.
"""
import sympy as sp
s, v, w, m6, M = sp.symbols('s v w m6 M', nonzero=True)
F = 1 - v*s/sp.Integer(2) + w*s**2/sp.Integer(24) - m6*s**3/sp.Integer(720)
H = sp.series((1 - F.subs(s, 4*s))/(2*v*s*F**3), s, 0, 3).removeO().expand()
b1 = 3*v - 2*w/(3*v)
b2 = 21*v*v/sp.Integer(4) - 9*w/sp.Integer(4) + w*w/(9*v*v) + 4*m6/(45*v)
h1 = 3*v/sp.Integer(2) - w/(3*v)
h2 = 3*v*v/sp.Integer(2) - 5*w/sp.Integer(8) + 2*m6/(45*v)
assert sp.simplify(H.coeff(s, 0) - 1) == 0
assert sp.simplify(H.coeff(s, 1) - h1) == 0
assert sp.simplify(H.coeff(s, 2) - h2) == 0
Q = sp.expand(sp.series(H*H, s, 0, 3).removeO())
assert sp.simplify(Q.coeff(s, 1) - b1) == 0
assert sp.simplify(Q.coeff(s, 2) - b2) == 0
# Recover c_1, c_2, c_3 by the all-order triangular formula, evaluated
# symbolically at these three orders only (m_2, m_4, m_6).
from itertools import product
h = [sp.Integer(1), h1, h2]
c = [sp.Integer(1)]
for j in (1, 2, 3):
    summand = sum(h[p]*c[q]*c[r]*c[u] for p,q,r,u in product(range(j), repeat=4)
                  if p+q+r+u == j-1)
    c.append(sp.factor(-2*v* summand /4**j))
assert sp.simplify(c[1] + v/2) == 0
assert sp.simplify(c[2] - w/24) == 0
assert sp.simplify(c[3] + m6/720) == 0
# Cumulants of independent centred uniforms through the sixth moment.
m6M = sp.factor(M/sp.Integer(448) + 15*M*(M-1)/(sp.Integer(80)*12)
                + 15*M*(M-1)*(M-2)/(12**3))
assert sp.simplify(m6M-M*(35*M*M-42*M+16)/4032) == 0
vM = M/sp.Integer(12)
wM = (5*M*M - 2*M)/240
assert sp.simplify(b1.subs({v:vM,w:wM})-(5*M+4)/60) == 0
assert sp.simplify(b2.subs({v:vM,w:wM,m6:m6M})
                   -(875*M*M+315*M+808)/151200) == 0
print('PASS: exact sixth-order cusp coefficients, triangular steps j=1,2,3, uniform-convolution specialization.')
