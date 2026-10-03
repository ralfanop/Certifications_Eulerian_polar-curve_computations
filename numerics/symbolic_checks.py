"""Symbolic checks (sympy) of identities in the V478 manuscript (equation numbers of the V478 PDF)."""
import sympy as sp
t, h, x, al = sp.symbols('theta h x alpha', positive=True)
r = 2*sp.sin(t/2)/t

# Def. 2.1, Eq. (4): the Si power series
z = sp.symbols('z')
claim_si = sum((-1)**k * z**(2*k+1) / ((2*k+1)*sp.factorial(2*k+1)) for k in range(8))
print("Eq.(4) Si series (through z^15):",
      sp.simplify(sp.series(sp.Si(z), z, 0, 17).removeO() - claim_si) == 0)

# Proof of Prop. 3.6: r_E'
print("Prop. 3.6 proof, r_E':", sp.simplify(sp.diff(r, t) - (sp.cos(t/2) - 2*sp.sin(t/2)/t)/t) == 0)

# Eq. (40): curvature numerator identity
num = r**2 + 2*sp.diff(r, t)**2 - r*sp.diff(r, t, 2)
claim = (3*t*sp.sin(t/2)**2 + 2*(t - sp.sin(t)))/t**3
print("Eq.(40) curvature numerator identity:", sp.simplify(sp.expand_trig(num - claim)) == 0)

# Cor. 3.8 proof: limacon numerator and its minimum
a, b = sp.symbols('a b', positive=True)
rl = b + a*sp.cos(t)
nl = sp.expand(rl**2 + 2*sp.diff(rl, t)**2 - rl*sp.diff(rl, t, 2))
print("Cor. 3.8 numerator:", sp.simplify(nl - (b**2 + 3*a*b*sp.cos(t) + 2*a**2)) == 0,
      " value at cos=-1:", sp.factor(b**2 - 3*a*b + 2*a**2))

# Eq. (59): f'(cos theta) for f(x) = r_E(arccos x)
f = 2*sp.sin(sp.acos(x)/2)/sp.acos(x)
fp = sp.diff(f, x).subs(x, sp.cos(t))
claim59 = (2*sp.sin(t/2) - t*sp.cos(t/2))/(t**2*sp.sin(t))
print("Eq.(59) slope formula, residual at theta=2.1:", sp.N((fp - claim59).subs(t, sp.Rational(21, 10)), 30))

# Eq. (62): f(cos theta) = int_0^1 cos(s theta/2) ds = r_E(theta)
s = sp.Symbol('s')
print("Eq.(62):", sp.simplify(sp.integrate(sp.cos(s*t/2), (s, 0, 1)) - r) == 0)

# Eqs. (63)-(64)
g = sp.cos(al*sp.acos(x))
g2 = sp.diff(g, x, 2).subs(x, sp.cos(t))
G = al*sp.sin(t)*sp.cos(al*t) - sp.cos(t)*sp.sin(al*t)
print("Eq.(63) residuals at two points:",
      [sp.N((g2 + al*G/sp.sin(t)**3).subs({t: tv, al: av}), 40)
       for tv, av in [(sp.Rational(7, 10), sp.Rational(3, 10)), (sp.Rational(29, 10), sp.Rational(1, 2))]])
print("Eq.(64):", sp.simplify(sp.diff(G, t) - (1 - al**2)*sp.sin(t)*sp.sin(al*t)) == 0)

# Lemma 3.14 proof: det(J^T J) = n + 1
for n in (3, 7):
    J = sp.Matrix.vstack(-sp.ones(1, n), sp.eye(n))
    print("Lemma 3.14, det(J^T J) for n=%d:" % n, (J.T*J).det())

# Sec. 3.11 (after Eq. 78): B(e^h) = e^{h/2} Z(h), r_E(t) = Z(it), psi''(0) = 1/12, -i psi'(i pi) = 1/pi
hh = sp.symbols('hh')
Z = 2*sp.sinh(hh/2)/hh
B_exp = (sp.exp(hh) - 1)/hh      # B(e^h) = (e^h - 1)/log(e^h) = (e^h - 1)/h for |Im h| < pi
print("B(e^h) = e^{h/2} Z(h):", sp.simplify((B_exp - sp.exp(hh/2)*Z).rewrite(sp.exp)) == 0)
print("r_E(t) = Z(it):", sp.simplify((Z.subs(hh, sp.I*t) - r).rewrite(sp.exp)) == 0)
psi = sp.log(Z)
print("psi''(0) = 1/12:", sp.limit(sp.diff(psi, hh, 2), hh, 0) == sp.Rational(1, 12))
dpsi = sp.coth(hh/2)/2 - 1/hh
print("psi' = coth(h/2)/2 - 1/h:", sp.simplify((sp.diff(psi, hh) - dpsi).rewrite(sp.exp)) == 0)
print("-i psi'(i pi) = 1/pi:", sp.simplify(-sp.I*dpsi.subs(hh, sp.I*sp.pi) - 1/sp.pi) == 0)

# Sec. 3.11 (after Eq. 79): Gaussian homothety
D, Dp, X = sp.symbols('D Dp X', positive=True)
G_ = lambda DD, xx: sp.sqrt(6/(sp.pi*DD))*sp.exp(-6*DD*(xx - sp.Rational(1, 2))**2)
lam = sp.sqrt(D/Dp)
print("Gaussian homothety:", sp.simplify(G_(Dp, sp.Rational(1, 2) + lam*(X - sp.Rational(1, 2))) - lam*G_(D, X)) == 0)
