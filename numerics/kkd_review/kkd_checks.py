#!/usr/bin/env python3
"""Numerical checks for the adversarial review of
R. Alfano, "Explicit identities connecting Krivine's sharp Grothendieck bound, Koenig's bilinear form,
and quadratic Dirichlet L-series" (Filomat submission, print of October 2026). Requires mpmath."""
import sys
from mpmath import mp, mpf, sqrt, log, pi, exp, erf, erfi, quad, inf, zeta, diff, euler, harmonic, nstr
mp.dps = 30
L = log(1 + sqrt(2))

# (5)-(7), (14), (16): the same kernel on the quadrant (0,inf)^2 and on the whole plane
# inner integral  int_0^inf sin(xy) e^{-y^2/2} dy = sqrt(pi/2) e^{-x^2/2} erfi(x/sqrt2)
inner = lambda x: sqrt(pi/2)*exp(-x**2/2)*erfi(x/sqrt(2))
quadrant = quad(lambda x: exp(-x**2/2)*inner(x), [0, inf])
print('quadrant (0,inf)^2, f = g = 1        :', quadrant, '  log(1+sqrt2)/sqrt2 =', L/sqrt(2))
print('whole plane, f = g = sign  (= 4x)     :', 4*quadrant, '  sqrt8 log(1+sqrt2) =', sqrt(8)*L)

# (43): Deninger's R(x) = -d^2/ds^2 zeta(s, x) at s = 0
R = lambda x: -diff(lambda s: zeta(s, x), 0, 2)
comb = R(mpf(1)/8) - R(mpf(3)/8) - R(mpf(5)/8) + R(mpf(7)/8)
g8 = mpf('1.20933063094138118664026424093547')
print('R(1/8)-R(3/8)-R(5/8)+R(7/8)          :', comb)
print('(43) log(2 pi e^{2 gamma}) + comb/2L  :', log(2*pi) + 2*euler + comb/(2*L), '  (44) gamma_8 =', g8)
print('     log(2 pi e^{gamma})   + comb/2L  :', log(2*pi) + euler + comb/(2*L))
print('     gamma + comb/2L                  :', euler + comb/(2*L))

# Table 1
print('H_2 =', harmonic(2), '  (Table 1 prints 2/3)')

# (93), last equality
I_erf = quad(lambda x: 1 - erf(x)**2, [-inf, 0, inf])
print('(93) int(1-erf^2) =', I_erf, '  16 P_A / int =', 16/(2*pi)/I_erf, '  (the paper states 1)')
print('     c_R = sqrt(2/pi) =', sqrt(2/pi), '  int/2 =', I_erf/2)

# (38), (40), (57): Coffey's combination equals the Hurwitz combination at s = 2
comb2 = zeta(2, mpf(1)/8) - zeta(2, mpf(3)/8) - zeta(2, mpf(5)/8) + zeta(2, mpf(7)/8)
print('(38) Hurwitz/Stieltjes combination    :', comb2, '  pi^2/(8 sqrt2) =', pi**2/(8*sqrt(2)), '  sqrt32 pi^2 =', sqrt(32)*pi**2)

# (12)-(13): Heilman's delta_0 (personal communication [32])
mp.dps = 500
d0 = mpf('4.07123102832e-457')
print('(12) as printed  pi d0 /(2L(L+d0))     :', nstr(pi*d0/(2*L*(L+d0)), 6))
print('     K_R - pi/(2(L+d0))                :', nstr(pi/(2*L) - pi/(2*(L+d0)), 6), ' = lower bound for K_R - K_G')
