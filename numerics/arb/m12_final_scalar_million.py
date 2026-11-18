#!/usr/bin/env python3
"""M12 final 2026-11-18, SHA256 7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860.
Supplement the eight exact-HEAD #318 checks; no claim about Table 1 quadrature."""
from million_decimal_common import arb, ctx, WORK, MIN, record, finish, exact
from fractions import Fraction as Q

assert ctx.prec == WORK == 3600000
pi = arb.pi()
z3 = arb(3).zeta()
G = arb.const_catalan()
# From beta(3)=pi^3/32 and odd cubic sum 7*zeta(3)/8:
# psi''(1/4)=-128 sum_{n>=0}(4n+1)^(-3)=-56*zeta(3)-2*pi^3.
pg = -56*z3-2*pi**3
printed = Q('-129.3277399375369')
unit = Q(1,10**13)
assert exact(printed-unit/2) < pg < exact(printed+unit/2)
sq2, sq5 = arb(2).sqrt(), arb(5).sqrt()
L8 = (1+sq2).log()
T = 2*(4/pi).log()
values = [
    ('eq:triangle-density-eulerian 2/pi^2', 2/pi**2),
    ('eq:valean-double-eulerian sqrt(8)/pi', 2*sq2/pi),
    ('eq:plouffe-general f(1/2)', (arb(1)/2).atan()/pi),
    ('eq:plouffe-euler-angle angle radians', 2*(1/pi).atan()),
    ('eq:sigma-one Omega(1/2)', 2*(arb(1)/2).atan()),
    ('eq:beta2-moment beta(2)', G),
    ('eq:beta2-moment integral', 2*G),
    ('eq:beta3-moment reciprocal d_E', pi**3/8),
    ('eq:zeta3-moment zeta(3)', z3),
    ('eq:zeta3-moment integral', 9*z3/8),
    ('cor:geometry-moment psi double prime(1/4)', pg),
    ('eq:blagouchine T_pi/2(1)', T),
    ('eq:catalan-q integral', 4*G/pi),
    ('eq:moments-log3 log(3)', arb(3).log()),
    ('eq:lambertian-45 log(1+sqrt(2))', L8),
    ('eq:lambertian-45 L_8(1)', L8/sq2),
    ('eg:eq:D12 c_L', sq5/12),
    ('eg:eq:D12 limiting vacuum', 2/sq5),
    ('eg:eq:Dproved critical slope', 2/(pi**2+1)),
    ('eg:eq:15proved critical prefactor', 1/(pi**2+1)),
]
for name, val in values:
    record(name,val)
finish('m12-final-scalars')
