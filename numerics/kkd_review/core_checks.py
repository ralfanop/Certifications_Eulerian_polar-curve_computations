# KKD "correct core": Lemma 2.0, Prop 2.2, Thm 2.12, Lemmas 2.13-2.14, Cor 2.15, (86)-(91), (94). Requires mpmath.
from mpmath import mp, sqrt, log, pi, sin, cos, quad, hyp2f1, hyp3f2, zeta, atan, exp, inf
mp.dps = 30
L = log(1 + sqrt(2))
print('(86) printed log E/(2 sqrt D), D=2 :', L/(2*sqrt(2)), '  L(1,chi_8) =', L/sqrt(2), '  2 log E/sqrt 8 =', 2*L/sqrt(8))
print('N(1+sqrt2) =', (1+sqrt(2))*(1-sqrt(2)), '  (the fundamental unit has norm -1)')
print('(87) int_0^{pi/2} sin^2/(sin+cos) =', quad(lambda x: sin(x)**2/(sin(x)+cos(x)), [0, pi/2]))
print('(67)-(70) 2F1(1)/2F1(-1) =', hyp2f1(0.5, 0.5, 1.5, 1)/hyp2f1(0.5, 0.5, 1.5, -1), '  pi/(2L) =', pi/(2*L))
print('(77) (2/3) 3F2(3/4,3/4,5/4;3/2,7/4;1) =', 2*hyp3f2(0.75, 0.75, 1.25, 1.5, 1.75, 1)/3, '  pi-2L =', pi-2*L)
print('(78) 4 3F2(1/4,1/4,3/4;1/2,5/4;1)     =', 4*hyp3f2(0.25, 0.25, 0.75, 0.5, 1.25, 1), '  pi+2L =', pi+2*L)
print('(89) 3 zeta(2)/4 =', 3*zeta(2)/4, '  sqrt =', sqrt(3*zeta(2)/4), '  pi/sqrt8 =', pi/sqrt(8))
print('Cor 2.15 (sqrt(pi)/2)/sqrt(2/pi) =', (sqrt(pi)/2)/sqrt(2/pi), '  E|g_C| / E|g_R| =',
      quad(lambda r: 2*r*r*exp(-r**2), [0, inf])/sqrt(2/pi))
print('(94) arctan(1/2)/pi =', atan(0.5)/pi)
