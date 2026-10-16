import sys  # requires mpmath
from mpmath import *
mp.dps = 40
chi = {1:1,3:-1,5:-1,7:1}
f = lambda s: mpf(8)**(-s)*fsum(c*zeta(s, mpf(a)/8) for a,c in chi.items())
L1 = f(1+mpf(10)**-30)
print('L(1,chi8) =', L1, ' exact', log(1+sqrt(2))/sqrt(2))
Lp = diff(f, 1+mpf(10)**-25)  # step around pole-free point
gK = euler + Lp/L1
print('gamma_Q(sqrt 2) = gamma + L\'(1)/L(1) =', gK)
print('draft (C.6) =', mpf('1.20933063094138118664026424093547097334700909059315456011578210585217390057'))
# draft (C.1): gamma_8 = log(2 pi e^gamma) + [R(1/8)-R(3/8)-R(5/8)+R(7/8)]/(2 log(1+sqrt2)); check what R-combination would be
print('log(2 pi e^gamma) =', log(2*pi)+euler)
# (C.4) as written: 2 + sqrt(8 pi gamma)  -- compare with log(2 pi e^gamma)
print('2+sqrt(8*pi*gamma) =', 2+sqrt(8*pi*euler))
