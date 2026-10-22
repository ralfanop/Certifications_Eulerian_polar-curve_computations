"""Second-order saddlepoint correction q(x) = kappa4/(8 v^2) - 5 kappa3^2/(24 v^3) at the test points."""
import mpmath as mp
mp.mp.dps=30
Lam=lambda s: mp.log(mp.sinh(s/2)/(s/2))
Lp=lambda s: mp.coth(s/2)/2-1/s
for x in ['0.05','0.15','0.25','0.35','0.42']:
    x=mp.mpf(x); s=mp.findroot(lambda t: Lp(t)-x, 12*x/(1-4*x*x))
    v=mp.diff(Lam,s,2); k3=mp.diff(Lam,s,3); k4=mp.diff(Lam,s,4)
    q=k4/(8*v**2)-5*k3**2/(24*v**3)
    print('x=',x,' q(x)=',mp.nstr(q,6))
