import numpy as np
from scipy.special import erf
from scipy.optimize import minimize
SQ2=np.sqrt(2); SQ6=np.sqrt(6)
phi=lambda x: np.exp(-x*x/2)/np.sqrt(2*np.pi)
Phi=lambda x: 0.5*(1+erf(x/SQ2))
nu=np.sqrt(2/np.pi)
def poly(a):  # coefficients of p(z)=sum a_j psi_j, low->high
    a0,a1,a2,a3=a
    return np.array([a0-a2/SQ2, a1-3*a3/SQ6, a2/SQ2, a3/SQ6])
def moments(al,be,K=3):
    # I_k = int_al^be z^k phi
    I=[Phi(be)-Phi(al), phi(al)-phi(be)]
    for k in range(2,K+1):
        fa=al**(k-1)*phi(al) if np.isfinite(al) else 0.0
        fb=be**(k-1)*phi(be) if np.isfinite(be) else 0.0
        I.append((k-1)*I[k-2]+fa-fb)
    return I
def posint(q):  # int_0^inf q(s)_+ phi(s) ds, q low->high
    r=np.roots(q[::-1]) if np.any(q[1:]!=0) else []
    rr=sorted([x.real for x in r if abs(x.imag)<1e-12 and x.real>0])
    pts=[0.0]+rr+[np.inf]; tot=0
    for al,be in zip(pts[:-1],pts[1:]):
        m=al+1 if be==np.inf else (al+be)/2
        if np.polyval(q[::-1],m)>0:
            I=moments(al,be); tot+=sum(q[k]*I[k] for k in range(4))
    return tot
def J(c,a):
    q=poly(a); qm=q*np.array([1,-1,1,-1])
    lin=np.array([0,c,0,0])
    return posint(q-lin)+posint(-q-lin)+posint(qm-lin)+posint(-qm-lin)
d=lambda c: 1.5*nu*(np.sqrt(1+c*c)-c)
from scipy.optimize import minimize_scalar
SQ2=np.sqrt(2); SQ6=np.sqrt(6); phi0=1/np.sqrt(2*np.pi); nu=np.sqrt(2/np.pi)
d=lambda c: 1.5*nu/(np.sqrt(1+c*c)+c)
kap=1.25
def bound(c,th,r):
    lam=1/c; a0=r*np.cos(th); a2=r*np.sin(th); A0=a0-a2/SQ2; B=a2/SQ2
    if A0<0: A0,B=-A0,-B
    O=1-r*r
    y1=2*A0/(1+np.sqrt(1-4*A0*B*lam**2))
    # Q/lam = int_0^y1 (A0 - y + B lam^2 y^2)(1 - lam^2 y^2/2 + lam^4 y^4/8) dy
    P=np.polynomial.polynomial
    g=np.array([A0,-1,B*lam**2]); w=np.array([1,0,-lam**2/2,0,lam**4/8])
    prod=P.polymul(g,w); integ=P.polyint(prod)
    Qol=P.polyval(y1,integ)
    T1=2*phi0*Qol*lam
    sst=kap/c
    Y2=2.5*O*sst**2; kp=c-2*abs(B)*sst
    T2=phi0*Y2/kp
    S0=np.sqrt(np.sqrt(6)*c)
    T3=4/np.sqrt(6)*phi0*np.exp(-S0**2/2)
    return T1+T2+T3, (T1,T2,T3)
# numerical sanity check (not part of the proof): the tail bound T1 + T2 + T3 dominates the exact J for c >= 8
rng = np.random.default_rng(5); worst = 1e9; viol = 0
for it in range(20000):
    a = rng.normal(size=4)
    if it % 2: a[1] *= 0.05; a[3] *= 0.05
    a /= np.linalg.norm(a); c = 8 * np.exp(rng.uniform(0, 2.5))
    b, _ = bound(c, np.arctan2(a[2], a[0]), np.hypot(a[0], a[2])); j = J(c, a)
    if j > 0: worst = min(worst, (b - j) / j)
    if b < j: viol += 1
print("samples 20000, violations", viol, ", min relative slack (bound - J)/J =", worst)
