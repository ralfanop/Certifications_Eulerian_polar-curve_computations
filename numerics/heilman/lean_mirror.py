"""Exact-rational mirror of every statement in lean/Heilman/AppendixA231.lean.
Each line evaluates, with Python Fractions, the same expression the Lean kernel checks."""
from fractions import Fraction as F
from math import factorial as fact
dec = lambda m, e: F(m, 10**e); sci = lambda m, e: F(m * 10**e)
rho, Mphi, L = dec(1152, 3), dec(1550302861362, 10), dec(341627465436, 10)
eps, Dl, Dh = dec(834296222775, 34), dec(429244734953, 32), dec(429244734953300, 35)
DlT = dec(429244734953296, 35)          # tighter certified lower bound for Delta
Cs, Cprinted = sci(184, 18), sci(201664948, 10)
q = dec(9, 1) / rho
tail = lambda n: Mphi * q**(2*n + 3) / F(399, 1024)
p = lambda m: rho**m / (2 * fact(m) * Mphi)
sign = lambda m, k: p(m) * Mphi / rho**(2*k + 1) < F(1, 2 * fact(2*k + 1))
lhs = lambda m, C: L * (C * p(m)**2 + p(m) * eps)
p092 = dec(466807077, 10) / (2 * dec(1936822943625, 10))
p096 = dec(371640256, 10) / (2 * dec(3007944582777, 10))
eta, B6 = dec(290803934947, 17), sci(12843271408, 7)
plo, phi_ = dec(314159265358979323846, 20), dec(314159265358979323847, 20)
slo, shi = dec(14142135623730950488, 19), dec(14142135623730950489, 19)
Cr, r, x = sci(407811339, 8), dec(92, 2), F(45, 46)
S = {
 "q = 25/32": q == F(25, 32),
 "q^2 + 399/1024 = 1": q**2 + F(399, 1024) == 1,
 "sqrt2 bounds": slo**2 < 2 < shi**2,
 "Delta >= Dl": Dl * phi_ + eta**4 * (B6 * eta**2 / 2880) <= eta**4 * (400 * slo),
 "Delta >= DlT": DlT * phi_ + eta**4 * (B6 * eta**2 / 2880) <= eta**4 * (400 * slo),
 "Delta <= Dh": eta**4 * (400 * shi) <= Dh * plo + eta**4 * (B6 * eta**2 / 2880),
 "Delta bracket > 0": eta**4 * (B6 * eta**2 / 2880) < eta**4 * (400 * slo),
 "2 tail(115) < eps": 2 * tail(115) < eps,
 "eps <= 2 tail(114)": eps <= 2 * tail(114),
 "Dh/L <= 2 tail(114)": Dh / L <= 2 * tail(114),
 "c=1/2: eps_half <= 2 tail(115)": F(1, 2) * Dl / L <= 2 * tail(115),
 "c=1/2: 2 tail(116) < eps_half": 2 * tail(116) < F(1, 2) * Dl / L,
 "sign 231 k<115": all(sign(231, k) for k in range(115)),
 "sign 231 k=115 equality": p(231) * Mphi / rho**231 == F(1, 2 * fact(231)),
 "sign 232 k<116": all(sign(232, k) for k in range(116)),
 "sign 233 k<116": all(sign(233, k) for k in range(116)),
 "sign 230 k=115 fails": not sign(230, 115),
 "delta0(231) >= 4.0712310283e-457": lhs(231, Cs) + dec(40712310283, 467) <= p(231) * DlT,
 "delta0(232) >= 2.0215e-459": lhs(232, Cs) + dec(20215, 463) <= p(232) * DlT,
 "delta0(233) >= 9.9950e-462": lhs(233, Cs) + dec(99950, 466) <= p(233) * DlT,
 "p(m) < p092, p096": all(p(m) < p092 and p(m) < p096 for m in (231, 232, 233)),
 "C' printed formula <= Cs": 2 * Cr / r * x / F(1, 46)**2 <= Cs,
 "slip A.39": p092 < dec(120508454, 12),
 "slip A.45": dec(4581618473084, 9) < 12 * dec(3818015394237, 10),
 "slip A.47": dec(705228288411, 11)**2 < F(6, 7)**2 + 49,
 "slip A.49 printed formula": Cprinted < 2 * Cr / r * x / F(1, 46)**2,
 "A.49 value formula ok": 2 * Cr / r * x / F(91, 2116) <= Cprinted,
 "slip A.66": p(231) * Dh < lhs(231, Cprinted) + dec(407123102832, 468),
 "c(115) in (0.66328, 0.66329)": F(66328,100000) < 2*L*tail(115)/Dh and 2*L*tail(115)/Dl < F(66329,100000),
 "R(232,115)=rho/232, R(233,115)=rho^2/(232*233)": p(232)*Mphi/rho**231*2*fact(231) == rho/232 and p(233)*Mphi/rho**231*2*fact(231) == rho**2/(232*233),
 "p(231) in monotone range": p(231)*(2*L*Cs) + L*eps < Dl,
 "m>=232 dominated": p(232)*Dh < dec(602,461) < dec(40712310283,467),
 "sup delta0(231) bounds": p(231)*(2*L*tail(115)) + L*Cs*p(231)**2 + dec(407992590889,468) <= p(231)*DlT and p(231)*Dh <= p(231)*(2*L*tail(115)) + dec(407992590890,468),
 "Heilman eps >= 99.78% of sup": F(9978,10000)*(p(231)*Dh) + lhs(231,Cs) <= p(231)*DlT + F(9978,10000)*(p(231)*(2*L*tail(115))),
 "phat(231) = 2 p(231)": rho**231/(fact(231)*Mphi) == 2*p(231),
 "relaxed sign control k<116 for phat(231)": all(rho**231/(fact(231)*Mphi)*Mphi/rho**(2*k+1) <= F(1,fact(2*k+1)) for k in range(116)),
 "relaxed sign control fails for phat(230) at k=115": not (rho**230/(fact(230)*Mphi)*Mphi/rho**231 <= F(1,fact(231))),
 "phat(231) < p096 < p092": 2*p(231) < p096 < p092,
 "delta0(phat 231) >= 8.1424620566e-457": L*(Cs*(2*p(231))**2 + 2*p(231)*eps) + dec(81424620566,467) <= 2*p(231)*DlT,
 "sup delta0(phat 231) >= 8.1598518177e-457": 2*p(231)*(2*L*tail(115)) + L*Cs*(2*p(231))**2 + dec(81598518177,467) <= 2*p(231)*DlT,
 "C' = (4500/91) C_r <= printed": F(4500,91)*Cr <= Cprinted and 2*Cr/r*x/F(91,2116) == F(4500,91)*Cr,
}
for k, v in S.items(): print("PASS" if v else "FAIL", k)
print(sum(S.values()), "/", len(S))
