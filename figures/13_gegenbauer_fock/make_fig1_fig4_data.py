"""Data for Figures 1 and 4 of manuscript 13 (Gegenbauer-Fock).

Figure 1: G_out_{3,1/2}(rho) = exp(i rho/2)/(4 pi rho) (Corollary 4.2), so
  8 pi Im G = 2 sin(rho/2)/rho = r_E(rho),  8 pi Re G = 2 cos(rho/2)/rho.
Figure 4: Eulerian case lambda = 1/2, m_{2n} = 1/(2n+1), c = 1/(4 alpha):
  T_N = sum_{n>=N} c^n m_{2n}/n!  (Theorem 8.1) and the bound B_N = e^c c^N/N!.
T_N is enclosed exactly: S_{N,K} <= T_N <= S_{N,K} + c^K e^c/K! with rational
partial sums S_{N,K} (K = N + 80) and the rational bound e^c <= sum_{j<=30} c^j/j! + 2 c^31/31!.
"""
from fractions import Fraction as Fr
import math

def efrac_upper(c, J=30):
    s = sum(c**j / math.factorial(j) for j in range(J + 1))
    return s + 2 * c**(J + 1) / math.factorial(J + 1)          # valid for 0 < c <= 1

def efrac_lower(c, J=30):
    return sum(c**j / math.factorial(j) for j in range(J + 1))

# Figure 1
with open('fig1_im.dat', 'w') as f, open('fig1_re.dat', 'w') as g:
    f.write('rho y\n'); g.write('rho y\n')
    n = 6000
    for i in range(n + 1):
        r = 8 * math.pi * i / n
        f.write(f'{r:.6f} {(1.0 if r == 0 else 2*math.sin(r/2)/r):.8f}\n')
        if r >= 0.55:
            g.write(f'{r:.6f} {2*math.cos(r/2)/r:.8f}\n')

# Figure 2
report = []
for alpha, c in [(Fr(1, 4), Fr(1)), (Fr(1), Fr(1, 4)), (Fr(4), Fr(1, 16))]:
    eu, el = efrac_upper(c), efrac_lower(c)
    with open(f'fig4_tail_a{alpha.numerator}_{alpha.denominator}.dat', 'w') as f, \
         open(f'fig4_bound_a{alpha.numerator}_{alpha.denominator}.dat', 'w') as g:
        f.write('N log10T\n'); g.write('N log10B\n')
        for N in range(0, 21):
            K = N + 80
            S = sum(c**n / (math.factorial(n) * (2 * n + 1)) for n in range(N, K))
            up = S + c**K * eu / math.factorial(K)
            B_lo = el * c**N / math.factorial(N)
            assert up <= B_lo, (alpha, N)          # Theorem 8.1 inequality, checked exactly
            lo10 = math.log10(S); up10 = math.log10(up)
            assert up10 - lo10 < 1e-12
            f.write(f'{N} {lo10:.10f}\n')
            g.write(f'{N} {math.log10(float(el*c**N/math.factorial(N))):.10f}\n')
            report.append(f'alpha={alpha} N={N} T_N in [{float(S):.6e}, {float(up):.6e}] <= e^c c^N/N! >= {float(B_lo):.6e}')
open('fig4_tail_certificate.txt', 'w').write('\n'.join(report) + '\n')
print('ok', len(report))
