#!/usr/bin/env python3
"""Manuscript 14, Remark 4.4 (Ising readings of the Langevin dipole and of the Eulerian ensemble).

Certificates in exact rational arithmetic and in Arb balls at 2000 bits for the identities of the remark:

  (A) descents of a uniform permutation, n = 2..9, by exhaustive enumeration: E[D_i] = 1/2,
      E[s_i s_{i+1}] = -1/3, E[s_i s_j] = 0 for |i-j| >= 2 (s_i = 2 D_i - 1), all correlation
      functions rho(A) = prod over blocks of 1/(a+1)! (Borodin-Diaconis-Fulman, Remark (4) after
      Theorem 5.1), Var(des) = (n+1)/12, and the law of des equal to Eulerian numbers / n!;
  (B) Var(des) = (n+1)/12 and the symmetry of the Eulerian numbers for every n = 2..670 (the range
      of Figure 2), from the exact recurrence;
  (C) the descent kernel: k(m) = -B_{m+1}/(m+1)! as the Laurent coefficients of 1/(1-e^z); the block
      determinants det[k(j-i)]_{a x a} = 1/(a+1)!; the identity 1/(1-e^z) = 1/2 - 1/z - L(z/2)/2
      coefficientwise (k(2m-1) = -2^{-2m} [y^{2m-1}] L(y), k(2m) = 0 for m >= 1) and in Arb at four
      points; -4 k(1) k(-1) = -1/3; the eight terms of (78) equal -k(2m-1)/(m 2^{m+1});
  (D) the binary (Ising) decomposition of the Langevin dipole at x = a = 1/sqrt 8 and x = b = 1/sqrt 2:
      sinh(x)/x = prod cosh(x/2^k), L(x) = sum 2^-k tanh(x/2^k), L'(x) = sum 4^-k sech^2(x/2^k),
      with K = 1100 factors and rigorous tail bounds below 2^-2190; the printed fifty-digit values
      (41), (42) reproduced with certified rounding; the first-step identities sinh(2x)/(2x) =
      cosh(x) sinh(x)/x, 2L(2x) = L(x) + tanh(x), 4L'(2x) = L'(x) + sech^2(x) at x = a;
  (E) Harper's reading: for n = 3..18 the Eulerian polynomial has n-1 distinct negative real zeros,
      certified by exact sign changes; each zero is bracketed to 2^-200 by exact bisection, and from
      the brackets Arb proves sum p_j = (n-1)/2, sum p_j (1-p_j) = (n+1)/12 with p_j = 1/(1-alpha_j),
      and, at u = e^{H_0}, the tilted mean 1 + sum u/(u - alpha_j) equal to the direct Eulerian sum;
  (F) the n-vector single-spin partition functions: the coefficients 1/(k! (lambda+1)_k (4^k)) of
      (eq:nvector) are 1/(2k+1)! at lambda = 1/2 and 1/(2k)! at lambda = -1/2, the moments
      (1/2)_k/(lambda+1)_k are those of the uniform law (lambda = 1/2) and of the arcsine law
      (lambda = 0), and the series equals sinh(x)/x and cosh(x) in Arb at x = a, b.
Requires python-flint 0.9.0 (as the other workflows).
"""
from fractions import Fraction as Q
from itertools import permutations
from math import factorial, comb
import sys
import flint
from flint import arb, ctx

PREC = 2000
ctx.prec = PREC
sys.set_int_max_str_digits(0)
failures = []
npass = 0

def check(desc, cond):
    global npass
    ok = bool(cond)
    print(f"{'PASS' if ok else 'FAIL'}: {desc}")
    if ok:
        npass += 1
    else:
        failures.append(desc)

def qball(q):
    q = Q(q)
    return arb(q.numerator) / arb(q.denominator)

print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, Arb precision {ctx.prec} bits")

# ------------------------------------------------------------------ Eulerian numbers (exact)
def eulerian_rows(nmax):
    """rows[n][d] = number of permutations of n elements with d descents, n = 1..nmax."""
    rows = {1: [1]}
    for n in range(2, nmax + 1):
        prev = rows[n - 1]
        row = [0] * n
        for d in range(n):
            a = (d + 1) * prev[d] if d < n - 1 else 0
            b = (n - d) * prev[d - 1] if d >= 1 else 0
            row[d] = a + b
        rows[n] = row
    return rows

ROWS = eulerian_rows(670)

# ------------------------------------------------------------------ (A) exhaustive enumeration
def block_rho(A):
    """prod over maximal blocks of consecutive integers in A of 1/(a+1)!"""
    A = sorted(A)
    r = Q(1)
    i = 0
    while i < len(A):
        j = i
        while j + 1 < len(A) and A[j + 1] == A[j] + 1:
            j += 1
        r /= factorial(j - i + 2)
        i = j + 1
    return r

for n in range(2, 10):
    m = n - 1
    hist = [0] * (1 << m)                     # histogram of descent masks
    for p in permutations(range(n)):
        mask = 0
        for i in range(m):
            if p[i] > p[i + 1]:
                mask |= 1 << i
        hist[mask] += 1
    N = factorial(n)
    # correlation functions rho(A) = P(D_i = 1 for all i in A)
    sup = hist[:]                              # superset sums
    for bit in range(m):
        for mask in range(1 << m):
            if not mask & (1 << bit):
                sup[mask] += sup[mask | (1 << bit)]
    ok_rho = all(Q(sup[mask], N) == block_rho([i for i in range(m) if mask >> i & 1])
                 for mask in range(1 << m))
    check(f"n={n}: all 2^{m} correlation functions rho(A) = prod 1/(a+1)! (one-dependent determinantal law)", ok_rho)
    ED = [Q(sup[1 << i], N) for i in range(m)]
    check(f"n={n}: E[D_i] = 1/2 for every i", all(e == Q(1, 2) for e in ED))
    if m >= 2:
        # E[s_i s_j] = 4 rho({i,j}) - 2 E D_i - 2 E D_j + 1
        def Ess(i, j):
            return 4 * Q(sup[(1 << i) | (1 << j)], N) - 2 * ED[i] - 2 * ED[j] + 1
        check(f"n={n}: E[s_i s_(i+1)] = -1/3 for every i", all(Ess(i, i + 1) == Q(-1, 3) for i in range(m - 1)))
        if m >= 3:
            check(f"n={n}: E[s_i s_j] = 0 for every |i-j| >= 2",
                  all(Ess(i, j) == 0 for i in range(m) for j in range(i + 2, m)))
    des_law = [0] * n
    for mask in range(1 << m):
        des_law[bin(mask).count('1')] += hist[mask]
    check(f"n={n}: law of des equals the Eulerian numbers", des_law == ROWS[n])
    mean = Q(sum(d * c for d, c in enumerate(des_law)), N)
    var = Q(sum(d * d * c for d, c in enumerate(des_law)), N) - mean * mean
    check(f"n={n}: Var(des) = (n-1)/4 - (n-2)/6 = (n+1)/12", var == Q(n + 1, 12) == Q(n - 1, 4) - Q(n - 2, 6))

# ------------------------------------------------------------------ (B) every n up to 670
okB_var = okB_sym = okB_sum = True
for n in range(2, 671):
    row = ROWS[n]
    N = factorial(n)
    okB_sum &= (sum(row) == N)
    okB_sym &= all(row[d] == row[n - 1 - d] for d in range(n))
    s1 = sum(d * c for d, c in enumerate(row))
    s2 = sum(d * d * c for d, c in enumerate(row))
    okB_var &= (Q(s2, N) - Q(s1, N) ** 2 == Q(n + 1, 12))
check("n = 2..670: Eulerian rows sum to n!", okB_sum)
check("n = 2..670: Eulerian numbers symmetric (zeros in reciprocal pairs)", okB_sym)
check("n = 2..670: Var(des) = (n+1)/12 exactly", okB_var)

# ------------------------------------------------------------------ (C) the descent kernel
M = 44
# E(z) = (e^z - 1)/z = sum z^j/(j+1)!, and 1/E(z) = z/(e^z - 1) = sum c_j z^j
Ecoef = [Q(1, factorial(j + 1)) for j in range(M + 2)]
c = [Q(0)] * (M + 2)
c[0] = Q(1)
for j in range(1, M + 2):
    c[j] = -sum(Ecoef[i] * c[j - i] for i in range(1, j + 1))
def bernoulli_list(nn):
    A = [Q(0)] * (nn + 1); B = []
    for mm in range(nn + 1):
        A[mm] = Q(1, mm + 1)
        for jj in range(mm, 0, -1):
            A[jj - 1] = jj * (A[jj - 1] - A[jj])
        B.append(A[0])
    return B
B = bernoulli_list(M + 2)
B[1] = Q(-1, 2)                                  # z/(e^z-1) convention
check("z/(e^z-1) = sum B_j z^j / j! (exact, j <= 45)", all(c[j] == B[j] / factorial(j) for j in range(M + 2)))
# 1/(1-e^z) = -(1/z) * z/(e^z-1): k(m) = -c_{m+1}, m >= -1
def k(mm):
    return Q(0) if mm < -1 else -c[mm + 1]
check("k(-1) = -1, k(0) = 1/2, k(1) = -1/12, k(2) = 0, k(3) = 1/720",
      (k(-1), k(0), k(1), k(2), k(3)) == (Q(-1), Q(1, 2), Q(-1, 12), Q(0), Q(1, 720)))
check("k(m) = -B_(m+1)/(m+1)! for m = 0..43", all(k(mm) == -B[mm + 1] / factorial(mm + 1) for mm in range(0, M)))

def det_frac(Mx):
    Mx = [row[:] for row in Mx]
    nn = len(Mx); d = Q(1)
    for col in range(nn):
        piv = next((r for r in range(col, nn) if Mx[r][col] != 0), None)
        if piv is None:
            return Q(0)
        if piv != col:
            Mx[col], Mx[piv] = Mx[piv], Mx[col]; d = -d
        d *= Mx[col][col]
        for r in range(col + 1, nn):
            f = Mx[r][col] / Mx[col][col]
            if f:
                for cc in range(col, nn):
                    Mx[r][cc] -= f * Mx[col][cc]
    return d
check("block determinants det[k(j-i)] (a x a) = 1/(a+1)!, a = 1..12",
      all(det_frac([[k(j - i) for j in range(a)] for i in range(a)]) == Q(1, factorial(a + 1)) for a in range(1, 13)))
# Langevin Taylor coefficients: L(y) = sum_{m>=1} 2^{2m} B_{2m} y^{2m-1}/(2m)!
Lcoef = {2 * mm - 1: Q(2 ** (2 * mm)) * B[2 * mm] / factorial(2 * mm) for mm in range(1, 21)}
check("L(y) = y/3 - y^3/45 + 2 y^5/945 - ... (first three coefficients)",
      (Lcoef[1], Lcoef[3], Lcoef[5]) == (Q(1, 3), Q(-1, 45), Q(2, 945)))
check("(eq:descent-kernel) coefficientwise: k(2m-1) = -2^(-2m) [y^(2m-1)] L(y), m = 1..20",
      all(k(2 * mm - 1) == -Lcoef[2 * mm - 1] / 2 ** (2 * mm) for mm in range(1, 21)))
check("(eq:descent-kernel) even part: k(0) = 1/2 and k(2m) = 0 for m = 1..21", k(0) == Q(1, 2) and all(k(2 * mm) == 0 for mm in range(1, 22)))
check("nearest-neighbour entry k(1) = -(1/4) L'(0) and -4 k(1) k(-1) = -1/3",
      k(1) == -Lcoef[1] / 4 and -4 * k(1) * k(-1) == Q(-1, 3))
stated78 = [Q(1, 48), Q(-1, 11520), Q(1, 1451520), Q(-1, 154828800), Q(1, 15328051200),
            Q(-691, 1004293914624000), Q(1, 133905855283200), Q(-3617, 43706871164436480000)]
check("coefficients of (78) equal -k(2m-1)/(m 2^(m+1)), m = 1..8",
      all(-k(2 * mm - 1) / (mm * 2 ** (mm + 1)) == stated78[mm - 1] for mm in range(1, 9)))

def langevin(x):
    return x.cosh() / x.sinh() - 1 / x
a = arb(8).rsqrt()
b = arb(2).rsqrt()
for name, z in (("2a", 2 * a), ("2b", 2 * b), ("1", arb(1)), ("-3", arb(-3))):
    lhs = 1 / (1 - z.exp())
    rhs = qball(Q(1, 2)) - 1 / z - langevin(z / 2) / 2
    check(f"(eq:descent-kernel) in Arb at z = {name}", (lhs - rhs).overlaps(arb(0)) and abs(lhs - rhs) < arb(2) ** (-1950))

# ------------------------------------------------------------------ (D) binary decomposition
K = 1100
tiny = arb(2) ** (-1960)
for name, x in (("a", a), ("b", b)):
    logr = (x.sinh() / x).log()
    P = arb(0); Ls = arb(0); Vs = arb(0)
    two_k = arb(1)
    for kk in range(1, K + 1):
        two_k = two_k * 2
        y = x / two_k
        P += y.cosh().log()
        Ls += y.tanh() / two_k
        ch = y.cosh()
        Vs += 1 / (ch * ch * two_k * two_k)
    # tails: 0 <= sum_{k>K} log cosh(x/2^k) <= x^2 4^-K / 6 ; tanh(y) <= y ; sech^2 <= 1
    t1 = x * x / (arb(4) ** K * 6); t2 = x / (arb(4) ** K * 3); t3 = 1 / (arb(4) ** K * 3)
    check(f"x={name}: tail bounds of (eq:binary-product)-(eq:binary-variance) below 2^-2190",
          t1 < arb(2) ** (-2190) and t2 < arb(2) ** (-2190) and t3 < arb(2) ** (-2190))
    check(f"x={name}: log(sinh x/x) = sum_k log cosh(x/2^k)  (K={K}, |diff| < 2^-1960)", abs(logr - P) < tiny)
    check(f"x={name}: L(x) = sum_k 2^-k tanh(x/2^k)", abs(langevin(x) - Ls) < tiny)
    Lp = 1 / (x * x) - 1 / (x.sinh() ** 2)
    check(f"x={name}: L'(x) = sum_k 4^-k sech^2(x/2^k)", abs(Lp - Vs) < tiny)
    if name == "a":
        Ls_a, Vs_a = Ls, Vs

def rounded(desc, x, printed):
    center = Q(printed)
    places = len(printed.partition('.')[2])
    half = Q(1, 2 * 10 ** places)
    check(f"{desc} correctly rounded to {places} places", x > qball(center - half) and x < qball(center + half))
rounded("(41) from the binary series sum 2^-k tanh(a/2^k)", Ls_a, "0.11688058470393301970853181386179164401493872379933")
rounded("(42) from the binary series sum 4^-k sech^2(a/2^k)", Vs_a, "0.32516249665366914396163376385083845935142050373689")

x = a
check("first factor: sinh(2a)/(2a) = cosh(a) sinh(a)/a (modular duplication)",
      abs((2 * x).sinh() / (2 * x) - x.cosh() * x.sinh() / x) < tiny)
check("first term: 2 L(2a) = L(a) + tanh(a) (eq:companion-langevin)",
      abs(2 * langevin(2 * x) - langevin(x) - x.tanh()) < tiny)
Lp1 = lambda t: 1 / (t * t) - 1 / (t.sinh() ** 2)
check("first term: 4 L'(2a) = L'(a) + sech^2(a) (eq:companion-variance)",
      abs(4 * Lp1(2 * x) - Lp1(x) - 1 / (x.cosh() ** 2)) < tiny)

# ------------------------------------------------------------------ (E) Harper's reading
def poly_sign_scaled(coeffs, num, den):
    """sign of p(-num/den) for integer coeffs (increasing degree): Horner on den^deg p(-num/den), exact integers."""
    deg = len(coeffs) - 1
    v = coeffs[deg]
    dp = 1
    for d in range(deg - 1, -1, -1):
        dp *= den
        v = v * (-num) + coeffs[d] * dp
    return (v > 0) - (v < 0)

def poly_eval_frac(coeffs, t):
    v = Q(0)
    for cf in reversed(coeffs):
        v = v * t + cf
    return v

r_num, r_den = 33, 32                 # grid t_j = -(33/32)^j
for n in range(3, 19):
    coeffs = ROWS[n]                  # E_n(u) = sum_d A(n,d) u^d, degree n-1
    deg = n - 1
    jmax = int((n + 2) * 0.6931471805599453 / 0.030771658666753687) + 2   # covers |log2 t| <= n+2; all zeros lie in [-2^n, -2^-n]
    brackets = []
    prev_s = None; prev_t = None
    for j in range(-jmax, jmax + 1):
        if j >= 0:
            num, den = r_num ** j, r_den ** j
        else:
            num, den = r_den ** (-j), r_num ** (-j)
        s = poly_sign_scaled(coeffs, num, den)
        t = Q(-num, den)
        if s == 0:
            brackets.append((t, t)); prev_s = None; continue
        if prev_s is not None and s != prev_s:
            brackets.append((t, prev_t))           # t < prev_t (more negative first)
        prev_s, prev_t = s, t
    check(f"n={n}: {deg} distinct negative real zeros of the Eulerian polynomial (exact sign changes)",
          len(brackets) == deg)
    # bisection to 2^-200 relative to the scale of each bracket
    roots = []
    for lo, hi in brackets:
        slo = poly_eval_frac(coeffs, lo)
        for _ in range(200):
            mid = (lo + hi) / 2
            smid = poly_eval_frac(coeffs, mid)
            if smid == 0:
                lo = hi = mid; break
            if (smid > 0) == (slo > 0):
                lo, slo = mid, smid
            else:
                hi = mid
        # ball containing the zero: the union of the two exact endpoints
        roots.append(qball(lo).union(qball(hi)))
    ps = [1 / (1 - al) for al in roots]
    check(f"n={n}: sum_j p_j = (n-1)/2 with p_j = 1/(1-alpha_j)", abs(sum(ps, arb(0)) - qball(Q(n - 1, 2))) < arb(2) ** (-150))
    var = sum((p * (1 - p) for p in ps), arb(0))
    check(f"n={n}: sum_j p_j (1-p_j) = (n+1)/12 (independent Ising spins reproduce the Eulerian variance)",
          abs(var - qball(Q(n + 1, 12))) < arb(2) ** (-150))
    u = (-1 / arb(2).sqrt()).exp()          # u = e^{H_0}
    direct_num = sum((qball(cf) * (d + 1) * u ** (d + 1) for d, cf in enumerate(coeffs)), arb(0))
    direct_den = sum((qball(cf) * u ** (d + 1) for d, cf in enumerate(coeffs)), arb(0))
    harper = 1 + sum((u / (u - al) for al in roots), arb(0))
    check(f"n={n}: tilted mean at u = e^(H_0): 1 + sum u/(u-alpha_j) = sum k p_(n,k) u^k / A_n(u)",
          abs(harper - direct_num / direct_den) < arb(2) ** (-150))

# ------------------------------------------------------------------ (F) n-vector partition functions
def poch(z, kk):
    r = Q(1)
    for i in range(kk):
        r *= z + i
    return r
check("lambda = 1/2: 1/(k! (3/2)_k 4^k) = 1/(2k+1)!, k = 0..60",
      all(Q(1) / (factorial(kk) * poch(Q(3, 2), kk) * 4 ** kk) == Q(1, factorial(2 * kk + 1)) for kk in range(61)))
check("lambda = -1/2: 1/(k! (1/2)_k 4^k) = 1/(2k)!, k = 0..60",
      all(Q(1) / (factorial(kk) * poch(Q(1, 2), kk) * 4 ** kk) == Q(1, factorial(2 * kk)) for kk in range(61)))
check("moments (1/2)_k/(lambda+1)_k: uniform law 1/(2k+1) at lambda = 1/2, arcsine law C(2k,k)/4^k at lambda = 0",
      all(poch(Q(1, 2), kk) / poch(Q(3, 2), kk) == Q(1, 2 * kk + 1) and
          poch(Q(1, 2), kk) / poch(Q(1), kk) == Q(comb(2 * kk, kk), 4 ** kk) for kk in range(61)))
for name, x in (("a", a), ("b", b)):
    s_half = arb(0); s_mhalf = arb(0); term_h = arb(1); term_m = arb(1)
    x2 = x * x / 4
    for kk in range(0, 400):
        if kk > 0:
            term_h = term_h * x2 / (kk * qball(Q(1, 2) + kk))
            term_m = term_m * x2 / (kk * qball(Q(-1, 2) + kk))
        s_half += term_h; s_mhalf += term_m
    check(f"x={name}: series of (eq:nvector) at lambda = 1/2 equals sinh(x)/x", abs(s_half - x.sinh() / x) < tiny)
    check(f"x={name}: series of (eq:nvector) at lambda = -1/2 equals cosh(x)", abs(s_mhalf - x.cosh()) < tiny)

print(f"python-flint {flint.__version__}, precision {ctx.prec} bits")
if failures:
    print(f"FAILED: {len(failures)} check(s)"); sys.exit(1)
print(f"ALL {npass} REMARK 4.4 ISING-READING CHECKS PASSED AT 2000 BITS")
