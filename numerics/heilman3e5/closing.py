#!/usr/bin/env python3
"""
closing.py -- exact rational closing step of the certification K_G <= K_Kr - 3e-5
for Heilman's 2D graph-threshold profiles, and generator of the Lean 4 file
lean/Heilman/Heilman3e5Closing.lean that re-checks every inequality in the kernel.

Inputs
  out/bounds.txt  (written by `certify ... 3e-5 out/bounds.txt`):
     Psup m 15      upper bound of sup_{|zeta|=s} |sum_{j<=J} phi_j zeta^j|, as m * 10^-15
     bU n m 40      upper bound of |b_n|, odd n <= 199, as m * 10^-40
     bL n m 40      lower bound of |b_n|
  out/mbound.log  (written by `mbound 1.10 2000 256 128`): M'_up_1e-10 m, M' <= m * 10^-10
Constants with outside provenance (as in lean/Heilman/AppendixA231.lean):
  3.14159265358979323846 < pi < 3.14159265358979323847   (Mathlib Real.pi_gt_d20, Real.pi_lt_d20)
Everything else is proved here and in Lean from these numbers by rational arithmetic:
  asinh(1) = log(1 + sqrt 2) lies in (L_lo, L_hi): exp-series bounds, squared against 2;
  sinh(51/50) <= sh_up: series plus a geometric tail.

Every check is an exact Fraction comparison.  Usage: python3 closing.py [--lean PATH]
"""
import sys, re
from fractions import Fraction as F
from math import factorial

HERE = __file__.rsplit('/', 1)[0] if '/' in __file__ else '.'

def dec(m, e):
    return F(m, 10 ** e)

def ceil_dec(x, e):
    n = -((-x.numerator * 10 ** e) // x.denominator)
    return n

def floor_dec(x, e):
    return (x.numerator * 10 ** e) // x.denominator

def horner(cs, y):
    acc = F(0)
    for c in reversed(cs):
        acc = c + y * acc
    return acc

# ---------------- inputs ----------------
bU, bL, Psup_m = {}, {}, None
for line in open(f'{HERE}/out/bounds.txt'):
    if line.startswith('#'):
        continue
    t = line.split()
    if t[0] == 'Psup':
        Psup_m = int(t[1]); assert t[2] == '15'
    elif t[0] in ('bU', 'bL'):
        n, m, e = int(t[1]), int(t[2]), int(t[3]); assert e == 40
        (bU if t[0] == 'bU' else bL)[n] = m
odd = list(range(1, 200, 2))
assert sorted(bU) == odd and sorted(bL) == odd
Mp_in = int(re.search(r"M'_up_1e-10 (\d+)", open(f'{HERE}/out/mbound.log').read()).group(1))

checks = []
def check(name, ok):
    checks.append((name, ok)); print(f"  [{'ok' if ok else 'FAIL'}] {name}")

pi_lo, pi_hi = dec(314159265358979323846, 20), dec(314159265358979323847, 20)
eps = F(3, 100000)
s, rho = F(51, 50), F(11, 10)
N = J = 200

# asinh(1) bounds: L_hi > L  <=>  exp(L_hi) - 1 > sqrt2  <=  T(L_hi)^2 > 2, T = sum_{k=1}^{40} x^k/k!
L_hi, L_lo = dec(88137358701954302524, 20), dec(88137358701954302523, 20)
def Texp(x, K):
    return sum(x ** k / factorial(k) for k in range(1, K + 1))
# upper bound of exp(x) - 1 for 0 < x < 1: T_K(x) + 2 x^{K+1}/(K+1)!
check('L_hi > asinh 1   [T_40(L_hi)^2 > 2]', Texp(L_hi, 40) ** 2 > 2)
check('L_lo < asinh 1   [(T_40(L_lo) + 2 L_lo^41/41!)^2 < 2]', (Texp(L_lo, 40) + 2 * L_lo ** 41 / factorial(41)) ** 2 < 2)

# gamma_t = pi L/(pi - 2 eps L) <= pi_lo L_hi/(pi_lo - 2 eps L_hi) =: <= g_up
g_exact_up = pi_lo * L_hi / (pi_lo - 2 * eps * L_hi)
g_up = dec(ceil_dec(g_exact_up, 20), 20)
check('gamma_t <= g_up   [pi_lo L_hi + 2 eps L_hi g_up <= g_up pi_lo]', pi_lo * L_hi + 2 * eps * L_hi * g_up <= g_up * pi_lo)

# sinh(s) <= sh_up: sum_{k<=15} s^{2k+1}/(2k+1)! + 2 s^33/33!
sh_ser = sum(s ** (2 * k + 1) / factorial(2 * k + 1) for k in range(16)) + 2 * s ** 33 / factorial(33)
sh_up = dec(ceil_dec(sh_ser, 15), 15)
check('sinh(51/50) <= sh_up', sh_ser <= sh_up)

# M' and delta
Mp = F(231, 10)
check("M' (mbound) <= 23.1", dec(Mp_in, 10) <= Mp)
Psup = dec(Psup_m, 15)
delta_ser = Psup + Mp * (s / rho) ** (J + 1) / (1 - s / rho)
delta_r = dec(ceil_dec(delta_ser, 12), 12)
check('delta := Psup + M (s/rho)^201 / (1 - s/rho) <= delta_r', delta_ser <= delta_r)
Rp = dec(floor_dec(s - delta_r - dec(1, 10), 12), 12)
check("R' + delta_r + 1e-10 <= s", Rp + delta_r + dec(1, 10) <= s)

def tail(g):
    # sinh(s) q^{N+1}/(1-q), q = g/R'  =  sh g^201 / (R'^200 (R' - g))
    assert g < Rp
    return sh_up * g ** (N + 1) / (Rp ** N * (Rp - g))

def A_up(g):
    return g * horner([dec(bU[n], 40) for n in odd], g * g)

def A_lo(g):
    return g * horner([dec(bL[n], 40) for n in odd], g * g)

# main target
A1 = A_up(g_up); A1r = dec(ceil_dec(A1, 20), 20)
T1 = tail(g_up); T1r = dec(ceil_dec(T1, 20), 20)
check('g_up < R\'', g_up < Rp)
check('A_N(g_up) <= A1r', A1 <= A1r)
check('tail(g_up) <= T1r', T1 <= T1r)
check('A1r + T1r < 1   ==> A(gamma_t) < 1 ==> K_G <= K_Kr - 3e-5', A1r + T1r < 1)
print(f"    A_N(gamma_t^+) <= {float(A1r):.15f},  tail <= {float(T1r):.3e},  1 - (A + tail) >= {float(1 - A1r - T1r):.6e}")

# existence of the root (not needed for the bound): A_N(0.9) > 1 with 0.9 < R'
check('0.9 < R\' and 1 < A_N(0.9) (lower bounds)', F(9, 10) < Rp and 1 < A_lo(F(9, 10)))

# two-sided enclosure of c* and the best eps
g_lo = dec(881388982611894, 15)    # from the bisection in certify.c, truncated
g_hi = dec(881388982617856, 15)
A2, T2 = A_up(g_lo), tail(g_lo)
check('A_N(g_lo) + tail(g_lo) < 1   ==> c* > g_lo', A2 + T2 < 1)
check('A_N(g_hi) > 1 (lower bounds)  ==> c* < g_hi', A_lo(g_hi) > 1)
Kb = dec(ceil_dec(pi_hi / (2 * g_lo), 15), 15)
check('pi/(2 g_lo) <= Kb', pi_hi <= 2 * g_lo * Kb)
eps_lo = dec(floor_dec(pi_lo / (2 * L_hi) - Kb, 15), 15)
check('Kb + eps_lo <= K_Kr', Kb + eps_lo <= pi_lo / (2 * L_hi))
eps_hi = dec(ceil_dec(pi_hi / (2 * L_lo) - pi_lo / (2 * g_hi), 15), 15)
check('K_Kr - pi/(2 g_hi) <= eps_hi', pi_hi / (2 * L_lo) <= eps_hi + pi_lo / (2 * g_hi))
print(f"    K_G <= Kb = {Kb * 10**15}e-15 = K_Kr - eps with eps >= eps_lo = {eps_lo * 10**15}e-15")
print(f"    the series bound pi/(2c*) of these profiles is K_Kr - eps*, eps_lo < eps* < eps_hi = {eps_hi * 10**15}e-15")

nok = sum(ok for _, ok in checks)
print(f"{nok}/{len(checks)} checks pass")

# ---------------- Lean generator ----------------
def qdec(x, e):
    m = x * 10 ** e
    assert m.denominator == 1
    return f"dec {m.numerator} {e}"

if '--lean' in sys.argv:
    path = sys.argv[sys.argv.index('--lean') + 1]
    bU_list = ', '.join(str(bU[n]) for n in odd)
    bL_list = ', '.join(str(bL[n]) for n in odd)
    lean = f'''/-
  Closing step of the certification of Heilman's 2D graph-threshold improvement
  K_G ≤ K_Kr − 3·10⁻⁵ (numerics/heilman3e5).

  Core Lean 4 only: no Mathlib, no `native_decide`. Every theorem is an inequality between
  nonnegative rationals, encoded as (numerator, denominator) pairs and checked by the kernel
  with `decide +kernel`. numerics/heilman3e5/closing.py generates this file and re-evaluates
  every statement with Python Fractions.

  Inputs (rigorous, from Arb ball arithmetic; see numerics/heilman3e5/README.md):
    bU n, bL n : upper and lower bounds of |b_n| (odd n ≤ 199), b_n = [wⁿ] H⁻¹(w), × 10⁻⁴⁰
    Psup       : upper bound of sup_{{|ζ|=51/50}} |Σ_{{j≤200}} φ_j ζ^j|, × 10⁻¹⁵   (certify.c)
    M'         : sup_{{|ζ|=11/10}} |E(sin ζ)| ≤ {Mp_in}·10⁻¹⁰                    (mbound.c)
    π ∈ (3.14159265358979323846, 3.14159265358979323847)   (Mathlib Real.pi_gt_d20, Real.pi_lt_d20)
  Proved here from these: asinh 1 = log(1 + √2) ∈ (L_lo, L_hi) by exp-series bounds,
  sinh(51/50) ≤ sh_up by its series, and the closing inequalities.
-/
namespace Heilman3e5

/-- A nonnegative rational as a (numerator, denominator) pair. -/
structure Q where
  num : Nat
  den : Nat

def Q.Lt (a b : Q) : Prop := a.num * b.den < b.num * a.den
def Q.Le (a b : Q) : Prop := a.num * b.den ≤ b.num * a.den
def Q.Eq (a b : Q) : Prop := a.num * b.den = b.num * a.den

instance (a b : Q) : Decidable (Q.Lt a b) := Nat.decLt _ _
instance (a b : Q) : Decidable (Q.Le a b) := Nat.decLe _ _
instance (a b : Q) : Decidable (Q.Eq a b) := Nat.decEq _ _

instance : Add Q := ⟨fun a b => ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩⟩
instance : Mul Q := ⟨fun a b => ⟨a.num * b.num, a.den * b.den⟩⟩
instance : Div Q := ⟨fun a b => ⟨a.num * b.den, a.den * b.num⟩⟩
instance : HPow Q Nat Q := ⟨fun a k => ⟨a.num ^ k, a.den ^ k⟩⟩
instance {{n : Nat}} : OfNat Q n := ⟨⟨n, 1⟩⟩

def fr (a b : Nat) : Q := ⟨a, b⟩
/-- `dec m e` is m · 10^(−e). -/
def dec (m e : Nat) : Q := ⟨m, 10 ^ e⟩

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Σ_{{k=1}}^{{K}} x^k / k!  (so exp x − 1 ≥ this for x ≥ 0). -/
def expm1Lo (x : Q) : Nat → Q
  | 0 => 0
  | k + 1 => expm1Lo x k + x ^ (k + 1) / fr (fact (k + 1)) 1

/-- Σ_{{k=0}}^{{K}} x^(2k+1) / (2k+1)!. -/
def sinhPart (x : Q) : Nat → Q
  | 0 => x
  | k + 1 => sinhPart x k + x ^ (2 * k + 3) / fr (fact (2 * k + 3)) 1

/-- Horner evaluation c₀ + y(c₁ + y(c₂ + …)) of coefficients given as m · 10⁻⁴⁰. -/
def horner (y : Q) : List Nat → Q
  | [] => 0
  | c :: cs => dec c 40 + y * horner y cs

/-! ### Inputs -/

def πlo : Q := dec 314159265358979323846 20
def πhi : Q := dec 314159265358979323847 20
def Lhi : Q := {qdec(L_hi, 20)}
def Llo : Q := {qdec(L_lo, 20)}
def ε : Q := fr 3 100000
def s : Q := fr 51 50
def ρ' : Q := fr 11 10
def Mp : Q := fr 231 10
def Mp_in : Q := dec {Mp_in} 10
def Psup : Q := dec {Psup_m} 15
/-- Upper bounds of |b_n|, n = 1, 3, …, 199, × 10⁻⁴⁰. -/
def bU : List Nat := [{bU_list}]
/-- Lower bounds of |b_n|, n = 1, 3, …, 199, × 10⁻⁴⁰. -/
def bL : List Nat := [{bL_list}]

def gup : Q := {qdec(g_up, 20)}
def shup : Q := {qdec(sh_up, 15)}
def δr : Q := {qdec(delta_r, 12)}
def Rp : Q := {qdec(Rp, 12)}
def RmG : Q := {qdec(Rp - g_up, 20)}
def A1r : Q := {qdec(A1r, 20)}
def T1r : Q := {qdec(T1r, 20)}
def glo : Q := {qdec(g_lo, 15)}
def ghi : Q := {qdec(g_hi, 15)}
def RmGlo : Q := {qdec(Rp - g_lo, 15)}
def A2r : Q := {qdec(dec(ceil_dec(A2, 20), 20), 20)}
def T2r : Q := {qdec(dec(ceil_dec(T2, 20), 20), 20)}
def Kb : Q := {qdec(Kb, 15)}
def εlo : Q := {qdec(eps_lo, 15)}
def εhi : Q := {qdec(eps_hi, 15)}

/-! ### Constants -/

/-- exp(L_hi) − 1 > √2, hence L_hi > log(1 + √2) = asinh 1. -/
theorem Lhi_gt : Q.Lt 2 (expm1Lo Lhi 40 ^ 2) := by decide +kernel
/-- exp(L_lo) − 1 ≤ T₄₀ + 2 L_lo⁴¹/41! < √2, hence L_lo < asinh 1. -/
theorem Llo_lt : Q.Lt ((expm1Lo Llo 40 + fr 2 1 * Llo ^ 41 / fr (fact 41) 1) ^ 2) 2 := by decide +kernel
/-- γ_t = πL/(π − 2εL) ≤ g_up (γ_t increases in L and decreases in π). -/
theorem gamma_le : Q.Le (πlo * Lhi + 2 * ε * Lhi * gup) (gup * πlo) := by decide +kernel
/-- sinh(51/50) ≤ sh_up: partial sum to k = 15 plus 2·s³³/33! bounds the tail. -/
theorem sinh_le : Q.Le (sinhPart s 15 + fr 2 1 * s ^ 33 / fr (fact 33) 1) shup := by decide +kernel
theorem Mp_ge : Q.Le Mp_in Mp := by decide +kernel

/-! ### Rouché radius -/

/-- δ = Psup + M'(s/ρ')²⁰¹/(1 − s/ρ') ≤ δ_r, with s/ρ' = 51/55 and 1 − s/ρ' = 4/55. -/
theorem delta_le : Q.Le (Psup + Mp * fr 51 55 ^ 201 * fr 55 4) δr := by decide +kernel
theorem Rp_le : Q.Le (Rp + δr + dec 1 10) s := by decide +kernel
theorem RmG_eq : Q.Eq (RmG + gup) Rp := by decide +kernel

/-! ### Main inequality: A(γ_t) < 1 -/

/-- A_N(g_up) = g_up · Σ |b_{{2i+1}}| (g_up²)^i ≤ A1r. -/
theorem A_le : Q.Le (gup * horner (gup * gup) bU) A1r := by decide +kernel
/-- Σ_{{n>200}} |b_n| g_upⁿ ≤ sinh(s) q²⁰¹/(1 − q) = sh_up g_up²⁰¹/(R'²⁰⁰ (R' − g_up)) ≤ T1r. -/
theorem tail_le : Q.Le (shup * gup ^ 201 / (Rp ^ 200 * RmG)) T1r := by decide +kernel
theorem main : Q.Lt (A1r + T1r) 1 := by decide +kernel

/-! ### Existence of the root c* of A(c) = 1 (not needed for the bound) -/

theorem root_exists : Q.Lt (fr 9 10) Rp ∧ Q.Lt 1 (fr 9 10 * horner (fr 81 100) bL) := by decide +kernel

/-! ### Two-sided enclosure: g_lo < c* < g_hi -/

theorem RmGlo_eq : Q.Eq (RmGlo + glo) Rp := by decide +kernel
theorem A_lo_le : Q.Le (glo * horner (glo * glo) bU) A2r := by decide +kernel
theorem tail_lo_le : Q.Le (shup * glo ^ 201 / (Rp ^ 200 * RmGlo)) T2r := by decide +kernel
theorem best : Q.Lt (A2r + T2r) 1 := by decide +kernel
theorem above : Q.Lt 1 (ghi * horner (ghi * ghi) bL) := by decide +kernel
/-- K_G ≤ π/(2 g_lo) ≤ Kb. -/
theorem Kb_ge : Q.Le πhi (2 * glo * Kb) := by decide +kernel
/-- Kb + ε_lo ≤ π/(2 L_hi) ≤ K_Kr. -/
theorem eps_lo_le : Q.Le (2 * Lhi * (Kb + εlo)) πlo := by decide +kernel
/-- K_Kr − π/(2 g_hi) ≤ π_hi/(2 L_lo) − π_lo/(2 g_hi) ≤ ε_hi. -/
theorem eps_hi_ge : Q.Le (πhi / (2 * Llo)) (εhi + πlo / (2 * ghi)) := by decide +kernel

end Heilman3e5

#print axioms Heilman3e5.Lhi_gt
#print axioms Heilman3e5.Llo_lt
#print axioms Heilman3e5.gamma_le
#print axioms Heilman3e5.sinh_le
#print axioms Heilman3e5.Mp_ge
#print axioms Heilman3e5.delta_le
#print axioms Heilman3e5.Rp_le
#print axioms Heilman3e5.RmG_eq
#print axioms Heilman3e5.A_le
#print axioms Heilman3e5.tail_le
#print axioms Heilman3e5.main
#print axioms Heilman3e5.root_exists
#print axioms Heilman3e5.RmGlo_eq
#print axioms Heilman3e5.A_lo_le
#print axioms Heilman3e5.tail_lo_le
#print axioms Heilman3e5.best
#print axioms Heilman3e5.above
#print axioms Heilman3e5.Kb_ge
#print axioms Heilman3e5.eps_lo_le
#print axioms Heilman3e5.eps_hi_ge
'''
    open(path, 'w').write(lean)
    print(f"wrote {path}")

sys.exit(0 if nok == len(checks) else 1)
