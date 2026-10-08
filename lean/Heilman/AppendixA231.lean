/-
  Heilman's proof, Appendix A of "A second look at Braverman et al.'s Theorem":
  the role of the constant 231 = 2n + 1.

  Claim certified here: 231 is the optimum produced by the choices made in the proof
  (ρ = 1.152, M_φ, L, Δ, ε = 0.664 Δ/L), not an intrinsic constant.
  * n = 115 is the least n with tail(n) < ε/2, and n = 114 is impossible for every
    admissible ε (ε < Δ/L, which δ₀ > 0 requires).
  * 232 and 233 (and larger) give valid, weaker proofs: sign control holds strictly
    for k = 0..115 and δ₀ > 0.
  * With ε = Δ/(2L) the same procedure gives n = 116, i.e. 2n + 1 = 233.
  * At 231 itself, sign control at k = 115 holds with equality, so strictness needs
    sup|φ| < M_φ strictly on |z| = ρ. 230 violates it.
  * The printed rounding slips (A.39), (A.45)-(A.46), (A.47), (A.49), (A.66) are recorded.

  Core Lean 4 only: no Mathlib, no `native_decide`, no extra axioms. Every statement is a
  finite inequality between rationals, encoded as (numerator, denominator) pairs of
  naturals and checked by the kernel with `decide +kernel`.

  Inputs are the constants certified in numerics/heilman/appendixA_chain.py (exact rational
  interval arithmetic). For Δ the inputs are
    π ∈ (3.14159265358979323846, 3.14159265358979323847)  (Mathlib: Real.pi_gt_d20, Real.pi_lt_d20)
    √2 ∈ (slo, shi), with slo² < 2 < shi² proved below.
  Since Δ(η) = (η⁴/π)(400√2 − B₆η²/2880) with a positive bracket, Δ is increasing in √2 and
  decreasing in π. Hence the bounds on Δ below follow from those on π and √2.
  numerics/heilman/lean_mirror.py re-evaluates every statement with Python Fractions.
-/
namespace HeilmanA

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
instance {n : Nat} : OfNat Q n := ⟨⟨n, 1⟩⟩

/-- `fr a b` is a/b. -/
def fr (a b : Nat) : Q := ⟨a, b⟩

/-- `dec m e` is m · 10^(−e). -/
def dec (m e : Nat) : Q := ⟨m, 10 ^ e⟩
/-- `sci m e` is m · 10^e. -/
def sci (m e : Nat) : Q := ⟨m * 10 ^ e, 1⟩

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-! ### Order lemmas (used for the statement "n = 114 is impossible for every ε") -/

theorem Q.lt_trans {a b c : Q} (ha : 0 < a.den) (h1 : Q.Lt a b) (h2 : Q.Lt b c) :
    Q.Lt a c := by
  unfold Q.Lt at *
  have s1 : a.num * b.den * c.den ≤ b.num * a.den * c.den :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt h1)
  have s2 : b.num * c.den * a.den < c.num * b.den * a.den :=
    Nat.mul_lt_mul_of_pos_right h2 ha
  rw [Nat.mul_right_comm a.num, Nat.mul_right_comm b.num] at s1
  rw [Nat.mul_right_comm c.num] at s2
  exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt s1 s2)

theorem Q.not_lt_of_le {a b : Q} (h : Q.Le b a) : ¬ Q.Lt a b := by
  unfold Q.Lt Q.Le at *
  exact Nat.not_lt_of_ge h

/-! ### Constants of Appendix A -/

def ρ : Q := dec 1152 3                      -- 1.152
def Mφ : Q := dec 1550302861362 10           -- 155.0302861362
def L : Q := dec 341627465436 10             -- 34.1627465436
def ε : Q := dec 834296222775 34             -- 8.34296222775e-23 (A.60)
def Dl : Q := dec 429244734953 32            -- 4.29244734953e-21, printed lower bound for Δ (A.23)
def DlT : Q := dec 429244734953296 35        -- 4.29244734953296e-21, tighter lower bound for Δ
def Dh : Q := dec 429244734953300 35         -- 4.29244734953300e-21, upper bound for Δ
def Cs : Q := sci 184 18                     -- 1.84e20 ≥ C_r' under either formula, see (A.49)
def Cprinted : Q := sci 201664948 10         -- 2.01664948e18, value printed in (A.49)
def q : Q := dec 9 1 / ρ                     -- 0.9/ρ

/-- M_φ · Σ_{k ≥ n+1} q^(2k+1) = M_φ q^(2n+3)/(1 − q²), where 1 − q² = 399/1024. -/
def tail (n : Nat) : Q := Mφ * q ^ (2 * n + 3) / (fr 399 1024)

/-- p(m) = ρ^m / (2 · m! · M_φ). -/
def p (m : Nat) : Q := ρ ^ m / (fr (2 * fact m) 1 * Mφ)

/-- Sign control at index k: p · M_φ · ρ^−(2k+1) < 1/(2 (2k+1)!). -/
def SignCtl (m k : Nat) : Prop := Q.Lt (p m * Mφ / ρ ^ (2 * k + 1)) (fr 1 (2 * fact (2 * k + 1)))
instance (m k : Nat) : Decidable (SignCtl m k) := by unfold SignCtl; infer_instance

/-- L (C' p² + p ε): δ₀ = p Δ − L (C' p² + p ε). -/
def loss (m : Nat) (C : Q) : Q := L * (C * p m ^ 2 + p m * ε)

def p092 : Q := dec 466807077 10 / (2 * dec 1936822943625 10)     -- (A.38)-(A.39)
def p096 : Q := dec 371640256 10 / (2 * dec 3007944582777 10)     -- (A.41)-(A.42)

def η : Q := dec 290803934947 17             -- 2.90803934947e-6
def B6 : Q := sci 12843271408 7              -- 1.2843271408e17
def πlo : Q := dec 314159265358979323846 20
def πhi : Q := dec 314159265358979323847 20
def slo : Q := dec 14142135623730950488 19
def shi : Q := dec 14142135623730950489 19
def Bterm : Q := η ^ 4 * (B6 * η ^ 2 / 2880)

/-! ### Δ bounds -/

theorem sqrt2_bounds : Q.Lt (slo ^ 2) 2 ∧ Q.Lt 2 (shi ^ 2) := by decide +kernel
theorem Delta_bracket_pos : Q.Lt Bterm (η ^ 4 * (400 * slo)) := by decide +kernel
/-- Δ ≥ η⁴(400 slo − B₆η²/2880)/πhi ≥ Dl -/
theorem Delta_ge_Dl : Q.Le (Dl * πhi + Bterm) (η ^ 4 * (400 * slo)) := by decide +kernel
theorem Delta_ge_DlT : Q.Le (DlT * πhi + Bterm) (η ^ 4 * (400 * slo)) := by decide +kernel
/-- Δ ≤ η⁴(400 shi − B₆η²/2880)/πlo ≤ Dh -/
theorem Delta_le_Dh : Q.Le (η ^ 4 * (400 * shi)) (Dh * πlo + Bterm) := by decide +kernel

/-! ### The tail: n = 115 is the least admissible n -/

theorem q_eq : Q.Eq q (fr 25 32) := by decide +kernel
theorem one_sub_q_sq : Q.Eq (q ^ 2 + (fr 399 1024)) 1 := by decide +kernel

/-- tail(115) < ε/2 (A.62). -/
theorem tail_115 : Q.Lt (2 * tail 115) ε := by decide +kernel
/-- tail(114) ≥ ε/2: n = 114 fails for the ε of (A.60). -/
theorem tail_114 : Q.Le ε (2 * tail 114) := by decide +kernel
/-- tail(114) ≥ Dh/(2L) ≥ Δ/(2L). -/
theorem tail_114_Dh : Q.Le (Dh / L) (2 * tail 114) := by decide +kernel

/-- n = 114 is impossible for every ε below Dh/L. That includes every ε < Δ/L,
    which δ₀ > 0 requires: then tail(114) < ε/2 never holds. -/
theorem n114_impossible (e : Q) (h : Q.Lt e (Dh / L)) : ¬ Q.Lt (2 * tail 114) e := by
  intro H
  have hpos : 0 < (2 * tail 114).den := by decide +kernel
  exact Q.not_lt_of_le tail_114_Dh (Q.lt_trans hpos H h)

/-- With ε = Δ/(2L) (c = 1/2 instead of 0.664) the least n is 116, i.e. 2n + 1 = 233. -/
theorem c_half_116 :
    Q.Le ((fr 1 2) * Dl / L) (2 * tail 115) ∧ Q.Lt (2 * tail 116) ((fr 1 2) * Dl / L) := by
  decide +kernel

/-! ### Sign control (A.63) -/

theorem sign_231_strict : ∀ k, k < 115 → SignCtl 231 k := by decide +kernel
/-- At k = 115, p(231) gives equality: strictness needs sup|φ| < M_φ strictly. -/
theorem sign_231_eq_115 : Q.Eq (p 231 * Mφ / ρ ^ 231) (fr 1 (2 * fact 231)) := by decide +kernel
theorem sign_232 : ∀ k, k < 116 → SignCtl 232 k := by decide +kernel
theorem sign_233 : ∀ k, k < 116 → SignCtl 233 k := by decide +kernel
theorem sign_230_fails : ¬ SignCtl 230 115 := by decide +kernel

/-! ### δ₀ > 0 (A.66), with Δ ≥ DlT and C' ≤ 1.84e20 -/

theorem C_prime_le_Cs :
    Q.Le (2 * sci 407811339 8 / dec 92 2 * (fr 45 46) / (fr 1 46) ^ 2) Cs := by decide +kernel
theorem delta0_231 : Q.Le (loss 231 Cs + dec 40712310283 467) (p 231 * DlT) := by decide +kernel
theorem delta0_232 : Q.Le (loss 232 Cs + dec 20215 463) (p 232 * DlT) := by decide +kernel
theorem delta0_233 : Q.Le (loss 233 Cs + dec 99950 466) (p 233 * DlT) := by decide +kernel
theorem p_small :
    Q.Lt (p 231) p092 ∧ Q.Lt (p 231) p096 ∧ Q.Lt (p 232) p092 ∧ Q.Lt (p 232) p096 ∧
    Q.Lt (p 233) p092 ∧ Q.Lt (p 233) p096 := by decide +kernel

/-! ### Printed rounding slips (none affects the conclusion) -/

/-- (A.39): the true p_0.92 = 1.2050845394…e-4 is below the printed lower bound 1.20508454e-4. -/
theorem slip_A39 : Q.Lt p092 (dec 120508454 12) := by decide +kernel
/-- (A.45)-(A.46): 12 × 381.8015394237 = 4581.6184730844 exceeds the printed M = 4581.618473084. -/
theorem slip_A45 : Q.Lt (dec 4581618473084 9) (12 * dec 3818015394237 10) := by decide +kernel
/-- (A.47): 7.05228288411² < (6/7)² + 7², so the printed value is not an upper bound for R. -/
theorem slip_A47 : Q.Lt (dec 705228288411 11 ^ 2) ((fr 6 7) ^ 2 + 49) := by decide +kernel
/-- (A.49): the printed formula 2C_r/r·(0.9/r)·[1 − 0.9/r]⁻² exceeds the printed 2.01664948e18,
    which is instead the value of 2C_r/r·(0.9/r)·[1 − (0.9/r)²]⁻¹. Here 0.9/0.92 = 45/46. -/
theorem slip_A49 :
    Q.Lt Cprinted (2 * sci 407811339 8 / dec 92 2 * (fr 45 46) / (fr 1 46) ^ 2) ∧
    Q.Le (2 * sci 407811339 8 / dec 92 2 * (fr 45 46) / (fr 91 2116)) Cprinted := by decide +kernel
/-- (A.66): even with Δ ≤ Dh, δ₀(231) < 4.07123102832e-457, the printed lower bound. -/
theorem slip_A66 : Q.Lt (p 231 * Dh) (loss 231 Cprinted + dec 407123102832 468) := by
  decide +kernel

/-! ### Axiom audit
  Every kernel-checked fact depends on no axiom at all. `n114_impossible` uses only the
  three standard Lean axioms (propext, Classical.choice, Quot.sound), through core `Nat` lemmas. -/

#print axioms sqrt2_bounds
#print axioms Delta_bracket_pos
#print axioms Delta_ge_Dl
#print axioms Delta_ge_DlT
#print axioms Delta_le_Dh
#print axioms q_eq
#print axioms one_sub_q_sq
#print axioms tail_115
#print axioms tail_114
#print axioms tail_114_Dh
#print axioms n114_impossible
#print axioms c_half_116
#print axioms sign_231_strict
#print axioms sign_231_eq_115
#print axioms sign_232
#print axioms sign_233
#print axioms sign_230_fails
#print axioms C_prime_le_Cs
#print axioms delta0_231
#print axioms delta0_232
#print axioms delta0_233
#print axioms p_small
#print axioms slip_A39
#print axioms slip_A45
#print axioms slip_A47
#print axioms slip_A49
#print axioms slip_A66

end HeilmanA
