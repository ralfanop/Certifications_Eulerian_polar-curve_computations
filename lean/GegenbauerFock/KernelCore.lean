import Mathlib

/-!
# Gegenbauer–Fock: algebraic kernel certificates

Scope: finite algebraic identities. No analytic integral, Hilbert-space
operator or domain theorem is claimed in this module. The proofs are
intended for kernel checking by the repository CI.
-/

namespace GegenbauerFock

/-- Pointwise differential-symbol factor for the spheroidal exponential kernel. -/
def spheroidalFactor (lam c u v : ℝ) : ℝ :=
  -(1 - u ^ 2) * (c * v) ^ 2
    + (2 * lam + 1) * u * (c * v)
    - c ^ 2 * u ^ 2

theorem spheroidalFactor_swap (lam c u v : ℝ) :
    spheroidalFactor lam c u v = spheroidalFactor lam c v u := by
  unfold spheroidalFactor
  ring

theorem exponentialKernel_balance (lam c u v : ℝ) :
    spheroidalFactor lam c u v * Real.exp (c * u * v) =
      spheroidalFactor lam c v u * Real.exp (c * u * v) := by
  rw [spheroidalFactor_swap]

theorem ultrasphericalSymbol_difference (lam c u v : ℝ) :
    (-(1-u^2)*(c*v)^2 + (2*lam+1)*u*(c*v)) -
      (-(1-v^2)*(c*u)^2 + (2*lam+1)*v*(c*u)) =
      c^2*(u^2-v^2) := by
  ring

/-! The next theorem is a *symbol identity*, not integration by parts. -/

noncomputable def gegenbauerSourceSymbol (lam u z q : ℂ) : ℂ :=
  -(1-u^2) * (q*z/2)^2 + (2*lam+1)*u*(q*z/2)

noncomputable def gegenbauerTargetSymbol (lam u z q : ℂ) : ℂ :=
  z^2*(q*u/2)^2 + (2*lam+1)*z*(q*u/2) + z^2/4

theorem gegenbauerFourier_symbol (lam u z q : ℂ)
    (hq : q*q = -1) :
    gegenbauerSourceSymbol lam u z q =
      gegenbauerTargetSymbol lam u z q := by
  have hq2 : q ^ 2 = -1 := by simpa [pow_two] using hq
  have hz : (q*z/2)^2 = -(z^2)/4 := by
    calc
      (q*z/2)^2 = q^2*z^2/4 := by ring
      _ = -(z^2)/4 := by rw [hq2]; ring
  have hu : (q*u/2)^2 = -(u^2)/4 := by
    calc
      (q*u/2)^2 = q^2*u^2/4 := by ring
      _ = -(u^2)/4 := by rw [hq2]; ring
  unfold gegenbauerSourceSymbol gegenbauerTargetSymbol
  rw [hz, hu]
  ring

/-- Formal coefficient cancellation for the Gegenbauer--Bessel radial ODE. -/
theorem radialCoefficient_balance
    (lam a0 a1 : ℝ) (k : ℕ)
    (h : (16:ℝ) * ((k:ℝ)+1) * (lam+(k:ℝ)+1) * a1 + a0 = 0) :
    (4:ℝ) * ((k:ℝ)+1) * (lam+(k:ℝ)+1) * a1 + a0/4 = 0 := by
  calc
    (4:ℝ)*((k:ℝ)+1)*(lam+(k:ℝ)+1)*a1+a0/4 =
      ((16:ℝ)*((k:ℝ)+1)*(lam+(k:ℝ)+1)*a1+a0)/4 := by ring
    _ = 0 := by rw [h]; ring

/-- Cross-multiplication avoids denominator side conditions. -/
theorem legendreJacobi_crossMultiplication (n : ℝ) :
    n*(n+2*(1/2:ℝ)-1)*(4*n^2-1) =
      n^2*((2*n+2*(1/2:ℝ)-2)*(2*n+2*(1/2:ℝ))) := by
  ring

theorem legendre_beta_1 :
    ((1:ℚ)^2)/(4*(4*(1:ℚ)^2-1)) = 1/12 := by norm_num

theorem legendre_beta_2 :
    ((2:ℚ)^2)/(4*(4*(2:ℚ)^2-1)) = 1/15 := by norm_num

theorem legendre_beta_3 :
    ((3:ℚ)^2)/(4*(4*(3:ℚ)^2-1)) = 9/140 := by norm_num

/-!
A sum-of-squares certificate for finite truncations of the kernel
exp(c*u*v), for c ≥ 0. No passage to the infinite sum is claimed.
-/
noncomputable def truncatedExponentialGram (m N : ℕ) (c : ℝ)
    (u a : Fin m → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    c^k * (∑ i : Fin m, a i * (u i)^k)^2 / (Nat.factorial k : ℝ)

theorem truncatedExponentialGram_nonneg
    (m N : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (u a : Fin m → ℝ) :
    0 ≤ truncatedExponentialGram m N c u a := by
  unfold truncatedExponentialGram
  apply Finset.sum_nonneg
  intro k hk
  have hck : 0 ≤ c^k := pow_nonneg hc k
  have hsq : 0 ≤ (∑ i : Fin m, a i * (u i)^k)^2 := sq_nonneg _
  exact div_nonneg (mul_nonneg hck hsq) (Nat.cast_nonneg _)

end GegenbauerFock
