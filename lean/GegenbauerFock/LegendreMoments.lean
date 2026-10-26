import Mathlib

/-!
# Legendre probability moments: exact interval integrals

For λ=1/2, the normalized Gegenbauer measure is the uniform probability
distribution du/2 on [-1,1]. We certify its normalization and every even
and odd moment using *actual Mathlib interval integrals*.

This is not yet the weighted general-λ beta-integral or the construction
of a Bochner-valued Fock transform.
-/

open intervalIntegral

namespace GegenbauerFock.Legendre

/-- The uniform probability moment on [-1,1]. -/
noncomputable def uniformMoment (n : ℕ) : ℝ :=
  (1/2 : ℝ) * (∫ u in (-1 : ℝ)..(1 : ℝ), u ^ n)

/-- Exact closed form before separating even and odd exponents. -/
theorem uniformMoment_eq (n : ℕ) :
    uniformMoment n =
      (1/2 : ℝ) *
      ((1 : ℝ) ^ (n+1) - (-1 : ℝ) ^ (n+1)) / ((n : ℝ)+1) := by
  unfold uniformMoment
  rw [integral_pow]
  ring

/-- The normalized Legendre weight has mass one. -/
theorem uniformMoment_zero : uniformMoment 0 = 1 := by
  rw [uniformMoment_eq]
  norm_num

/-- All odd moments of the symmetric Legendre probability law vanish. -/
theorem uniformMoment_odd (n : ℕ) :
    uniformMoment (2*n+1) = 0 := by
  rw [uniformMoment_eq]
  have hpow : (-1 : ℝ) ^ ((2*n+1)+1) = 1 := by
    simp [pow_add, pow_mul]
  rw [hpow]
  norm_num

/-- The degree 2n moment is 1/(2n+1). -/
theorem uniformMoment_even (n : ℕ) :
    uniformMoment (2*n) = 1 / (((2*n : ℕ) : ℝ)+1) := by
  rw [uniformMoment_eq]
  have hpow : (-1 : ℝ) ^ ((2*n)+1) = -1 := by
    simp [pow_add, pow_mul]
  rw [hpow]
  norm_num

#print axioms GegenbauerFock.Legendre.uniformMoment_eq
#print axioms GegenbauerFock.Legendre.uniformMoment_zero
#print axioms GegenbauerFock.Legendre.uniformMoment_odd
#print axioms GegenbauerFock.Legendre.uniformMoment_even

end GegenbauerFock.Legendre
