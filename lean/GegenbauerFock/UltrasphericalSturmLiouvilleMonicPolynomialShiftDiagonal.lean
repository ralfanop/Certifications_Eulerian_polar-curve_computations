import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenPolynomial
import GegenbauerFock.UltrasphericalSturmLiouvillePositiveShiftSurjective

/-!
# V007 — explicit shifted Gegenbauer action and polynomial resolvent preimages

The genuinely constructed finite monic Gegenbauer eigenpolynomials satisfy
the exact positive-shift equation (tI-L) G_n = (t+n(n+2λ)) G_n.
The positive denominator permits a fully explicit *finite polynomial*
preimage of G_n at every t>0. No L² basis completeness or resolvent
surjectivity on the full Hilbert space is assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- The actual polynomial positive shift acts diagonally on the
explicit finite monic Gegenbauer eigenpolynomial of arbitrary degree. -/
theorem sturmMonicEigenCandidate_shift_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (n : ℕ) :
    sturmPositiveShiftPolynomial lam t (sturmMonicEigenCandidate lam n) =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam)) •
        sturmMonicEigenCandidate lam n := by
  calc
    sturmPositiveShiftPolynomial lam t (sturmMonicEigenCandidate lam n) =
      C t * sturmMonicEigenCandidate lam n -
        C (sturmEigenvalue lam n) *
          sturmMonicEigenCandidate lam n := by
            simp only [sturmPositiveShiftPolynomial,
              sturmMonicEigenCandidate_eigen lam hlam n, smul_eq_C_mul]
    _ = C (t - sturmEigenvalue lam n) *
          sturmMonicEigenCandidate lam n := by
            rw [map_sub, sub_mul]
    _ = (t + (n : ℝ) * ((n : ℝ) + 2 * lam)) •
          sturmMonicEigenCandidate lam n := by
            have hcoeff : t - sturmEigenvalue lam n =
                t + (n : ℝ) * ((n : ℝ) + 2 * lam) := by
              unfold sturmEigenvalue
              ring
            rw [hcoeff]
            simp only [smul_eq_C_mul]

/-- Explicit finite polynomial solution of (tI-L)q=G_n for
every real t>0, λ>0 and nonnegative integer degree n. -/
theorem sturmMonicEigenCandidate_shift_exact_preimage
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    sturmPositiveShiftPolynomial lam t
        ((t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
          sturmMonicEigenCandidate lam n) =
      sturmMonicEigenCandidate lam n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hterm : 0 ≤ (n : ℝ) + 2 * lam := by positivity
  have hden : t + (n : ℝ) * ((n : ℝ) + 2 * lam) ≠ 0 :=
    ne_of_gt (by have hp := mul_nonneg hn hterm; linarith)
  rw [sturmPositiveShiftPolynomial_smul,
    sturmMonicEigenCandidate_shift_diagonal lam t hlam n,
    smul_smul, inv_mul_cancel₀ hden, one_smul]

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_shift_diagonal
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_shift_exact_preimage

end GegenbauerFock.Ultraspherical
