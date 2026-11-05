import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2BasisResolvent
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierDecay

/-!
# V007 — quadratic decay of the genuine closed Gegenbauer resolvent

The actual positive-shift Sturm resolvent is already kernel-certified
to diagonalize in an explicitly constructed, complete normalized
Gegenbauer Hilbert basis of real weighted L². This module strengthens
scalar convergence of the eigenvalues to zero to the quantitative
bound beta_n ≤ 1/n² for every positive mode n.

This is an analytic input for subsequent finite-rank approximations
of the genuine closed Sturm resolvent; it does not itself assert
compactness from scalar decay alone.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The nth nonconstant eigenvalue of the genuine positive Sturm
resolvent decays at least quadratically in n, uniformly in
the positive Gegenbauer parameter lambda and positive shift t. -/
theorem sturmResolventMultiplier_le_inv_degree_sq
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (n : ℕ) (hn : 1 ≤ n) :
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ ≤
      ((n : ℝ) ^ 2)⁻¹ := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hquad : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  have hden :
      (n : ℝ) ^ 2 ≤
        t + (n : ℝ) * ((n : ℝ) + 2 * lam) := by
    nlinarith [mul_pos hnpos hlam]
  have h := one_div_le_one_div_of_le hquad hden
  simpa only [one_div] using h

/-- The genuine weighted-L² resolvent on the nth normalized,
complete Gegenbauer basis eigenvector has norm at most 1/n²
for every n≥1. -/
theorem sturmRealPositiveResolvent_normalized_mode_quadratic_decay
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖ ≤
      ((n : ℝ) ^ 2)⁻¹ := by
  have heig := sturmMonicEigenCandidate_realL2_normalized_resolvent_diagonal
    lam t hlam ht n
  have hnorm :
      ‖sturmMonicEigenCandidate_realL2_normalized lam hlam n‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n
  have hpos := sturmResolventMultiplier_pos lam t hlam ht n
  rw [heig, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_pos hpos]
  exact sturmResolventMultiplier_le_inv_degree_sq lam t hlam ht n hn

#print axioms GegenbauerFock.Ultraspherical.sturmResolventMultiplier_le_inv_degree_sq
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_normalized_mode_quadratic_decay

end GegenbauerFock.Ultraspherical
