import GegenbauerFock.UltrasphericalSturmLiouvilleResolventQuadraticDecay
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates

/-!
# V007 — uniform high-frequency tail estimates for the genuine closed Sturm resolvent

The normalized Gegenbauer Hilbert basis diagonalizes the actual bounded
resolvent on every vector of the concrete real weighted L² space. These
three results promote pointwise O(n^-2) scalar decay to a uniform bound
over all modes n ≥ N, including all Fourier coordinates of an arbitrary
L² vector.

This is the quantitative spectral-tail input for finite-rank approximation.
No operator-norm convergence or compactness claim is made in this module.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- Every positive-degree spectral multiplier in the tail n ≥ N is
bounded by N⁻², uniformly over all such n. -/
theorem sturmResolventMultiplier_uniform_tail_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (N n : ℕ) (hN : 1 ≤ N) (hNn : N ≤ n) :
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ ≤
      ((N : ℝ) ^ 2)⁻¹ := by
  have hn : 1 ≤ n := le_trans hN hNn
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNnr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hNp : 0 < (N : ℝ) := by linarith
  have hnp : 0 < (n : ℝ) := by linarith
  have hsq : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hNnr)
      (add_nonneg (le_of_lt hnp) (le_of_lt hNp))]
  calc
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
        ≤ ((n : ℝ) ^ 2)⁻¹ :=
          sturmResolventMultiplier_le_inv_degree_sq lam t hlam ht n hn
    _ ≤ ((N : ℝ) ^ 2)⁻¹ := by
      have h := one_div_le_one_div_of_le (sq_pos_of_pos hNp) hsq
      simpa only [one_div] using h

/-- Uniform quadratic cutoff estimate for the actual resolvent
applied to each normalized Gegenbauer eigenmode. -/
theorem sturmRealPositiveResolvent_normalized_mode_uniform_tail
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (N n : ℕ) (hN : 1 ≤ N) (hNn : N ≤ n) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖ ≤
      ((N : ℝ) ^ 2)⁻¹ := by
  calc
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖
        ≤ ((n : ℝ) ^ 2)⁻¹ :=
          sturmRealPositiveResolvent_normalized_mode_quadratic_decay
            lam t hlam ht n (le_trans hN hNn)
    _ ≤ ((N : ℝ) ^ 2)⁻¹ := by
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hNnr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
      have hNp : 0 < (N : ℝ) := by linarith
      have hnp : 0 < (n : ℝ) := by linarith
      have hsq : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hNnr)
          (add_nonneg (le_of_lt hnp) (le_of_lt hNp))]
      have h := one_div_le_one_div_of_le (sq_pos_of_pos hNp) hsq
      simpa only [one_div] using h

/-- The cutoff controls every high-frequency Fourier coefficient of
the genuine closed resolvent applied to an arbitrary weighted-L² vector. -/
theorem sturmRealPositiveResolvent_full_coordinate_uniform_tail
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (N n : ℕ) (hN : 1 ≤ N) (hNn : N ≤ n)
    (f : Lp ℝ 2 (measure lam)) :
    |(sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
       (sturmRealPositiveResolventFullCLM lam t hlam ht f) n| ≤
    ((N : ℝ) ^ 2)⁻¹ *
      |(sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n| := by
  rw [sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal,
    abs_mul, abs_of_pos (sturmResolventMultiplier_pos lam t hlam ht n)]
  exact mul_le_mul_of_nonneg_right
    (sturmResolventMultiplier_uniform_tail_bound lam t hlam ht N n hN hNn)
    (abs_nonneg _)

#print axioms GegenbauerFock.Ultraspherical.sturmResolventMultiplier_uniform_tail_bound
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_normalized_mode_uniform_tail
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_full_coordinate_uniform_tail

end GegenbauerFock.Ultraspherical
