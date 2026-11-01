import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierDecay

/-!
# V007 — genuine normalized approximate null modes of closed Sturm resolvent

The actual weighted-real-L² closed Sturm positive resolvent has unit
Gegenbauer eigenmodes with output norms tending to zero. Thus zero
is approached by its nonzero point eigenvalues in infinite dimension.
Together with the independent no-zero-eigenvalue theorem, this
identifies the concrete source of unstable inversion.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Filter

/-- The norm of the genuine closed Sturm resolvent on each normalized
Gegenbauer mode equals its strictly positive scalar spectral multiplier. -/
theorem sturmRealPositiveResolventFullCLM_normalized_mode_norm_eq
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖ =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ := by
  rw [sturmMonicRealHilbertBasis_full_resolvent_eigen
      lam t hlam ht n, norm_smul,
    sturmMonicEigenCandidate_realL2_normalized_norm
      lam hlam n, mul_one, Real.norm_eq_abs,
    abs_of_pos (sturmResolventMultiplier_pos lam t hlam ht n)]

/-- Unit Gegenbauer eigenvectors of the actual full-L² Sturm resolvent
form an approximate null sequence: their image norms converge to zero
as the degree tends to infinity. No finite truncation is assumed. -/
theorem sturmRealPositiveResolventFullCLM_normalized_mode_norm_tendsto_zero
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Tendsto (fun n : ℕ =>
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖)
      atTop (nhds 0) := by
  have hfun :
      (fun n : ℕ =>
        ‖sturmRealPositiveResolventFullCLM lam t hlam ht
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖) =
        (fun n : ℕ =>
          (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹) := by
    funext n
    exact sturmRealPositiveResolventFullCLM_normalized_mode_norm_eq
      lam t hlam ht n
  rw [hfun]
  exact sturmResolventMultiplier_tendsto_zero lam t hlam ht

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_normalized_mode_norm_eq
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_normalized_mode_norm_tendsto_zero

end GegenbauerFock.Ultraspherical
