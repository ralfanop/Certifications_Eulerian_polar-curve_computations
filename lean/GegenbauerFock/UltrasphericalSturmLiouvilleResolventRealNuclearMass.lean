import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealPositiveNuclear
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventSquareSeriesSummable

/-!
# V007 — exact mass of the actual real-Hilbert positive nuclear series

The nuclear decomposition is of the actual canonical closed Sturm
resolvent in the bounded-operator norm. Here its rank-one mass is
calculated by the exact sum of the norms of the operator-valued
summands. This is a *specific positive nuclear witness* with a
certified exact mass; no unproved universal CFC trace norm over
arbitrary real operators is identified implicitly.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace

/-- The nuclear mass of the explicit positive Gegenbauer rank-one
operator decomposition equals the scalar spectral trace. -/
theorem sturmRealResolvent_positive_nuclear_mass_eq_trace
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (∑' n : ℕ,
      ‖(t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖) =
      sturmResolventSpectralTrace lam t := by
  unfold sturmResolventSpectralTrace
  apply tsum_congr
  intro n
  rw [norm_smul, norm_rankOne,
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n]
  simp only [one_mul, mul_one, Real.norm_eq_abs,
    abs_of_pos (sturmResolventMultiplier_pos lam t hlam ht n)]

/-- The squared norms of the same genuine rank-one operator
summands sum to the already certified squared spectral trace. -/
theorem sturmRealResolvent_positive_nuclear_square_mass_eq
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (∑' n : ℕ,
      ‖(t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖ ^ 2) =
      sturmResolventSquaredSpectralTrace lam t := by
  unfold sturmResolventSquaredSpectralTrace
  apply tsum_congr
  intro n
  rw [norm_smul, norm_rankOne,
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n]
  simp only [one_mul, mul_one, Real.norm_eq_abs,
    abs_of_pos (sturmResolventMultiplier_pos lam t hlam ht n)]

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_positive_nuclear_mass_eq_trace
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_positive_nuclear_square_mass_eq

end GegenbauerFock.Ultraspherical
