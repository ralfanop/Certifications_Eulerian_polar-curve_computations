import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventNorm

/-!
# Sharp norm of the closed Gegenbauer Sturm resolvent

The canonical all-L² resolvent of the ultraspherical Sturm operator
has norm exactly 1/t for every positive shift t. The upper bound
comes from its dissipative closed-graph estimate; the degree-zero
normalized Gegenbauer eigenmode attains that bound. This is a claim
about the actual weighted real L² operator, without any spectral
extension or completeness hypothesis.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The degree-zero normalized Gegenbauer mode is an exact eigenvector
of the genuine closed Sturm resolvent, with multiplier t⁻¹. -/
theorem sturmRealPositiveResolventFullCLM_zero_mode
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmMonicEigenCandidate_realL2_normalized lam hlam 0) =
      t⁻¹ • sturmMonicEigenCandidate_realL2_normalized lam hlam 0 := by
  simpa using
    sturmMonicRealHilbertBasis_full_resolvent_eigen lam t hlam ht 0

/-- The positive-shift resolvent has EXACT operator norm 1/t.
The constant Gegenbauer mode is a unit-norm extremizer. -/
theorem sturmRealPositiveResolventFullCLM_opNorm_eq
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht‖ = t⁻¹ := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let u := sturmMonicEigenCandidate_realL2_normalized lam hlam 0
  have hu : ‖u‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 0
  have heig : R u = t⁻¹ • u :=
    sturmRealPositiveResolventFullCLM_zero_mode lam t hlam ht
  have hle : ‖R‖ ≤ t⁻¹ :=
    sturmRealPositiveResolventFullCLM_opNorm_le lam t hlam ht
  have hge : t⁻¹ ≤ ‖R‖ := by
    have h := ContinuousLinearMap.le_opNorm R u
    rw [heig, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr ht.le), mul_one] at h
    exact h
  exact le_antisymm hle hge

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_zero_mode
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_opNorm_eq

end GegenbauerFock.Ultraspherical
