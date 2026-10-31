import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertSharpResolventNorm
import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventIdentity

/-!
# Sharp quantitative stability of the Gegenbauer Sturm resolvent under shift

The exact positive-shift resolvents of the closed weighted Sturm operator
obey the second resolvent identity. Their sharp operator norms and the
unit constant Gegenbauer eigenvector establish the exact two-shift
operator-norm distance:

    ‖(tI-A)⁻¹ - (sI-A)⁻¹‖ = |1/t - 1/s|

for all t,s>0 and every ultraspherical parameter λ>0. The bound
is attained on the degree-zero normalized Gegenbauer mode.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Resolvent shifts are sharply Lipschitz in the inverse shift
parameter; equality holds on the unit degree-zero Gegenbauer mode. -/
theorem sturmRealPositiveResolventFullCLM_difference_opNorm_eq
    (lam t s : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hs : 0 < s) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht -
      sturmRealPositiveResolventFullCLM lam s hlam hs‖ =
      |t⁻¹ - s⁻¹| := by
  let Rt := sturmRealPositiveResolventFullCLM lam t hlam ht
  let Rs := sturmRealPositiveResolventFullCLM lam s hlam hs
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 0
  have hu : ‖u‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 0
  have hident : Rt - Rs = (s - t) • (Rt.comp Rs) := by
    ext f
    change Rt f - Rs f = (s - t) • Rt (Rs f)
    exact sturmRealPositiveResolventFullCLM_difference
      lam t s hlam ht hs f
  have hupper : ‖Rt - Rs‖ ≤ |s - t| * (t⁻¹ * s⁻¹) := by
    rw [hident, norm_smul, Real.norm_eq_abs]
    calc
      |s - t| * ‖Rt.comp Rs‖ ≤
          |s - t| * (‖Rt‖ * ‖Rs‖) := by
        exact mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le Rt Rs) (abs_nonneg _)
      _ = |s - t| * (t⁻¹ * s⁻¹) := by
        rw [show ‖Rt‖ = t⁻¹ from
          sturmRealPositiveResolventFullCLM_opNorm_eq lam t hlam ht,
          show ‖Rs‖ = s⁻¹ from
          sturmRealPositiveResolventFullCLM_opNorm_eq lam s hlam hs]
  have hformula : |s - t| * (t⁻¹ * s⁻¹) = |t⁻¹ - s⁻¹| := by
    have hneqt : t ≠ 0 := ne_of_gt ht
    have hneqs : s ≠ 0 := ne_of_gt hs
    have hfield : t⁻¹ - s⁻¹ = (s - t) * (t⁻¹ * s⁻¹) := by
      field_simp
      ring
    rw [hfield, abs_mul,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ht.le)
        (inv_nonneg.mpr hs.le))]
  have heig : (Rt - Rs) u = (t⁻¹ - s⁻¹) • u := by
    change Rt u - Rs u = (t⁻¹ - s⁻¹) • u
    rw [sturmRealPositiveResolventFullCLM_zero_mode lam t hlam ht,
      sturmRealPositiveResolventFullCLM_zero_mode lam s hlam hs, sub_smul]
  have hlower : |t⁻¹ - s⁻¹| ≤ ‖Rt - Rs‖ := by
    have h := ContinuousLinearMap.le_opNorm (Rt - Rs) u
    rw [heig, norm_smul, Real.norm_eq_abs, hu, mul_one, mul_one] at h
    exact h
  exact le_antisymm (hupper.trans_eq hformula) hlower

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_difference_opNorm_eq

end GegenbauerFock.Ultraspherical
