import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaGeneratorConvergence
import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventSelfAdjoint

/-!
# V007 — self-adjoint Yosida generators and contractive Euler steps

The true real weighted-L² closed ultraspherical Sturm operator has
a self-adjoint bounded positive resolvent R_t and the actual
Yosida generator A_t := t(tR_t-I).

This module proves that A_t itself is self-adjoint. It also
constructs the actual bounded Euler step I+h A_t and proves
‖(I+h A_t)f‖ ≤ ‖f‖ whenever 0≤h and h*t≤1, uniformly on L².

These are concrete semigroup-approximation building blocks; this
module does NOT itself construct a strongly continuous C₀ semigroup.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Each bounded Yosida generator of the actual closed Sturm
operator is self-adjoint on the entire weighted real Hilbert space. -/
theorem sturmRealYosidaGenerator_isSelfAdjoint
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    IsSelfAdjoint (sturmRealYosidaGenerator lam t hlam ht) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hR :=
    sturmRealPositiveResolventFullCLM_inner_symmetric lam t hlam ht f g
  rw [sturmRealYosidaGenerator_apply lam t hlam ht f,
      sturmRealYosidaGenerator_apply lam t hlam ht g]
  simp only [real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right]
  rw [hR]

/-- Bounded forward Euler approximation I+hA_t to the Yosida
semigroup, defined on ALL of the true weighted real L². -/
noncomputable def sturmRealYosidaEulerStep
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (h : ℝ) :
    SturmH lam →L[ℝ] SturmH lam :=
  ContinuousLinearMap.id ℝ (SturmH lam) +
    h • sturmRealYosidaGenerator lam t hlam ht

/-- Exact vector action of the bounded Yosida forward Euler step. -/
theorem sturmRealYosidaEulerStep_apply
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (h : ℝ)
    (f : SturmH lam) :
    sturmRealYosidaEulerStep lam t hlam ht h f =
      f + h • sturmRealYosidaGenerator lam t hlam ht f := by
  simp [sturmRealYosidaEulerStep]

/-- Every sufficiently small positive Euler step is a contraction
on the complete real weighted-L² space, for 0≤h≤1/t. -/
theorem sturmRealYosidaEulerStep_norm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (h : ℝ) (hh : 0 ≤ h) (hsmall : h * t ≤ 1)
    (f : SturmH lam) :
    ‖sturmRealYosidaEulerStep lam t hlam ht h f‖ ≤ ‖f‖ := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hc : ‖t • R f‖ ≤ ‖f‖ :=
    sturmRealYosidaContraction_norm_le lam t hlam ht f
  have ha : 0 ≤ h * t := mul_nonneg hh ht.le
  have hb : 0 ≤ 1 - h * t := sub_nonneg.mpr hsmall
  have hid :
      f + h • (t • (t • R f - f)) =
        (1 - h * t) • f + (h * t) • (t • R f) := by
    calc
      f + h • (t • (t • R f - f)) =
          f + (h * t) • (t • R f - f) := by rw [smul_smul]
      _ = (1 - h * t) • f + (h * t) • (t • R f) := by
        rw [smul_sub, sub_smul, one_smul]
        abel
  rw [sturmRealYosidaEulerStep_apply,
    sturmRealYosidaGenerator_apply]
  change ‖f + h • (t • (t • R f - f))‖ ≤ ‖f‖
  rw [hid]
  calc
    ‖(1 - h * t) • f + (h * t) • (t • R f)‖ ≤
        ‖(1 - h * t) • f‖ + ‖(h * t) • (t • R f)‖ :=
      norm_add_le _ _
    _ = (1 - h * t) * ‖f‖ + (h * t) * ‖t • R f‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hb, abs_of_nonneg ha]
    _ ≤ ‖f‖ := by
      have hmul := mul_nonneg ha (sub_nonneg.mpr hc)
      nlinarith

/-- Operator norm at most one for each stable bounded Euler step. -/
theorem sturmRealYosidaEulerStep_opNorm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (h : ℝ) (hh : 0 ≤ h) (hsmall : h * t ≤ 1) :
    ‖sturmRealYosidaEulerStep lam t hlam ht h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa only [one_mul] using
    sturmRealYosidaEulerStep_norm_le lam t hlam ht h hh hsmall f

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_isSelfAdjoint
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaEulerStep_apply
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaEulerStep_norm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaEulerStep_opNorm_le

end GegenbauerFock.Ultraspherical
