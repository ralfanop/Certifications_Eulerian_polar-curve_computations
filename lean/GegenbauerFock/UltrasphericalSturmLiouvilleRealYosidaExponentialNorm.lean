import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaExponentialContinuity
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# V007 — quantitative Banach-algebra exponential norm bound

A direct formal estimate for the operator exponential on the actual
real weighted L², without any pre-existing semigroup or eigenbasis:
  ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖.

The proof works around the fact that continuous endomorphisms generally
have only ‖1‖ ≤ 1, not the NormOneClass required by norm_pow_le. It
separates the degree-zero coefficient from positive powers and applies
the majorized exponential series, with an explicit real hasSum proof.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- General quantitative bound for the exponential of any bounded
endomorphism of genuine weighted real L². -/
theorem sturmRealOperatorExponential_norm_le_exp_norm
    (lam : ℝ) (X : SturmH lam →L[ℝ] SturmH lam) :
    ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  letI : NormedAlgebra ℚ (SturmH lam →L[ℝ] SturmH lam) :=
    .restrictScalars ℚ ℝ _
  have he :
      HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • X ^ n)
        (NormedSpace.exp X) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hre :
      HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) * ‖X‖ ^ n)
        (Real.exp ‖X‖) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa only [smul_eq_mul] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (‖X‖ : ℝ))
  apply he.norm_le_of_bounded hre
  intro n
  have hcoeff : 0 ≤ ((n.factorial : ℝ)⁻¹) := by positivity
  have hp : ‖X ^ n‖ ≤ ‖X‖ ^ n := by
    cases n with
    | zero =>
        simpa only [pow_zero, ContinuousLinearMap.one_def, pow_zero] using
          (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := SturmH lam))
    | succ k =>
        exact norm_pow_le' X (Nat.succ_pos k)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff]
  exact mul_le_mul_of_nonneg_left hp hcoeff

#print axioms GegenbauerFock.Ultraspherical.sturmRealOperatorExponential_norm_le_exp_norm

end GegenbauerFock.Ultraspherical
