import GegenbauerFock.CanonicalCFCGramPositiveShiftCoercivity
import GegenbauerFock.CanonicalCFCGramTikhonovShift

/-!
# V007 — uniform contraction of the genuine Tikhonov error filter

Combining the strictly positive Gram shift coercivity estimate
eps*‖x‖ ≤ ‖(G+eps I)x‖ with genuine two-sided bounded inverse
produces the sharp uniform estimate
‖eps (G+eps I)⁻¹‖ ≤ 1
on the complete weighted L² Hilbert source.
-/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev ContractH (lam : ℝ) := Lp ℂ 2 (Ultraspherical.measure lam)

/-- Actual Tikhonov residual filter is pointwise contractive, for every
strictly positive regularization parameter. -/
theorem sourceGramTikhonov_error_pointwise_contract
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (x : ContractH lam) :
    ‖((eps : ℂ) •
      (Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps))) x‖ ≤
      ‖x‖ := by
  let A := sourceGramPositiveShift lam alpha hlam ha eps
  let y : ContractH lam := (Ring.inverse A) x
  have hAy : A y = x := by
    have h := (sourceGramPositiveShift_two_sided_inverse
      lam alpha hlam ha eps heps).1
    have hx := congrArg (fun T : ContractH lam →L[ℂ] ContractH lam => T x) h
    change A ((Ring.inverse A) x) = x at hx
    exact hx
  have hco := sourceGram_positive_shift_norm_lower
    lam alpha hlam ha eps heps y
  have heval :
      gram lam alpha hlam ha y + (eps : ℂ) • y = A y := by
    simp [A, sourceGramPositiveShift, ContinuousLinearMap.add_apply]
  change ‖(eps : ℂ) • y‖ ≤ ‖x‖
  calc
    ‖(eps : ℂ) • y‖ ≤ ‖(eps : ℂ)‖ * ‖y‖ := norm_smul_le _ _
    _ = eps * ‖y‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps]
    _ ≤ ‖gram lam alpha hlam ha y + (eps : ℂ) • y‖ := hco
    _ = ‖A y‖ := by rw [heval]
    _ = ‖x‖ := by rw [hAy]

/-- Uniform operator-norm contraction of the true Tikhonov error. -/
theorem sourceGramTikhonov_error_opNorm_le_one
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) :
    ‖(eps : ℂ) •
      (Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [one_mul] using
    sourceGramTikhonov_error_pointwise_contract
      lam alpha hlam ha eps heps x

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonov_error_pointwise_contract
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonov_error_opNorm_le_one

end GegenbauerFock.GeneralUltrasphericalFock
