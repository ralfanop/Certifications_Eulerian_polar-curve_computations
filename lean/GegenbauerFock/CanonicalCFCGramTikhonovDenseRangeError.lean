import GegenbauerFock.CanonicalCFCGramTikhonovContraction
import GegenbauerFock.TwoSidedGramProperDenseRange
import GegenbauerFock.CanonicalCFCGramTikhonovErrorIdentity

/-!
# V007 — exact Tikhonov error identity on the dense source Gram image

With G=C* C and A_eps=G+eps I, B_eps=A_eps^{-1}, the actual
bounded error E_eps=eps B_eps obeys

  E_eps (G y) = eps (y - E_eps y).

Combining this with contractivity gives the useful quantitative
dense-image bound ‖E_eps(Gy)‖ ≤ 2 eps‖y‖ for every y.

This is not by itself full strong convergence on arbitrary f:
the final step uses density of ran G and a uniform estimate.
-/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev RangeH (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

/-- Exact regularization error identity on the genuine dense image
of the positive ultraspherical source Gram. -/
theorem sourceGramTikhonov_error_on_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) (y : RangeH lam) :
    (((eps : ℂ) •
        Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps))
      (gram lam alpha hlam ha y)) =
      (eps : ℂ) • (y -
        (((eps : ℂ) •
          Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) y)) := by
  let G := gram lam alpha hlam ha
  let A := sourceGramPositiveShift lam alpha hlam ha eps
  let B := Ring.inverse A
  have hinv : B * A = (1 : RangeH lam →L[ℂ] RangeH lam) :=
    (sourceGramPositiveShift_two_sided_inverse lam alpha hlam ha eps heps).2
  have hAG : A = G + (eps : ℂ) •
      (1 : RangeH lam →L[ℂ] RangeH lam) := rfl
  have hBG : B * G + (eps : ℂ) • B =
      (1 : RangeH lam →L[ℂ] RangeH lam) := by
    calc
      B * G + (eps : ℂ) • B =
          B * (G + (eps : ℂ) •
            (1 : RangeH lam →L[ℂ] RangeH lam)) := by
              rw [mul_add, mul_smul_comm, mul_one]
      _ = B * A := by rw [hAG]
      _ = 1 := hinv
  have hBG1 : B * G = (1 : RangeH lam →L[ℂ] RangeH lam) -
      (eps : ℂ) • B := eq_sub_iff_add_eq.mpr hBG
  have hE : ((eps : ℂ) • B) * G =
      (eps : ℂ) • ((1 : RangeH lam →L[ℂ] RangeH lam) -
        (eps : ℂ) • B) := by
    rw [smul_mul_assoc, hBG1]
  have hvec := congrArg (fun T : RangeH lam →L[ℂ] RangeH lam => T y) hE
  simpa [B, A, G, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def] using hvec

/-- O(eps) dense-image error bound, uniform on any fixed Gram datum
Gy, based on the exact true shifted inverse and contractivity. -/
theorem sourceGramTikhonov_error_on_range_norm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) (y : RangeH lam) :
    ‖(((eps : ℂ) •
        Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps))
      (gram lam alpha hlam ha y))‖ ≤ 2 * eps * ‖y‖ := by
  let E : RangeH lam →L[ℂ] RangeH lam :=
    (eps : ℂ) •
      Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)
  have heq := sourceGramTikhonov_error_on_range
    lam alpha hlam ha eps heps y
  have hnorm := sourceGramTikhonov_error_pointwise_contract
    lam alpha hlam ha eps heps y
  have htri : ‖y - E y‖ ≤ ‖y‖ + ‖E y‖ := norm_sub_le _ _
  have hnorm' : ‖E y‖ ≤ ‖y‖ := hnorm
  have hsub : ‖y - E y‖ ≤ 2 * ‖y‖ := by linarith
  calc
    ‖E (gram lam alpha hlam ha y)‖ =
        ‖(eps : ℂ) • (y - E y)‖ := by exact congrArg norm heq
    _ = eps * ‖y - E y‖ := by
        simp [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps]
    _ ≤ eps * (2 * ‖y‖) :=
        mul_le_mul_of_nonneg_left hsub heps.le
    _ = 2 * eps * ‖y‖ := by ring

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonov_error_on_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonov_error_on_range_norm

end GegenbauerFock.GeneralUltrasphericalFock
