import Mathlib

/-!
# V007: bounded infinite Fock-coordinate analysis map from summable coefficients

This is a genuine bounded operator between a complex normed space and
the infinite-dimensional Hilbert space ℓ²(ℕ;ℂ), conditional on the
mathematically meaningful hypothesis that the squared norms of all its
coefficient functionals are summable. The summability of the *specific*
Gegenbauer-Fock exponential coefficient family is a separate obligation.

This file does not assert the holomorphic evaluation formula or the
Gaussian weighted Fock isometry, and does not alone certify compactness
or a Hilbert-Schmidt operator norm.
-/

open scoped ENNReal

namespace GegenbauerFock.InfiniteAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev FockCoefficients : Type := lp (fun _ : ℕ => ℂ) 2

/-- Assumption: sum of squared operator norms is finite. -/
def SquareSummable (k : ℕ → E →L[ℂ] ℂ) : Prop :=
  Summable (fun n => ‖k n‖ ^ 2)

private theorem section_sq_bound (k : ℕ → E →L[ℂ] ℂ)
    (f : E) (n : ℕ) :
    ‖k n f‖ ^ 2 ≤ ‖k n‖ ^ 2 * ‖f‖ ^ 2 := by
  calc
    ‖k n f‖ ^ 2 ≤ (‖k n‖ * ‖f‖) ^ 2 := by
      gcongr
      exact (k n).le_opNorm f
    _ = ‖k n‖ ^ 2 * ‖f‖ ^ 2 := mul_pow _ _ _

private theorem section_sq_summable (k : ℕ → E →L[ℂ] ℂ)
    (hk : SquareSummable k) (f : E) :
    Summable (fun n => ‖k n f‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) (section_sq_bound k f)
  exact hk.mul_right (‖f‖ ^ 2)

/-- Real ℓ² membership for the full infinite coefficient sequence. -/
theorem coefficients_memℓp (k : ℕ → E →L[ℂ] ℂ)
    (hk : SquareSummable k) (f : E) :
    Memℓp (fun n : ℕ => k n f) 2 := by
  apply memℓp_gen
  simpa using section_sq_summable k hk f

/-- Genuine infinite Fock-coordinate output, not a finite truncation. -/
noncomputable def evaluate (k : ℕ → E →L[ℂ] ℂ)
    (hk : SquareSummable k) (f : E) : FockCoefficients :=
  ⟨fun n => k n f, coefficients_memℓp k hk f⟩

/-- Exact coordinate formula for the infinite coefficient family. -/
theorem evaluate_apply (k : ℕ → E →L[ℂ] ℂ)
    (hk : SquareSummable k) (f : E) (n : ℕ) :
    evaluate k hk f n = k n f := rfl

/-- Infinite Fock-coordinate analysis as a complex-linear map. -/
noncomputable def linear (k : ℕ → E →L[ℂ] ℂ)
    (hk : SquareSummable k) : E →ₗ[ℂ] FockCoefficients where
  toFun := evaluate k hk
  map_add' := by
    intro x y
    ext n
    simp [evaluate_apply]
  map_smul' := by
    intro c x
    ext n
    simp [evaluate_apply]

/-- Quantitative bound for the actual infinite ℓ² output. -/
theorem norm_sq_le (k : ℕ → E →L[ℂ] ℂ)
    (hk : SquareSummable k) (f : E) :
    ‖linear k hk f‖ ^ 2 ≤
      (∑' n, ‖k n‖ ^ 2) * ‖f‖ ^ 2 := by
  have hsum :
      (∑' n, ‖k n f‖ ^ 2) ≤
        (∑' n, ‖k n‖ ^ 2 * ‖f‖ ^ 2) := by
    exact (section_sq_summable k hk f).tsum_le_tsum
      (section_sq_bound k f) (hk.mul_right (‖f‖ ^ 2))
  have hnorm : ‖linear k hk f‖ ^ 2 =
      (∑' n, ‖k n f‖ ^ 2) := by
    convert lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (linear k hk f) using 1 <;> norm_num
  rw [hnorm]
  simpa only [tsum_mul_right] using hsum

/-- The infinite analysis map is bounded, with an explicit universal
operator norm upper bound supplied by the ℓ² coefficient energies. -/
noncomputable def bounded (k : ℕ → E →L[ℂ] ℂ)
    (hk : SquareSummable k) : E →L[ℂ] FockCoefficients :=
  (linear k hk).mkContinuous
    (Real.sqrt (∑' n, ‖k n‖ ^ 2)) (by
      intro f
      have hpos : 0 ≤ ∑' n, ‖k n‖ ^ 2 :=
        tsum_nonneg (fun n => sq_nonneg _)
      have hsq := norm_sq_le k hk f
      have hsqrt := Real.sq_sqrt hpos
      have hzero : 0 ≤ Real.sqrt (∑' n, ‖k n‖ ^ 2) * ‖f‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      nlinarith [norm_nonneg (linear k hk f)])

theorem bounded_apply (k : ℕ → E →L[ℂ] ℂ)
    (hk : SquareSummable k) (f : E) (n : ℕ) :
    bounded k hk f n = k n f := by
  rfl

#print axioms GegenbauerFock.InfiniteAnalysis.coefficients_memℓp
#print axioms GegenbauerFock.InfiniteAnalysis.norm_sq_le
#print axioms GegenbauerFock.InfiniteAnalysis.bounded_apply

end GegenbauerFock.InfiniteAnalysis
