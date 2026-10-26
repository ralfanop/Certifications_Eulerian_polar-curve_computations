import GegenbauerFock.WeightedMoments

/-!
# V007 — justified exchange of the factorial Fock sum and ultraspherical integral

For any probability measure supported on [-1,1] and every α>0,
the positive factorial-weighted monomial energy functions are
Bochner integrable and the series of their L¹ norms is summable.
Therefore Mathlib's dominated-convergence theorem for series
justifies exchanging the infinite sum and integral.

This is a real analytic theorem, not a purely formal rearrangement.
The identification of the pointwise power series with Real.exp and
the concrete Hilbert–Schmidt norm remains separate.
-/

open MeasureTheory

namespace GegenbauerFock.MomentSeriesIntegral

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))
variable (alpha : ℝ) (ha : 0 < alpha)

noncomputable def term (n : ℕ) (u : ℝ) : ℝ :=
  WeightedMoments.squareWeight alpha n * ‖(u : ℂ) ^ n‖ ^ 2

theorem term_norm_le (n : ℕ) (u : ℝ) (hu : |u| ≤ 1) :
    ‖term alpha n u‖ ≤ WeightedMoments.squareWeight alpha n := by
  have hw := WeightedMoments.squareWeight_nonneg alpha ha n
  have hnorm : ‖(u : ℂ) ^ n‖ ^ 2 ≤ 1 := by
    calc
      ‖(u : ℂ) ^ n‖ ^ 2 = (|u| ^ n) ^ 2 := by simp
      _ ≤ (1 ^ n : ℝ) ^ 2 := by gcongr
      _ = 1 := by simp
  have hterm : 0 ≤ WeightedMoments.squareWeight alpha n *
      ‖(u : ℂ) ^ n‖ ^ 2 :=
    mul_nonneg hw (sq_nonneg _)
  simpa only [term, Real.norm_eq_abs, abs_of_nonneg hterm,
    mul_one] using mul_le_mul_of_nonneg_left hnorm hw

include hsupport

theorem term_integrable (n : ℕ) : Integrable (term alpha n) μ := by
  have hmeas : AEStronglyMeasurable (term alpha n) μ := by
    apply Continuous.aestronglyMeasurable
    unfold term
    fun_prop
  apply Integrable.of_bound hmeas (WeightedMoments.squareWeight alpha n)
  filter_upwards [hsupport] with u hu
  exact term_norm_le alpha ha n u hu

theorem integral_norm_le_weight (n : ℕ) :
    (∫ u : ℝ, ‖term alpha n u‖ ∂μ) ≤
      WeightedMoments.squareWeight alpha n := by
  have hae : ∀ᵐ u ∂μ, ‖term alpha n u‖ ≤
      WeightedMoments.squareWeight alpha n := by
    filter_upwards [hsupport] with u hu
    exact term_norm_le alpha ha n u hu
  have h := integral_mono_ae
    (term_integrable μ hsupport alpha ha n).norm
    (integrable_const (WeightedMoments.squareWeight alpha n))
    hae
  simpa using h

theorem summable_integrals_norm :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖term alpha n u‖ ∂μ) := by
  apply Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun u => norm_nonneg _)
    (integral_norm_le_weight μ hsupport alpha ha)
    (WeightedMoments.squareWeight_summable alpha)

theorem integral_tsum_energy :
    (∫ u : ℝ, ∑' n : ℕ, term alpha n u ∂μ) =
      ∑' n : ℕ, ∫ u : ℝ, term alpha n u ∂μ := by
  exact (integral_tsum_of_summable_integral_norm
    (term_integrable μ hsupport alpha ha)
    (summable_integrals_norm μ hsupport alpha ha)).symm

#print axioms GegenbauerFock.MomentSeriesIntegral.term_integrable
#print axioms GegenbauerFock.MomentSeriesIntegral.summable_integrals_norm
#print axioms GegenbauerFock.MomentSeriesIntegral.integral_tsum_energy

end GegenbauerFock.MomentSeriesIntegral
