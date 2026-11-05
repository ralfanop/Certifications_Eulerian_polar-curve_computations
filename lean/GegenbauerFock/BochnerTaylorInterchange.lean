import GegenbauerFock.BochnerStage

/-!
# V007 — absolutely summable complex Eulerian Taylor kernels

The original Eulerian section exp(i*z*u/2) is integrated against
an arbitrary complex L¹ input on any measure concentrated on [-1,1].
We prove term integrability, the summable bound on integral norms,
and Bochner sum/integral interchange for every complex z.

This module does not conflate pointwise complex series with the
a priori separate Fock coefficient normalisation.
-/

open MeasureTheory

namespace GegenbauerFock.BochnerTaylor

/-- The actual complex Taylor integrand of the Eulerian Fourier section. -/
noncomputable def term (z : ℂ) (f : ℝ → ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  f u * ((Complex.I * z * (u : ℂ) / 2) ^ n / (Nat.factorial n : ℂ))

/-- A nonnegative, absolutely summable bound on Taylor coefficients. -/
noncomputable def bound (z : ℂ) (n : ℕ) : ℝ :=
  (‖z‖ / 2) ^ n / (Nat.factorial n : ℝ)

theorem bound_nonneg (z : ℂ) (n : ℕ) : 0 ≤ bound z n := by
  unfold bound
  positivity

theorem bound_summable (z : ℂ) : Summable (bound z) := by
  exact Real.summable_pow_div_factorial (‖z‖ / 2)

/-- Uniform coefficient bound on the actual ultraspherical support. -/
theorem norm_term_le (z : ℂ) (f : ℝ → ℂ) (n : ℕ)
    (u : ℝ) (hu : |u| ≤ 1) :
    ‖term z f n u‖ ≤ bound z n * ‖f u‖ := by
  have hnormu : ‖(u : ℂ)‖ ≤ 1 := by simpa using hu
  have harg : ‖Complex.I * z * (u : ℂ) / 2‖ ≤ ‖z‖ / 2 := by
    calc
      ‖Complex.I * z * (u : ℂ) / 2‖ =
          ‖z‖ * ‖(u : ℂ)‖ / 2 := by
            simp [norm_mul, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ ‖z‖ * 1 / 2 := by gcongr
      _ = ‖z‖ / 2 := by ring
  have hpow :
      ‖(Complex.I * z * (u : ℂ) / 2) ^ n /
        (Nat.factorial n : ℂ)‖ ≤ bound z n := by
    unfold bound
    rw [norm_div, norm_pow, norm_natCast]
    gcongr
  unfold term
  rw [norm_mul]
  calc
    ‖f u‖ * ‖(Complex.I * z * (u : ℂ) / 2) ^ n /
        (Nat.factorial n : ℂ)‖ ≤ ‖f u‖ * bound z n :=
      mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = bound z n * ‖f u‖ := by ring

/-- Each complex Taylor term really belongs to Bochner L¹. -/
theorem term_integrable (μ : Measure ℝ)
    (hsupport : ∀ᵐ u ∂μ, |u| ≤ 1)
    (z : ℂ) (f : ℝ → ℂ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (term z f n) μ := by
  have hcont : Continuous (fun u : ℝ =>
      (Complex.I * z * (u : ℂ) / 2) ^ n / (Nat.factorial n : ℂ)) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (term z f n) μ := by
    unfold term
    exact hf.aestronglyMeasurable.mul hcont.aestronglyMeasurable
  apply Integrable.mono'
    ((hf.norm).const_mul (bound z n)) hmeas
  filter_upwards [hsupport] with u hu
  exact norm_term_le z f n u hu

/-- The L¹ norm of each Taylor term is bounded by a factorial
coefficient times the L¹ norm of the original input. -/
theorem integral_norm_le (μ : Measure ℝ)
    (hsupport : ∀ᵐ u ∂μ, |u| ≤ 1)
    (z : ℂ) (f : ℝ → ℂ) (hf : Integrable f μ) (n : ℕ) :
    (∫ u : ℝ, ‖term z f n u‖ ∂μ) ≤
      bound z n * (∫ u : ℝ, ‖f u‖ ∂μ) := by
  have hdom : ∀ᵐ u ∂μ,
      ‖term z f n u‖ ≤ bound z n * ‖f u‖ := by
    filter_upwards [hsupport] with u hu
    exact norm_term_le z f n u hu
  have h := integral_mono_ae
    (term_integrable μ hsupport z f hf n).norm
    ((hf.norm).const_mul (bound z n)) hdom
  simpa only [integral_const_mul] using h

/-- Absolutely summable integrals: the precise condition needed for
unconditional Bochner sum/integral interchange. -/
theorem summable_integrals_norm (μ : Measure ℝ)
    (hsupport : ∀ᵐ u ∂μ, |u| ≤ 1)
    (z : ℂ) (f : ℝ → ℂ) (hf : Integrable f μ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖term z f n u‖ ∂μ) := by
  apply Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun u => norm_nonneg _)
    (integral_norm_le μ hsupport z f hf)
    ((bound_summable z).mul_right (∫ u : ℝ, ‖f u‖ ∂μ))

/-- The norm-summable complex Bochner series may be integrated
term by term without a tacit Fubini assumption. -/
theorem integral_tsum (μ : Measure ℝ)
    (hsupport : ∀ᵐ u ∂μ, |u| ≤ 1)
    (z : ℂ) (f : ℝ → ℂ) (hf : Integrable f μ) :
    (∫ u : ℝ, ∑' n : ℕ, term z f n u ∂μ) =
      ∑' n : ℕ, ∫ u : ℝ, term z f n u ∂μ := by
  exact (integral_tsum_of_summable_integral_norm
    (term_integrable μ hsupport z f hf)
    (summable_integrals_norm μ hsupport z f hf)).symm

/-- Pointwise, the absolutely convergent Taylor series reconstructs
the original Eulerian complex exponential. -/
theorem tsum_term (z : ℂ) (f : ℝ → ℂ) (u : ℝ) :
    (∑' n : ℕ, term z f n u) =
      f u * Complex.exp (Complex.I * z * (u : ℂ) / 2) := by
  unfold term
  rw [tsum_mul_left]
  rw [← BochnerStage.kernel_eq_tsum]
  rfl

/-- Main scalar bridge: an actual L¹ Fourier integral equals the sum
of its monomial Bochner integrals for every complex frequency. -/
theorem integral_exp_eq_tsum (μ : Measure ℝ)
    (hsupport : ∀ᵐ u ∂μ, |u| ≤ 1)
    (z : ℂ) (f : ℝ → ℂ) (hf : Integrable f μ) :
    (∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ) / 2) ∂μ) =
      ∑' n : ℕ, ∫ u : ℝ, term z f n u ∂μ := by
  calc
    (∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ) / 2) ∂μ) =
        ∫ u : ℝ, (∑' n : ℕ, term z f n u) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with u
          exact (tsum_term z f u).symm
    _ = ∑' n : ℕ, ∫ u : ℝ, term z f n u ∂μ :=
          integral_tsum μ hsupport z f hf

#print axioms GegenbauerFock.BochnerTaylor.norm_term_le
#print axioms GegenbauerFock.BochnerTaylor.term_integrable
#print axioms GegenbauerFock.BochnerTaylor.summable_integrals_norm
#print axioms GegenbauerFock.BochnerTaylor.integral_tsum
#print axioms GegenbauerFock.BochnerTaylor.tsum_term
#print axioms GegenbauerFock.BochnerTaylor.integral_exp_eq_tsum

end GegenbauerFock.BochnerTaylor
