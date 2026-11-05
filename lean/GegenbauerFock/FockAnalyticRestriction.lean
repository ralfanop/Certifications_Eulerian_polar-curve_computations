import GegenbauerFock.GramIntegralKernel

/-!
# V007: actual analytic point-evaluation restriction along the imaginary axis

This module proves measurability of the reconstructed Fock evaluation
on the imaginary line, and prepares its L² interpretation independently
of the Hilbert adjoint. No pointwise representative is assigned to
an arbitrary L² equivalence class.
-/

open MeasureTheory
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockAnalyticRestriction

/-- The imaginary point corresponding to a real ultraspherical coordinate. -/
noncomputable def imaginaryPoint (alpha : ℝ) (u : ℝ) : ℂ :=
  -Complex.I * (u : ℂ) / (2 * (alpha : ℂ))

/-- Pointwise reconstruction of the analytic Fock coefficient vector,
restricted to the imaginary axis at w=-i*u/(2α). -/
noncomputable def evaluate (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) (u : ℝ) : ℂ :=
  FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u) F

/-- The analytic restriction is a measurable complex-valued function
of u, for an arbitrary infinite Fock vector. -/
theorem measurable_evaluate (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    Measurable (evaluate alpha ha F) := by
  have hterm (n : ℕ) :
      Measurable (fun u : ℝ =>
        inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)) := by
    have hc : Continuous (fun u : ℝ =>
        inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)) := by
      unfold imaginaryPoint FockEvaluation.kernelCoordinate
      fun_prop
    exact hc.measurable
  have heq :
      evaluate alpha ha F =
        fun u : ℝ => ∑' n : ℕ,
          inner ℂ
            (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
            (F n) := by
    funext u
    exact FockEvaluation.evaluation_eq_tsum_inner
      alpha ha (imaginaryPoint alpha u) F
  rw [heq]
  exact Measurable.tsum hterm

#print axioms GegenbauerFock.FockAnalyticRestriction.measurable_evaluate

/-- Exact norm of the imaginary Fock evaluation argument. -/
theorem norm_imaginaryPoint (alpha u : ℝ) (ha : 0 < alpha) :
    ‖imaginaryPoint alpha u‖ = |u| / (2 * alpha) := by
  unfold imaginaryPoint
  simp [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha, mul_comm]

/-- Uniform evaluation bound on the full ultraspherical support. -/
theorem norm_evaluate_le (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) (u : ℝ)
    (hu : |u| ≤ 1) :
    ‖evaluate alpha ha F u‖ ≤
      Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖F‖ := by
  have hne : alpha ≠ 0 := ne_of_gt ha
  have hc :
      alpha * ‖imaginaryPoint alpha u‖ ^ 2 ≤
        1 / (4 * alpha) := by
    rw [norm_imaginaryPoint alpha u ha]
    have hu2 : |u| ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg u]
    calc
      alpha * (|u| / (2 * alpha)) ^ 2 =
          |u| ^ 2 / (4 * alpha) := by
            field_simp
            <;> ring
      _ ≤ 1 / (4 * alpha) := by
        exact div_le_div_of_nonneg_right hu2 (by positivity)
  have hk :
      ‖FockEvaluation.kernelVector alpha ha
        (imaginaryPoint alpha u)‖ ≤
        Real.sqrt (Real.exp (1 / (4 * alpha))) := by
    have hb :
        ‖FockEvaluation.kernelVector alpha ha
          (imaginaryPoint alpha u)‖ ^ 2 ≤
          Real.exp (1 / (4 * alpha)) := by
      calc
        _ = Real.exp (alpha * ‖imaginaryPoint alpha u‖ ^ 2) :=
          FockEvaluation.kernelVector_norm_sq alpha ha _
        _ ≤ _ := Real.exp_monotone hc
    have hpos := Real.sqrt_nonneg (Real.exp (1 / (4 * alpha)))
    have hsqr := Real.sq_sqrt (Real.exp_nonneg (1 / (4 * alpha)))
    nlinarith [norm_nonneg (FockEvaluation.kernelVector alpha ha
      (imaginaryPoint alpha u))]
  unfold evaluate
  calc
    ‖FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u) F‖ ≤
        ‖FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u)‖ *
          ‖F‖ :=
        (FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u)).le_opNorm F
    _ = ‖FockEvaluation.kernelVector alpha ha
          (imaginaryPoint alpha u)‖ * ‖F‖ := by
        rw [FockEvaluation.evaluation_norm]
    _ ≤ Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖F‖ :=
        mul_le_mul_of_nonneg_right hk (norm_nonneg _)

/-- The analytic evaluation along the imaginary axis is a bona fide
L² function on the actual ultraspherical law, for every F∈ℓ². -/
theorem memLp_evaluate (lam alpha : ℝ) (hlam : 0 < lam)
    (ha : 0 < alpha) (F : InfiniteAnalysis.FockCoefficients) :
    MemLp (evaluate alpha ha F) 2 (Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  apply MemLp.of_bound
    (measurable_evaluate alpha ha F).aestronglyMeasurable
    (Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖F‖)
  filter_upwards [Ultraspherical.ae_mem_unit_interval lam] with u hu
  exact norm_evaluate_le alpha ha F u (abs_le.mpr ⟨hu.1, hu.2⟩)

/-- Concrete L² equivalence class of the analytic imaginary-axis
restriction, constructed independently of the adjoint. -/
noncomputable def restrictionLp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    Lp ℂ 2 (Ultraspherical.measure lam) :=
  (memLp_evaluate lam alpha hlam ha F).toLp (evaluate alpha ha F)

#print axioms GegenbauerFock.FockAnalyticRestriction.norm_imaginaryPoint
#print axioms GegenbauerFock.FockAnalyticRestriction.norm_evaluate_le
#print axioms GegenbauerFock.FockAnalyticRestriction.memLp_evaluate


end GegenbauerFock.FockAnalyticRestriction
