import GegenbauerFock.OutputAnalyticCoordinateSeparation

/-!
# V007 — continuity of the actual coherent reconstruction on the complex plane

The coherent Fock point evaluation, originally constructed as a bounded
functional for each complex point, varies continuously with that point.
The proof is genuinely infinite-dimensional: it uses an ℓ² Hölder
majorant on each bounded complex disk and the locally uniform convergence
of the resulting scalar series.

Complex continuity is only a prerequisite for holomorphy. No analytic
identity theorem or injectivity of the output adjoint is claimed here.
-/

noncomputable section

open Set
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockEvaluation

/-- Local uniform convergence gives continuity of the actual coherent
evaluation on every complex disk centered at the origin. -/
theorem continuousOn_evaluation_complex_ball
    (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients)
    (R : ℝ) (hR : 0 < R) :
    ContinuousOn (fun z : ℂ => evaluation alpha ha z F)
      (Metric.ball (0 : ℂ) R) := by
  let k := kernelVector alpha ha (R : ℂ)
  have hs : Summable (fun n : ℕ =>
      ‖kernelCoordinate alpha (R : ℂ) n‖ * ‖F n‖) := by
    exact lp.summable_mul
      (by rw [Real.holderConjugate_iff]; norm_num) k F
  have hterm (n : ℕ) :
      Continuous (fun z : ℂ =>
        inner ℂ (kernelCoordinate alpha z n) (F n)) := by
    unfold kernelCoordinate
    fun_prop
  have hbound (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) (n : ℕ) :
      ‖kernelCoordinate alpha z n‖ ≤
        ‖kernelCoordinate alpha (R : ℂ) n‖ := by
    have hz' : ‖z‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hnorm : ‖z‖ ≤ ‖(R : ℂ)‖ := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using
        (le_of_lt hz')
    unfold kernelCoordinate
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_star]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hnorm n) (abs_nonneg _)
  have hcont :
      ContinuousOn (fun z : ℂ => ∑' n : ℕ,
        inner ℂ (kernelCoordinate alpha z n) (F n))
        (Metric.ball (0 : ℂ) R) := by
    apply continuousOn_tsum (fun n => (hterm n).continuousOn) hs
    intro n z hz
    calc
      ‖inner ℂ (kernelCoordinate alpha z n) (F n)‖ ≤
          ‖kernelCoordinate alpha z n‖ * ‖F n‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖kernelCoordinate alpha (R : ℂ) n‖ * ‖F n‖ :=
        mul_le_mul_of_nonneg_right (hbound z hz n) (norm_nonneg _)
  have heq : (fun z : ℂ => ∑' n : ℕ,
      inner ℂ (kernelCoordinate alpha z n) (F n)) =
        (fun z : ℂ => evaluation alpha ha z F) := by
    funext z
    exact (evaluation_eq_tsum_inner alpha ha z F).symm
  rw [← heq]
  exact hcont

/-- Global continuity of coherent evaluation as a function of its
complex argument. This is not yet the stronger holomorphy theorem. -/
theorem continuous_evaluation_complex
    (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients) :
    Continuous (fun z : ℂ => evaluation alpha ha z F) := by
  rw [continuous_iff_continuousAt]
  intro z
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    simp [Metric.mem_ball, dist_zero_right, R]
  exact (continuousOn_evaluation_complex_ball alpha ha F R hR z hz).continuousAt
    (Metric.isOpen_ball.mem_nhds hz)

#print axioms GegenbauerFock.FockEvaluation.continuousOn_evaluation_complex_ball
#print axioms GegenbauerFock.FockEvaluation.continuous_evaluation_complex

end GegenbauerFock.FockEvaluation
