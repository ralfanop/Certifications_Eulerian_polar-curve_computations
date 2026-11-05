import GegenbauerFock.OutputComplexEvaluationContinuity
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# V007 — entire holomorphy of the genuine coherent Fock reconstruction

The actual infinite-dimensional coherent evaluation is represented by
its complex monomial series. On every disk the terms admit a summable
Hölder majorant, so the Weierstrass theorem for complex differentiable
series proves holomorphy of the *actual* evaluation, not of a truncation.

This module does not yet claim coefficient uniqueness or injectivity of
the Gegenbauer–Fock adjoint.
-/

noncomputable section

open Set
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockEvaluation

/-- Exact monomial form of each scalar coherent-evaluation term. -/
theorem inner_kernelCoordinate_eq_monomial
    (alpha : ℝ) (z : ℂ) (n : ℕ) (a : ℂ) :
    inner ℂ (kernelCoordinate alpha z n) a =
      ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * z ^ n) * a := by
  simp [kernelCoordinate, mul_comm, mul_left_comm, mul_assoc]

/-- The true infinite coherent evaluation is a complex power series. -/
theorem evaluation_eq_tsum_monomial
    (alpha : ℝ) (ha : 0 < alpha)
    (z : ℂ) (F : FockSequence.Coefficients) :
    evaluation alpha ha z F =
      ∑' n : ℕ,
        ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * z ^ n) * F n := by
  rw [evaluation_eq_tsum_inner]
  apply tsum_congr
  intro n
  exact inner_kernelCoordinate_eq_monomial alpha z n (F n)

/-- The actual coherent evaluation is complex differentiable on any disk. -/
theorem differentiableOn_evaluation_complex_ball
    (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients)
    (R : ℝ) (hR : 0 < R) :
    DifferentiableOn ℂ (fun z : ℂ => evaluation alpha ha z F)
      (Metric.ball (0 : ℂ) R) := by
  let k := kernelVector alpha ha (R : ℂ)
  have hs : Summable (fun n : ℕ =>
      ‖kernelCoordinate alpha (R : ℂ) n‖ * ‖F n‖) := by
    exact lp.summable_mul
      (by rw [Real.holderConjugate_iff]; norm_num) k F
  have hterm (n : ℕ) :
      DifferentiableOn ℂ (fun z : ℂ =>
        inner ℂ (kernelCoordinate alpha z n) (F n))
        (Metric.ball (0 : ℂ) R) := by
    have h : Differentiable ℂ (fun z : ℂ =>
        ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * z ^ n) * F n) := by
      fun_prop
    simpa only [inner_kernelCoordinate_eq_monomial] using h.differentiableOn
  have hbound (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) (n : ℕ) :
      ‖kernelCoordinate alpha z n‖ ≤
        ‖kernelCoordinate alpha (R : ℂ) n‖ := by
    have hz' : ‖z‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hnorm : ‖z‖ ≤ |R| := by
      simpa [abs_of_pos hR] using (le_of_lt hz')
    unfold kernelCoordinate
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_star]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hnorm n) (abs_nonneg _)
  have hhol :
      DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ,
        inner ℂ (kernelCoordinate alpha z n) (F n))
        (Metric.ball (0 : ℂ) R) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hs hterm Metric.isOpen_ball
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
  exact hhol

/-- Entire holomorphy of the genuine ℓ² coherent Fock reconstruction. -/
theorem differentiable_evaluation_complex
    (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients) :
    Differentiable ℂ (fun z : ℂ => evaluation alpha ha z F) := by
  intro z
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    simp [Metric.mem_ball, dist_zero_right, R]
  exact (differentiableOn_evaluation_complex_ball alpha ha F R hR z hz).differentiableAt
    (Metric.isOpen_ball.mem_nhds hz)

#print axioms GegenbauerFock.FockEvaluation.inner_kernelCoordinate_eq_monomial
#print axioms GegenbauerFock.FockEvaluation.evaluation_eq_tsum_monomial
#print axioms GegenbauerFock.FockEvaluation.differentiableOn_evaluation_complex_ball
#print axioms GegenbauerFock.FockEvaluation.differentiable_evaluation_complex

end GegenbauerFock.FockEvaluation
