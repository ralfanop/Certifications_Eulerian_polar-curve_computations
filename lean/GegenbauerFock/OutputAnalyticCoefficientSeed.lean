import GegenbauerFock.OutputInteriorContinuity

/-!
# V007 — local-to-global continuity and the first analytic coefficient

The actual coherent Fock reconstruction is continuous on every bounded
real interval, not merely on the ultraspherical support. Its value at
the origin extracts the zeroth Fock coefficient. Consequently, any
vector in the kernel of the genuine Gegenbauer–Fock adjoint has zero
zeroth coefficient.

These are initial steps toward analytic identity uniqueness, NOT a
proof that all coefficients vanish.
-/

noncomputable section

open Set
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockAnalyticRestriction

/-- Local uniform convergence of coherent evaluation on any open
symmetric interval. The summable majorant is the reproducing kernel
at its right endpoint. -/
theorem continuousOn_evaluate_Ioo_radius
    (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients)
    (R : ℝ) (hR : 0 < R) :
    ContinuousOn (evaluate alpha ha F) (Set.Ioo (-R) R) := by
  let k := FockEvaluation.kernelVector alpha ha (imaginaryPoint alpha R)
  have hs : Summable (fun n : ℕ =>
      ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha R) n‖ *
        ‖F n‖) := by
    exact lp.summable_mul
      (by rw [Real.holderConjugate_iff]; norm_num) k F
  have hterm (n : ℕ) :
      Continuous (fun u : ℝ =>
        inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)) := by
    unfold imaginaryPoint FockEvaluation.kernelCoordinate
    fun_prop
  have hbound (u : ℝ) (hu : u ∈ Set.Ioo (-R) R) (n : ℕ) :
      ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n‖ ≤
        ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha R) n‖ := by
    have hu' : |u| ≤ R :=
      abs_le.mpr ⟨le_of_lt (by linarith [hu.1]), le_of_lt hu.2⟩
    have hnorm : ‖imaginaryPoint alpha u‖ ≤ ‖imaginaryPoint alpha R‖ := by
      rw [norm_imaginaryPoint alpha u ha, norm_imaginaryPoint alpha R ha,
        abs_of_pos hR]
      exact div_le_div_of_nonneg_right hu' (by positivity)
    unfold FockEvaluation.kernelCoordinate
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_star]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hnorm n) (abs_nonneg _)
  have hcont :
      ContinuousOn (fun u : ℝ => ∑' n : ℕ,
        inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)) (Set.Ioo (-R) R) := by
    apply continuousOn_tsum (fun n => (hterm n).continuousOn) hs
    intro n u hu
    calc
      ‖inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)‖ ≤
          ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n‖ *
            ‖F n‖ := norm_inner_le_norm _ _
      _ ≤ ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha R) n‖ *
            ‖F n‖ :=
        mul_le_mul_of_nonneg_right (hbound u hu n) (norm_nonneg _)
  have heq : (fun u : ℝ => ∑' n : ℕ,
      inner ℂ
        (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
        (F n)) = evaluate alpha ha F := by
    funext u
    exact (FockEvaluation.evaluation_eq_tsum_inner
      alpha ha (imaginaryPoint alpha u) F).symm
  rw [← heq]
  exact hcont

/-- The genuine coherent restriction is globally continuous on ℝ. -/
theorem continuous_evaluate
    (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    Continuous (evaluate alpha ha F) := by
  rw [continuous_iff_continuousAt]
  intro u
  let R : ℝ := |u| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hu : u ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor
    · have h := neg_le_abs u
      linarith
    · have h := le_abs_self u
      linarith
  exact (continuousOn_evaluate_Ioo_radius alpha ha F R hR u hu).continuousAt
    (isOpen_Ioo.mem_nhds hu)

/-- At the origin the coherent reconstruction is the zeroth coefficient. -/
theorem evaluate_zero (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    evaluate alpha ha F 0 = F 0 := by
  change FockEvaluation.evaluation alpha ha (imaginaryPoint alpha 0) F = F 0
  have hz : imaginaryPoint alpha 0 = 0 := by simp [imaginaryPoint]
  rw [hz]
  exact FockEvaluation.evaluation_at_zero alpha ha F

#print axioms GegenbauerFock.FockAnalyticRestriction.continuousOn_evaluate_Ioo_radius
#print axioms GegenbauerFock.FockAnalyticRestriction.continuous_evaluate
#print axioms GegenbauerFock.FockAnalyticRestriction.evaluate_zero

end GegenbauerFock.FockAnalyticRestriction

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every adjoint-kernel vector has vanishing zeroth Fock coefficient.
This is a genuine coefficient-extraction statement, but it does not
yet prove that all higher coefficients vanish. -/
theorem C_adjoint_zero_implies_zeroth_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients)
    (hz : C_adjoint lam alpha hlam ha F = 0) :
    F 0 = 0 := by
  have hzero :=
    (C_adjoint_eq_zero_iff_interior_zero lam alpha hlam ha F).mp hz
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  simpa only [FockAnalyticRestriction.evaluate_zero] using hzero 0 hmem

/-- A nonzero vacuum coefficient obstructs membership in the kernel
of the genuine Hilbert adjoint. -/
theorem C_adjoint_ne_zero_of_zeroth_ne_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients)
    (h0 : F 0 ≠ 0) :
    C_adjoint lam alpha hlam ha F ≠ 0 := by
  intro hz
  exact h0 (C_adjoint_zero_implies_zeroth_zero lam alpha hlam ha F hz)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_zero_implies_zeroth_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_ne_zero_of_zeroth_ne_zero

end GegenbauerFock.GeneralUltrasphericalFock
