import GegenbauerFock.FockEvaluationSequence
import GegenbauerFock.GeneralUltrasphericalFock
import GegenbauerFock.GeneralFockNormBound

/-!
# V007: Fock point evaluation of the concrete ultraspherical Hilbert operator

This theorem combines the bounded evaluation functional on the
coefficient Hilbert space with the concrete ultraspherical Fock
operator and proves an exact, convergent coefficient-series formula
for their composition.

The final identification of this series with the Bochner Fourier
integral ∫ f(u) exp(i z u / 2) dν_λ(u) is a separate convergence and
term-by-term-integration theorem, not smuggled into this declaration.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem evaluation_C_eq_tsum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ) (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    FockEvaluation.evaluation alpha ha z (C lam alpha hlam ha f) =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      ∑' n : ℕ, inner ℂ (FockEvaluation.kernelCoordinate alpha z n)
        (WeightedMoments.coefficient (Ultraspherical.measure lam)
          (ae_abs_le_one lam) alpha n f) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  rw [FockEvaluation.evaluation_eq_tsum_inner]
  apply tsum_congr
  intro n
  rw [C_coefficient lam alpha hlam ha f n]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.evaluation_C_eq_tsum

/-- The pointwise Fock evaluation composed with the actual ultraspherical
operator is a bounded complex-linear functional on the input L² space. -/
noncomputable def evaluatedOperator
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (z : ℂ) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ] ℂ :=
  (FockEvaluation.evaluation alpha ha z).comp (C lam alpha hlam ha)

/-- Point evaluation of the operator has the proven convergent weighted
moment series, not merely a formal power series. -/
theorem evaluatedOperator_eq_tsum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ) (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    evaluatedOperator lam alpha hlam ha z f =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      ∑' n : ℕ, inner ℂ (FockEvaluation.kernelCoordinate alpha z n)
        (WeightedMoments.coefficient (Ultraspherical.measure lam)
          (ae_abs_le_one lam) alpha n f) :=
  evaluation_C_eq_tsum lam alpha hlam ha z f

/-- Genuine Hilbert adjoint of the composed point-evaluation operator.
The scalar evaluation is adjointed *before* the Fock analysis operator:
no unproved Fourier integral identification is used here. -/
theorem evaluatedOperator_adjoint_apply
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z w : ℂ) :
    (evaluatedOperator lam alpha hlam ha z).adjoint w =
      (C lam alpha hlam ha).adjoint
        ((FockEvaluation.evaluation alpha ha z).adjoint w) := by
  apply ext_inner_right ℂ
  intro f
  calc
    inner ℂ ((evaluatedOperator lam alpha hlam ha z).adjoint w) f =
        inner ℂ w (evaluatedOperator lam alpha hlam ha z f) :=
          (evaluatedOperator lam alpha hlam ha z).adjoint_inner_left f w
    _ = inner ℂ w (FockEvaluation.evaluation alpha ha z
        (C lam alpha hlam ha f)) := rfl
    _ = inner ℂ ((FockEvaluation.evaluation alpha ha z).adjoint w)
        (C lam alpha hlam ha f) :=
          ((FockEvaluation.evaluation alpha ha z).adjoint_inner_left
            (C lam alpha hlam ha f) w).symm
    _ = inner ℂ ((C lam alpha hlam ha).adjoint
        ((FockEvaluation.evaluation alpha ha z).adjoint w)) f :=
          ((C lam alpha hlam ha).adjoint_inner_left f
            ((FockEvaluation.evaluation alpha ha z).adjoint w)).symm

/-- Explicit Gaussian-growth estimate for genuine point evaluation of C.
This concerns the bounded coefficient model and makes no unsupported
claim that the moment series is already identified with its integral. -/
theorem evaluatedOperator_norm_apply_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ) (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    ‖evaluatedOperator lam alpha hlam ha z f‖ ≤
      ‖FockEvaluation.kernelVector alpha ha z‖ *
        Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖f‖ := by
  calc
    ‖evaluatedOperator lam alpha hlam ha z f‖ =
        ‖FockEvaluation.evaluation alpha ha z (C lam alpha hlam ha f)‖ := rfl
    _ ≤ ‖FockEvaluation.evaluation alpha ha z‖ *
          ‖C lam alpha hlam ha f‖ :=
          (FockEvaluation.evaluation alpha ha z).le_opNorm _
    _ ≤ ‖FockEvaluation.evaluation alpha ha z‖ *
          (‖C lam alpha hlam ha‖ * ‖f‖) :=
          mul_le_mul_of_nonneg_left
            ((C lam alpha hlam ha).le_opNorm f) (norm_nonneg _)
    _ ≤ ‖FockEvaluation.evaluation alpha ha z‖ *
          (Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖f‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (C_opNorm_le_exp lam alpha hlam ha) (norm_nonneg _)
    _ = ‖FockEvaluation.kernelVector alpha ha z‖ *
          Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖f‖ := by
          rw [FockEvaluation.evaluation_norm]
          ring

#print axioms GegenbauerFock.GeneralUltrasphericalFock.evaluatedOperator_eq_tsum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.evaluatedOperator_adjoint_apply
#print axioms GegenbauerFock.GeneralUltrasphericalFock.evaluatedOperator_norm_apply_le


/-- The complete composed point-evaluation operator at z=0 equals
the genuine Bochner integral of the input L² class. This is a
kernel-level base case of the general complex-frequency identity. -/
theorem evaluatedOperator_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    evaluatedOperator lam alpha hlam ha 0 f =
      ∫ u : ℝ, f u ∂(Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  calc
    evaluatedOperator lam alpha hlam ha 0 f =
        (C lam alpha hlam ha f) 0 :=
          FockEvaluation.evaluation_at_zero alpha ha (C lam alpha hlam ha f)
    _ = WeightedMoments.coefficient (Ultraspherical.measure lam)
        (ae_abs_le_one lam) alpha 0 f :=
          C_coefficient lam alpha hlam ha f 0
    _ = ∫ u : ℝ, f u ∂(Ultraspherical.measure lam) :=
          WeightedMoments.coefficient_zero_integral
            (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.evaluatedOperator_at_zero


end GegenbauerFock.GeneralUltrasphericalFock
