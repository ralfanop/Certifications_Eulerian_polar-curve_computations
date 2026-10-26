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


/-- Equality of the actual bounded Fourier-integral functional and
the concrete Fock evaluation composite at zero complex frequency.
This is a continuous-linear-map equality, not just a scalar example. -/
theorem evaluatedOperator_zero_eq_fourier
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    evaluatedOperator lam alpha hlam ha 0 =
      Ultraspherical.fourierFunctional lam hlam 0 := by
  ext f
  rw [evaluatedOperator_at_zero,
    Ultraspherical.fourierFunctional_integral]
  simp

#print axioms GegenbauerFock.GeneralUltrasphericalFock.evaluatedOperator_zero_eq_fourier



/-- Exact cancellation of the two real square-root factors in the
Gaussian Fock evaluation and ultraspherical monomial coefficient. -/
theorem fock_amplitude_product
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) *
      Real.sqrt (WeightedMoments.squareWeight alpha n) =
        (1 / 2 : ℝ) ^ n / (Nat.factorial n : ℝ) := by
  have hα : alpha ≠ 0 := ne_of_gt ha
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have harg : 0 ≤ alpha ^ n / (Nat.factorial n : ℝ) := by positivity
  have hweight : 0 ≤ WeightedMoments.squareWeight alpha n :=
    WeightedMoments.squareWeight_nonneg alpha ha n
  have hleft : 0 ≤
      Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) *
        Real.sqrt (WeightedMoments.squareWeight alpha n) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright : 0 ≤ (1 / 2 : ℝ) ^ n / (Nat.factorial n : ℝ) := by
    positivity
  have hfour : alpha * (1 / (4 * alpha)) = (1 / 4 : ℝ) := by
    field_simp
    <;> ring
  have hfactor :
      (alpha ^ n / (Nat.factorial n : ℝ)) *
        WeightedMoments.squareWeight alpha n =
      ((1 / 2 : ℝ) ^ n / (Nat.factorial n : ℝ)) ^ 2 := by
    unfold WeightedMoments.squareWeight
    calc
      (alpha ^ n / (Nat.factorial n : ℝ)) *
          ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) =
        (alpha * (1 / (4 * alpha))) ^ n /
          ((Nat.factorial n : ℝ) ^ 2) := by
            rw [mul_pow]
            ring
      _ = (1 / 4 : ℝ) ^ n / ((Nat.factorial n : ℝ) ^ 2) := by
            rw [hfour]
      _ = ((1 / 2 : ℝ) ^ n / (Nat.factorial n : ℝ)) ^ 2 := by
            have hpow : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
              calc
                (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ 2) ^ n := by norm_num
                _ = ((1 / 2 : ℝ) ^ n) ^ 2 := by
                  rw [← pow_mul, mul_comm 2 n, pow_mul]
            rw [hpow, div_pow]
            ring
  have hsq :
      (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) *
        Real.sqrt (WeightedMoments.squareWeight alpha n)) ^ 2 =
      ((1 / 2 : ℝ) ^ n / (Nat.factorial n : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt harg, Real.sq_sqrt hweight]
    exact hfactor
  nlinarith

#print axioms GegenbauerFock.GeneralUltrasphericalFock.fock_amplitude_product


/-- Each Fock reproducing-kernel coordinate multiplied by the
normalised Fourier coefficient has exactly the Taylor amplitude
\((iz/2)^n/n!\), including its complex phase. -/
theorem fock_kernel_weight
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) (n : ℕ) :
    inner ℂ (FockEvaluation.kernelCoordinate alpha z n)
      (WeightedMoments.complexWeight alpha n) =
        (Complex.I * z / 2) ^ n / (Nat.factorial n : ℂ) := by
  have hamp := fock_amplitude_product alpha ha n
  have hampC :
      (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) *
        (Real.sqrt (WeightedMoments.squareWeight alpha n) : ℂ) =
          (1 / 2 : ℂ) ^ n / (Nat.factorial n : ℂ) := by
    calc
      (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) *
          (Real.sqrt (WeightedMoments.squareWeight alpha n) : ℂ) =
          ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) *
            Real.sqrt (WeightedMoments.squareWeight alpha n) : ℝ) : ℂ) := by
              push_cast
              rfl
      _ = (((1 / 2 : ℝ) ^ n / (Nat.factorial n : ℝ)) : ℂ) := by
            exact congrArg (fun x : ℝ => (x : ℂ)) hamp
      _ = (1 / 2 : ℂ) ^ n / (Nat.factorial n : ℂ) := by
            push_cast
            ring
  rw [RCLike.inner_apply']
  change star ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) *
      (star z) ^ n) *
      ((Real.sqrt (WeightedMoments.squareWeight alpha n) : ℂ) *
        Complex.I ^ n) = _
  rw [star_mul, star_pow, star_star]
  have hstar :
      star (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) =
        (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) := by simp
  rw [hstar]
  calc
    z ^ n * (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) *
        ((Real.sqrt (WeightedMoments.squareWeight alpha n) : ℂ) *
          Complex.I ^ n) =
      ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) *
        (Real.sqrt (WeightedMoments.squareWeight alpha n) : ℂ)) *
        (Complex.I * z) ^ n := by
          rw [mul_pow]
          ring
    _ = ((1 / 2 : ℂ) ^ n / (Nat.factorial n : ℂ)) *
          (Complex.I * z) ^ n := by rw [hampC]
    _ = (Complex.I * z / 2) ^ n / (Nat.factorial n : ℂ) := by
          simp only [div_pow, one_pow]
          ring

#print axioms GegenbauerFock.GeneralUltrasphericalFock.fock_kernel_weight


/-- Exact identification of the nth evaluated Fock coefficient
with the corresponding genuine complex Bochner integral.  The
infinite-series/integral exchange is a separate theorem. -/
theorem evaluation_term_eq_integral
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ) (n : ℕ) (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    inner ℂ (FockEvaluation.kernelCoordinate alpha z n)
      (WeightedMoments.coefficient (Ultraspherical.measure lam)
        (ae_abs_le_one lam) alpha n f) =
      ∫ u : ℝ, f u *
        ((Complex.I * z * (u : ℂ) / 2) ^ n / (Nat.factorial n : ℂ))
          ∂(Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  rw [WeightedMoments.coefficient_integral
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n f]
  rw [RCLike.inner_apply', ← mul_assoc]
  have hw := fock_kernel_weight alpha ha z n
  rw [RCLike.inner_apply'] at hw
  rw [hw, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  calc
    ((Complex.I * z / 2) ^ n / (Nat.factorial n : ℂ)) *
        ((u : ℂ) ^ n * f u) =
      f u * (((Complex.I * z / 2) * (u : ℂ)) ^ n /
        (Nat.factorial n : ℂ)) := by
          rw [mul_pow]
          ring
    _ = f u * ((Complex.I * z * (u : ℂ) / 2) ^ n /
        (Nat.factorial n : ℂ)) := by
          congr 2
          ring

#print axioms GegenbauerFock.GeneralUltrasphericalFock.evaluation_term_eq_integral

end GegenbauerFock.GeneralUltrasphericalFock
