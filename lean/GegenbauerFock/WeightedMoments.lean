import Mathlib

/-!
# V007 concrete weighted monomial coefficient family

This file builds the ACTUAL factorially weighted moment coefficient
functionals on a genuine L² Hilbert space supported on [-1,1].
Its parameters are a probability measure μ with proved support in [-1,1]
and α > 0. The general ultraspherical Beta-pushforward measure is a
concrete instance of these hypotheses.

The next construction step assembles this square-summable family as
a bounded operator L²(μ) -> ℓ²(ℕ;ℂ). An explicit norm-equality for the
operator as a Hilbert-Schmidt operator and the equivalence with
holomorphic Gaussian Fock functions remain independent obligations.
No sorry, no custom axioms.
-/

open MeasureTheory

namespace GegenbauerFock.WeightedMoments

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))

/-- Positive squared coherent coefficient, cⁿ/n!, c=1/(4α). -/
noncomputable def squareWeight (alpha : ℝ) (n : ℕ) : ℝ :=
  (1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)

theorem squareWeight_nonneg (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    0 ≤ squareWeight alpha n := by
  unfold squareWeight
  positivity

theorem squareWeight_summable (alpha : ℝ) :
    Summable (squareWeight alpha) := by
  exact Real.summable_pow_div_factorial (1 / (4 * alpha))

/-- Factorial amplitude times the phase iⁿ. -/
noncomputable def complexWeight (alpha : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (squareWeight alpha n) : ℂ) * Complex.I ^ n

theorem complexWeight_norm_sq (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    ‖complexWeight alpha n‖ ^ 2 = squareWeight alpha n := by
  have hs : 0 ≤ Real.sqrt (squareWeight alpha n) := Real.sqrt_nonneg _
  have hn : ‖complexWeight alpha n‖ = Real.sqrt (squareWeight alpha n) := by
    unfold complexWeight
    simp [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hs]
  rw [hn, Real.sq_sqrt (squareWeight_nonneg alpha ha n)]

include hsupport

/-- L² membership of every complex monomial on the unit interval. -/
theorem monomial_memLp (n : ℕ) :
    MemLp (fun u : ℝ => (u : ℂ) ^ n) 2 μ := by
  have hc : Continuous (fun u : ℝ => (u : ℂ) ^ n) := by fun_prop
  apply MemLp.of_bound hc.aestronglyMeasurable 1
  filter_upwards [hsupport] with u hu
  calc
    ‖(u : ℂ) ^ n‖ = |u| ^ n := by simp
    _ ≤ (1 : ℝ) ^ n := by gcongr
    _ = 1 := by simp

/-- Genuine L² Riesz representer for the n-th monomial. -/
noncomputable def monomial (n : ℕ) : Lp ℂ 2 μ :=
  (monomial_memLp μ hsupport n).toLp (fun u : ℝ => (u : ℂ) ^ n)

/-- Uniform norm control of the concrete Riesz monomials. -/
theorem monomial_norm_le_one (n : ℕ) :
    ‖monomial μ hsupport n‖ ≤ 1 := by
  have hrep :
      (monomial μ hsupport n : ℝ → ℂ) =ᵐ[μ]
        (fun u : ℝ => (u : ℂ) ^ n) := by
    simpa only [monomial] using
      (monomial_memLp μ hsupport n).coeFn_toLp
  have hae : ∀ᵐ u ∂μ, ‖(monomial μ hsupport n : ℝ → ℂ) u‖ ≤ 1 := by
    filter_upwards [hrep, hsupport] with u he hu
    rw [he]
    calc
      ‖(u : ℂ) ^ n‖ = |u| ^ n := by simp
      _ ≤ (1 : ℝ) ^ n := by gcongr
      _ = 1 := by simp
  have h := Lp.norm_le_of_ae_bound
    (f := monomial μ hsupport n) (C := (1 : ℝ)) (by norm_num) hae
  have hm : measureUnivNNReal μ = 1 := by
    unfold measureUnivNNReal
    simp
  simpa [hm] using h

/-- The *concrete* Gegenbauer–Fock monomial coefficient functional,
including the iⁿ phase and the exact Gaussian/factorial amplitude. -/
noncomputable def coefficient (alpha : ℝ) (n : ℕ) :
    Lp ℂ 2 μ →L[ℂ] ℂ :=
  (complexWeight alpha n) • innerSL ℂ (monomial μ hsupport n)

/-- Its squared operator norm is bounded by cⁿ/n!. -/
theorem coefficient_norm_sq_le (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    ‖coefficient μ hsupport alpha n‖ ^ 2 ≤ squareWeight alpha n := by
  have hn : ‖monomial μ hsupport n‖ ^ 2 ≤ 1 := by
    have hb := monomial_norm_le_one μ hsupport n
    nlinarith [norm_nonneg (monomial μ hsupport n)]
  calc
    ‖coefficient μ hsupport alpha n‖ ^ 2 =
        ‖complexWeight alpha n‖ ^ 2 * ‖monomial μ hsupport n‖ ^ 2 := by
          unfold coefficient
          rw [norm_smul, innerSL_apply_norm, mul_pow]
    _ ≤ squareWeight alpha n * 1 := by
          rw [complexWeight_norm_sq alpha ha n]
          exact mul_le_mul_of_nonneg_left hn (squareWeight_nonneg alpha ha n)
    _ = squareWeight alpha n := by ring

/-- Square summability of the *actual* weighted moment functionals. -/
theorem coefficient_norm_sq_summable (alpha : ℝ) (ha : 0 < alpha) :
    Summable (fun n => ‖coefficient μ hsupport alpha n‖ ^ 2) := by
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (coefficient_norm_sq_le μ hsupport alpha ha)
    (squareWeight_summable alpha)

#print axioms GegenbauerFock.WeightedMoments.complexWeight_norm_sq
#print axioms GegenbauerFock.WeightedMoments.monomial_norm_le_one
#print axioms GegenbauerFock.WeightedMoments.coefficient_norm_sq_le
#print axioms GegenbauerFock.WeightedMoments.coefficient_norm_sq_summable

end GegenbauerFock.WeightedMoments
