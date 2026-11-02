import V033ProbabilityFunctional
import V033RecurrenceGram
import V033CumulantPolynomials
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Manuscript 12, Subsection 9.5: the first two recurrence coefficients, exactly

For the law of `S_M = U_1 + ⋯ + U_M` (independent uniform on `[-1/2,1/2]`):
`μ_2 = M/12`, `μ_4 = M^2/48 - M/120`, and, for every `M ≥ 1`,
`β_1^{[M]} = M/12`, `β_2^{[M]} = M/6 - 1/10`, `κ_4(S_M) = β_1(β_2 - 2β_1) = -M/120`,
both as Hankel quotients of the actual moments and for every monic Lanczos family of the
moment functional (`Gram.IsLanczosFamily`). -/

noncomputable section
namespace V033.UniformSum
open Polynomial Finset Matrix MeasureTheory ProbabilityTheory

theorem single_zero : singleMoment 0 = 1 := by
  rw [show (0:ℕ) = 2*0 from rfl, singleMoment_even]; norm_num

theorem single_one : singleMoment 1 = 0 := by
  simpa using singleMoment_odd 0

theorem single_two : singleMoment 2 = 1/12 := by
  rw [show (2:ℕ) = 2*1 from rfl, singleMoment_even]; norm_num

theorem single_three : singleMoment 3 = 0 := by
  simpa using singleMoment_odd 1

theorem single_four : singleMoment 4 = 1/80 := by
  rw [show (4:ℕ) = 2*2 from rfl, singleMoment_even]; norm_num

theorem sum_zero (M : ℕ) : sumMoment M 0 = 1 := by
  induction M with
  | zero => simp [sumMoment]
  | succ M ih => simp [sumMoment, ih, single_zero]

theorem sum_one (M : ℕ) : sumMoment M 1 = 0 := by
  simpa using sumMoment_odd M 0

theorem sum_three (M : ℕ) : sumMoment M 3 = 0 := by
  simpa using sumMoment_odd M 1

/-- `μ_2 = M/12`. -/
theorem sum_two (M : ℕ) : sumMoment M 2 = (M:ℝ)/12 := by
  induction M with
  | zero => simp [sumMoment]
  | succ M ih =>
    rw [sumMoment]
    simp [Finset.sum_range_succ, ih, sum_zero, sum_one, single_zero, single_one, single_two]
    ring

/-- `μ_4 = M^2/48 - M/120`. -/
theorem sum_four (M : ℕ) : sumMoment M 4 = (M:ℝ)^2/48 - (M:ℝ)/120 := by
  induction M with
  | zero => simp [sumMoment]
  | succ M ih =>
    rw [sumMoment]
    simp [Finset.sum_range_succ, ih, sum_zero, sum_one, sum_two, sum_three,
      single_zero, single_one, single_two, single_three, single_four, Nat.choose]
    ring

/-- The fourth cumulant `κ_4(S_M) = μ_4 - 3μ_2^2 = -M/120`. -/
theorem fourth_cumulant (M : ℕ) : sumMoment M 4 - 3 * (sumMoment M 2)^2 = -(M:ℝ)/120 := by
  rw [sum_four, sum_two]; ring

theorem rf_one (M : ℕ) : rawFunctional M 1 = 1 := by
  rw [← pow_zero (X:ℝ[X]), rawFunctional_X_pow, sum_zero]

theorem rf_X (M : ℕ) : rawFunctional M X = 0 := by
  rw [← pow_one (X:ℝ[X]), rawFunctional_X_pow, sum_one]

theorem hankel_zero_det (M : ℕ) : (Gram.hankel (rawFunctional M) 0).det = 1 :=
  Matrix.det_isEmpty

theorem hankel_one_det (M : ℕ) : (Gram.hankel (rawFunctional M) 1).det = 1 := by
  rw [Matrix.det_fin_one]
  simp [Gram.hankel, rf_one]

theorem hankel_two_det (M : ℕ) : (Gram.hankel (rawFunctional M) 2).det = (M:ℝ)/12 := by
  rw [Matrix.det_fin_two]
  simp [Gram.hankel, rf_one, rf_X, sum_two]

theorem hankel_three_det (M : ℕ) :
    (Gram.hankel (rawFunctional M) 3).det =
      sumMoment M 2 * sumMoment M 4 - (sumMoment M 2)^3 := by
  rw [Matrix.det_fin_three]
  simp [Gram.hankel, rf_one, rf_X, sum_three]
  ring

/-- `β_1^{[M]} = M/12` as the Hankel quotient of the actual moments. -/
theorem exact_beta_one (M : ℕ) :
    (Gram.hankel (rawFunctional M) 2).det * (Gram.hankel (rawFunctional M) 0).det /
      (Gram.hankel (rawFunctional M) 1).det^2 = (M:ℝ)/12 := by
  rw [hankel_two_det, hankel_zero_det, hankel_one_det]; ring

/-- `β_2^{[M]} = M/6 - 1/10` as the Hankel quotient of the actual moments, `M ≥ 1`. -/
theorem exact_beta_two (M : ℕ) (hM : M ≠ 0) :
    (Gram.hankel (rawFunctional M) 3).det * (Gram.hankel (rawFunctional M) 1).det /
      (Gram.hankel (rawFunctional M) 2).det^2 = (M:ℝ)/6 - 1/10 := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  rw [hankel_three_det, hankel_one_det, hankel_two_det, sum_two, sum_four]
  field_simp
  ring

/-- The same values for every monic Lanczos family of the moment functional of `S_M`, with
`μ_2 = β_1`, `μ_4 = β_1^2 + β_1β_2` and `κ_4 = β_1(β_2 - 2β_1) = -M/120`. -/
theorem lanczos_first_two (M : ℕ) (hM : M ≠ 0) (P : ℕ → ℝ[X]) (β : ℕ → ℝ)
    (h : Gram.IsLanczosFamily (rawFunctional M) P β) :
    β 1 = (M:ℝ)/12 ∧ β 2 = (M:ℝ)/6 - 1/10 ∧
    sumMoment M 2 = β 1 ∧ sumMoment M 4 = (β 1)^2 + β 1 * β 2 ∧
    β 1 * (β 2 - 2 * β 1) = -(M:ℝ)/120 := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  have h1 : β 1 = (M:ℝ)/12 := by
    rw [h.coefficient_as_determinants 0 (by rw [hankel_one_det]; norm_num), exact_beta_one]
  have h2 : β 2 = (M:ℝ)/6 - 1/10 := by
    rw [h.coefficient_as_determinants 1
      (by rw [hankel_two_det]; exact div_ne_zero hm (by norm_num)), exact_beta_two M hM]
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rw [sum_two, h1]
  · rw [sum_four, h1, h2]; ring
  · rw [h1, h2]; ring

/-- The moments of the actual random variable `S_M`. -/
theorem actual_second_fourth {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = uniformLaw) (M : ℕ) :
    (∫ ω, (∑ k ∈ range M, U k ω)^2 ∂μ) = (M:ℝ)/12 ∧
    (∫ ω, (∑ k ∈ range M, U k ω)^4 ∂μ) = (M:ℝ)^2/48 - (M:ℝ)/120 := by
  refine ⟨?_, ?_⟩
  · rw [(all_sum_moments U hU hind hlaw M 2).2, sum_two]
  · rw [(all_sum_moments U hU hind hlaw M 4).2, sum_four]

end V033.UniformSum
