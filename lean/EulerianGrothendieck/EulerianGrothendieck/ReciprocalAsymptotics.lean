import EulerianGrothendieck.PolynomialAbsoluteBounds
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Finite-order inversion with a consistent, infinite sequence of reciprocal
coefficients. All low-degree cancellations are proved in the power-series ring. -/
noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace EulerianGrothendieck

def inverseSeriesCoefficient (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  PowerSeries.coeff r ((PowerSeries.mk b)⁻¹)

theorem trunc_eval_eq (f : PowerSeries ℝ) (R : ℕ) (h : ℝ) :
    (PowerSeries.trunc (R+1) f).eval h =
      ∑ r ∈ range (R+1), PowerSeries.coeff r f*h^r := by
  exact PowerSeries.eval₂_trunc_eq_sum_range h (RingHom.id ℝ) (R+1) f

theorem polynomial_abs_eval_le (p : ℝ[X]) (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    |p.eval h| ≤ polyAbsEval p 1 := by
  have hb : ∀ r : ℕ, ‖p.coeff r*h^r‖ ≤ |p.coeff r| * (1:ℝ)^r := by
    intro r
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hh r), one_pow, mul_one]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hh hh1)
  have H := tsum_of_norm_bounded (polyAbsEval_summable p 1).hasSum hb
  rwa [(polynomial_evaluation_hasSum p h).tsum_eq, Real.norm_eq_abs] at H

theorem polynomial_zero_low_coeff_remainder (p : ℝ[X]) (R : ℕ) (h : ℝ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hz : ∀ r ≤ R, p.coeff r = 0) :
    |p.eval h| ≤ polyAbsEval p 1*h^(R+1) := by
  have hb : ∀ r : ℕ, ‖p.coeff r*h^r‖ ≤ (|p.coeff r| * (1:ℝ)^r)*h^(R+1) := by
    intro r
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hh r), one_pow, mul_one]
    by_cases hr : r ≤ R
    · rw [hz r hr]; simp
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hh hh1 (show R+1 ≤ r by omega)) (abs_nonneg _)
  have H := tsum_of_norm_bounded ((polyAbsEval_summable p 1).hasSum.mul_right (h^(R+1))) hb
  rwa [(polynomial_evaluation_hasSum p h).tsum_eq, Real.norm_eq_abs] at H

theorem truncated_inverse_low_coeff (b : ℕ → ℝ) (hb : b 0 ≠ 0) (R r : ℕ) (hr : r ≤ R) :
    ((PowerSeries.trunc (R+1) (PowerSeries.mk b))*
      (PowerSeries.trunc (R+1) ((PowerSeries.mk b)⁻¹))).coeff r =
      (if r=0 then 1 else 0) := by
  have h := PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc
    (PowerSeries.mk b) ((PowerSeries.mk b)⁻¹) (show r<R+1 by omega)
  rw [PowerSeries.mul_inv_cancel _ (by simpa using hb), PowerSeries.coeff_one] at h
  simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using h.symm

/-- General all-order inversion, under an actual positive lower bound for the
sequence. No asymptotic property of its inverse is assumed. -/
theorem reciprocal_all_order_remainder (N : ℕ → ℝ) (b : ℕ → ℝ) (η : ℝ)
    (hη : 0 < η) (hN : ∀ M : ℕ, M ≠ 0 → η ≤ N M) (hb : b 0 ≠ 0)
    (hrem : ∀ R : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |N M-∑ r ∈ range (R+1), b r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1))
    (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |1/(N M)-∑ r ∈ range (R+1), inverseSeriesCoefficient b r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  let B := PowerSeries.trunc (R+1) (PowerSeries.mk b)
  let D := PowerSeries.trunc (R+1) ((PowerSeries.mk b)⁻¹)
  let S := polyAbsEval D 1
  let T := polyAbsEval (1-B*D) 1
  obtain ⟨C, hC, hCrem⟩ := hrem R
  have hS : 0 ≤ S := polyAbsEval_nonneg D 1 (by norm_num)
  have hT : 0 ≤ T := polyAbsEval_nonneg (1-B*D) 1 (by norm_num)
  refine ⟨(T+C*S)/η, by positivity, ?_⟩
  intro M hM
  let h := 1/(M:ℝ)
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := (div_le_one (by positivity)).2 hM1
  have hBval : B.eval h = ∑ r ∈ range (R+1), b r/(M:ℝ)^r := by
    rw [trunc_eval_eq]
    simp only [PowerSeries.coeff_mk, h, one_div_pow, mul_one_div]
  have hDval : D.eval h = ∑ r ∈ range (R+1), inverseSeriesCoefficient b r/(M:ℝ)^r := by
    rw [trunc_eval_eq]
    simp only [inverseSeriesCoefficient, h, one_div_pow, mul_one_div]
  have hz : ∀ r ≤ R, (1-B*D).coeff r = 0 := by
    intro r hr
    rw [Polynomial.coeff_sub, Polynomial.coeff_one, truncated_inverse_low_coeff b hb R r hr]
    ring
  have hBD : |1-B.eval h*D.eval h| ≤ T*h^(R+1) := by
    simpa only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul] using
      polynomial_zero_low_coeff_remainder (1-B*D) R h hh hh1 hz
  have hNB : |N M-B.eval h| ≤ C*h^(R+1) := by
    rw [hBval]
    simpa only [h, one_div_pow, mul_one_div] using hCrem M hM
  have H := reciprocal_remainder_transfer (N M) (B.eval h) (D.eval h) C T S η h (R+1)
    hη (hN M hM) hh hC hT hS hNB hBD (polynomial_abs_eval_le D h hh hh1)
  simpa only [hDval, h, one_div_pow, mul_one_div] using H

end EulerianGrothendieck
