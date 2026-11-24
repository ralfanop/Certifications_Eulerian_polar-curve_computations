import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
Manuscript 17, 24 Nov 2026, Cyclohedral.tex, theorem `m17-curvature-area`,
equation `m17-area-integration` (analytic step only).

The integral recorded in `numerics/arb/m17_independent_quadrature.py` and in
`certificates/M17_cassini_area_L8_30000_decimal_certificate_20261124.json`,

  2π ∫₀¹ ν² / (2 − ν²)² dν = π (1 − log(1 + √2) / √2),

is proved here as an identity of genuine Lebesgue interval integrals, by the
fundamental theorem of calculus with the explicit primitive

  F(ν) = ν / (2 (2 − ν²)) − (log(√2 + ν) − log(√2 − ν)) / (4 √2).

Not claimed: that this integral is the area of the Fefferman/Cassini lobe
(metric integration on the surface, a geometric statement), and the identity
log(1 + √2) / √2 = L₈(1, χ₂) (classical value of a Dirichlet L-series, a
published result cited). Neither is formalized in this module.
-/

noncomputable section

namespace EulerianCert.CassiniAreaIntegral20261124

open Real intervalIntegral MeasureTheory Set

/-- The integrand of `m17-area-integration`. -/
def areaDensity (ν : ℝ) : ℝ := ν ^ 2 / (2 - ν ^ 2) ^ 2

/-- Explicit primitive of `areaDensity` on `(−√2, √2)`. -/
def areaPrimitive (ν : ℝ) : ℝ :=
  ν / (2 * (2 - ν ^ 2)) - (Real.log (√2 + ν) - Real.log (√2 - ν)) / (4 * √2)

theorem sqrt2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem one_lt_sqrt2 : (1 : ℝ) < √2 := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt2_pos : (0 : ℝ) < √2 := by positivity

/-- On the closed lobe chart `0 ≤ ν ≤ 1` all factors of the primitive are positive. -/
theorem chart_factors_pos {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    0 < √2 + ν ∧ 0 < √2 - ν ∧ 0 < 2 - ν ^ 2 := by
  have hs := one_lt_sqrt2
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith

/-- `F' = areaDensity` at every point of `[0, 1]`. -/
theorem hasDerivAt_areaPrimitive {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    HasDerivAt areaPrimitive (areaDensity ν) ν := by
  obtain ⟨hp, hm, hq⟩ := chart_factors_pos h0 h1
  have hs2 := sqrt2_sq
  have hs0 : (√2 : ℝ) ≠ 0 := sqrt2_pos.ne'
  have hd : HasDerivAt (fun x : ℝ => 2 * (2 - x ^ 2)) (2 * (0 - 2 * ν)) ν := by
    have := ((hasDerivAt_const ν (2 : ℝ)).sub (hasDerivAt_pow 2 ν)).const_mul (2 : ℝ)
    simpa using this
  have hq2 : (2 : ℝ) * (2 - ν ^ 2) ≠ 0 := by positivity
  have hfrac := (hasDerivAt_id ν).div hd hq2
  have hlp : HasDerivAt (fun x : ℝ => Real.log (√2 + x)) (1 / (√2 + ν)) ν := by
    have := ((hasDerivAt_const ν (√2 : ℝ)).add (hasDerivAt_id ν)).log hp.ne'
    simpa using this
  have hlm : HasDerivAt (fun x : ℝ => Real.log (√2 - x)) (-1 / (√2 - ν)) ν := by
    have := ((hasDerivAt_const ν (√2 : ℝ)).sub (hasDerivAt_id ν)).log hm.ne'
    simpa using this
  have hall := hfrac.sub ((hlp.sub hlm).div_const (4 * √2))
  unfold areaPrimitive areaDensity
  have hpm : (√2 + ν) * (√2 - ν) = 2 - ν ^ 2 := by nlinarith [hs2]
  have key : 1 / (√2 + ν) - -1 / (√2 - ν) = 2 * √2 / (2 - ν ^ 2) := by
    rw [← hpm]
    field_simp
    ring
  convert hall using 1
  · funext x
    simp only [Pi.sub_apply, Pi.div_apply, id]
  rw [key]
  simp only [id]
  field_simp
  ring

/-- The integrand is continuous on the lobe chart, hence interval integrable. -/
theorem areaDensity_intervalIntegrable :
    IntervalIntegrable areaDensity volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  obtain ⟨_, _, hq⟩ := chart_factors_pos hx.1 hx.2
  unfold areaDensity
  exact ((continuous_pow 2).continuousAt.div
    ((continuous_const.sub (continuous_pow 2)).pow 2).continuousAt
    (pow_ne_zero 2 hq.ne')).continuousWithinAt

theorem areaPrimitive_zero : areaPrimitive 0 = 0 := by
  simp [areaPrimitive]

/-- `log(√2 − 1) = −log(1 + √2)`, since `(√2 − 1)(√2 + 1) = 1`. -/
theorem log_sqrt_two_sub_one : Real.log (√2 - 1) = -Real.log (1 + √2) := by
  have hs := one_lt_sqrt2
  have hs2 := sqrt2_sq
  have hprod : (√2 - 1) * (1 + √2) = 1 := by nlinarith
  have h := Real.log_mul (by linarith : (√2 - 1 : ℝ) ≠ 0) (by linarith : (1 + √2 : ℝ) ≠ 0)
  rw [hprod, Real.log_one] at h
  linarith

theorem areaPrimitive_one :
    areaPrimitive 1 = 1 / 2 - Real.log (1 + √2) / (2 * √2) := by
  have hs0 : (√2 : ℝ) ≠ 0 := sqrt2_pos.ne'
  have hs2 := sqrt2_sq
  unfold areaPrimitive
  rw [log_sqrt_two_sub_one, add_comm (√2 : ℝ) 1]
  field_simp
  ring

/-- `∫₀¹ ν² / (2 − ν²)² dν = 1/2 − log(1 + √2) / (2√2)`. -/
theorem areaDensity_integral :
    ∫ ν in (0 : ℝ)..1, areaDensity ν = 1 / 2 - Real.log (1 + √2) / (2 * √2) := by
  rw [integral_eq_sub_of_hasDerivAt (f := areaPrimitive) (fun x hx => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact hasDerivAt_areaPrimitive hx.1 hx.2) areaDensity_intervalIntegrable,
    areaPrimitive_one, areaPrimitive_zero, sub_zero]

/-- `m17-area-integration`, analytic step:
`2π ∫₀¹ ν² / (2 − ν²)² dν = π (1 − log(1 + √2) / √2)`. -/
theorem area_integration :
    2 * π * ∫ ν in (0 : ℝ)..1, ν ^ 2 / (2 - ν ^ 2) ^ 2 =
      π * (1 - Real.log (1 + √2) / √2) := by
  have h := areaDensity_integral
  unfold areaDensity at h
  rw [h]
  have hs0 : (√2 : ℝ) ≠ 0 := sqrt2_pos.ne'
  field_simp

/-- `log(1 + √2) / √2 < 1`, from `log y < y − 1` for `y ≠ 1`. -/
theorem log_one_add_sqrt_two_div_lt_one : Real.log (1 + √2) / √2 < 1 := by
  have hs := one_lt_sqrt2
  have h := Real.log_lt_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + √2) (by linarith)
  rw [div_lt_one sqrt2_pos]
  linarith

/-- The value is strictly positive: `0 < π (1 − log(1 + √2) / √2)`. -/
theorem area_value_pos : 0 < π * (1 - Real.log (1 + √2) / √2) := by
  have := log_one_add_sqrt_two_div_lt_one
  have := Real.pi_pos
  nlinarith

#print axioms sqrt2_sq
#print axioms one_lt_sqrt2
#print axioms sqrt2_pos
#print axioms areaPrimitive_zero
#print axioms chart_factors_pos
#print axioms hasDerivAt_areaPrimitive
#print axioms areaDensity_intervalIntegrable
#print axioms log_sqrt_two_sub_one
#print axioms areaPrimitive_one
#print axioms areaDensity_integral
#print axioms area_integration
#print axioms log_one_add_sqrt_two_div_lt_one
#print axioms area_value_pos

end EulerianCert.CassiniAreaIntegral20261124
