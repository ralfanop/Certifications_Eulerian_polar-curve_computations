import Mathlib

/-!
Manuscript 11, revision 2026-11-25, Proposition 3.17, p. 28.
Actual centred uniform law represented by its unit-density interval integral.
Candidate first tranche: real MGF, removable value, moments and algebraic jet.
The analytic O(h^6) remainder and identification with the analytic log derivative
are separate obligations; the formal polynomial identity alone does not prove them.
-/
open Real MeasureTheory Set intervalIntegral
noncomputable section

namespace EulerianCert.M11StandardizedCumulant

def mgf (h : ℝ) : ℝ :=
  ∫ u in (-1 / 2 : ℝ)..(1 / 2), Real.exp (Real.sqrt 12 * h * u)

def moment (n : ℕ) : ℝ :=
  ∫ u in (-1 / 2 : ℝ)..(1 / 2), (Real.sqrt 12 * u) ^ n

lemma sqrt12_eq : Real.sqrt 12 = 2 * Real.sqrt 3 := by
  rw [show (12 : ℝ) = 4 * 3 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem mgf_zero : mgf 0 = 1 := by
  norm_num [mgf]

/-- The closed form away from the removable singularity, Eq. (116). -/
theorem mgf_eq_sinh (h : ℝ) (hh : h ≠ 0) :
    mgf h = Real.sinh (Real.sqrt 3 * h) / (Real.sqrt 3 * h) := by
  let c : ℝ := Real.sqrt 12 * h
  have hc : c ≠ 0 := mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) hh
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (c * y) / c)
      (Real.exp (c * x)) x := by
    intro x
    have hd := ((Real.hasDerivAt_exp (c * x)).comp x
      ((hasDerivAt_id x).const_mul c)).div_const c
    have hcancel : Real.exp (c * x) * (c * 1) / c = Real.exp (c * x) := by
      rw [mul_one, mul_div_cancel_right₀ _ hc]
    rw [hcancel] at hd
    exact hd
  have he : (∫ x in (-1 / 2 : ℝ)..(1 / 2), Real.exp (c * x)) =
      Real.exp (c * (1 / 2)) / c - Real.exp (c * (-1 / 2)) / c := by
    rw [intervalIntegral.integral_deriv_eq_sub' _ (funext fun x => (D x).deriv)
      (fun x _ => (D x).differentiableAt)]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hc' : c = 2 * (Real.sqrt 3 * h) := by
    simp [c, sqrt12_eq]
    ring
  change (∫ x in (-1 / 2 : ℝ)..(1 / 2), Real.exp (c * x)) = _
  rw [he, hc', Real.sinh_eq]
  rw [show 2 * (Real.sqrt 3 * h) * (1 / 2) = Real.sqrt 3 * h by ring,
      show 2 * (Real.sqrt 3 * h) * (-1 / 2) = -(Real.sqrt 3 * h) by ring]
  have hz : Real.sqrt 3 * h ≠ 0 := mul_ne_zero
    (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) hh
  field_simp

/-- Joint total version of (116) and (117); division by zero in Lean is not the extension. -/
theorem mgf_eq_total (h : ℝ) :
    mgf h = if h = 0 then 1 else Real.sinh (Real.sqrt 3 * h) / (Real.sqrt 3 * h) := by
  by_cases hh : h = 0
  · subst h
    simp [mgf_zero]
  · simpa [hh] using mgf_eq_sinh h hh

theorem moment_eq (n : ℕ) : moment n =
    (Real.sqrt 12) ^ n * (((1 / 2 : ℝ) ^ (n + 1) -
      (-1 / 2 : ℝ) ^ (n + 1)) / ((n : ℝ) + 1)) := by
  unfold moment
  simp only [mul_pow]
  rw [intervalIntegral.integral_const_mul, integral_pow]

theorem moment_one : moment 1 = 0 := by
  rw [moment_eq]
  norm_num

theorem moment_two : moment 2 = 1 := by
  rw [moment_eq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  norm_num

theorem moment_four : moment 4 = 9 / 5 := by
  have hs : (Real.sqrt 12) ^ 4 = 144 := by
    calc
      (Real.sqrt 12) ^ 4 = ((Real.sqrt 12) ^ 2) ^ 2 := by ring
      _ = 144 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]; norm_num
  rw [moment_eq, hs]
  norm_num

/-- Eq. (119), through the actual centered standardized moments.
    The identification with the fourth derivative of log mgf is not yet claimed. -/
theorem fourth_centered_cumulant : moment 4 - 3 * (moment 2) ^ 2 = -6 / 5 := by
  rw [moment_four, moment_two]
  norm_num

/-- Algebraic precursor for (118), not an analytic remainder estimate. -/
theorem quartic_log_jet (h : ℝ) :
    (h ^ 2 / 2 + 3 * h ^ 4 / 40) - (h ^ 2 / 2) ^ 2 / 2 =
    h ^ 2 / 2 - h ^ 4 / 20 := by ring

theorem fourth_log_coefficient : (Nat.factorial 4 : ℝ) * (-1 / 20) = -6 / 5 := by
  norm_num [Nat.factorial]

#print axioms EulerianCert.M11StandardizedCumulant.mgf_zero
#print axioms EulerianCert.M11StandardizedCumulant.mgf_eq_sinh
#print axioms EulerianCert.M11StandardizedCumulant.mgf_eq_total
#print axioms EulerianCert.M11StandardizedCumulant.moment_eq
#print axioms EulerianCert.M11StandardizedCumulant.moment_one
#print axioms EulerianCert.M11StandardizedCumulant.moment_two
#print axioms EulerianCert.M11StandardizedCumulant.moment_four
#print axioms EulerianCert.M11StandardizedCumulant.fourth_centered_cumulant
#print axioms EulerianCert.M11StandardizedCumulant.quartic_log_jet
#print axioms EulerianCert.M11StandardizedCumulant.fourth_log_coefficient

end EulerianCert.M11StandardizedCumulant
