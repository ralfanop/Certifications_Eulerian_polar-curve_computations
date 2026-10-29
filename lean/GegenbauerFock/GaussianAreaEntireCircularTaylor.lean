import GegenbauerFock.GaussianAreaEntireCircleMean

/-!
# V007 — exact Taylor coefficient extraction by a genuine circle average

For every entire complex function, the normalized angular average of
f(z)/(z-c)^n over any circle centered at c recovers the nth Taylor
coefficient. This is a genuine Cauchy-integral statement, not a
formal power-series manipulation or an assumed Gaussian moment identity.

The remaining Gaussian Fock density problem requires connecting these
circle coefficients to the *area-weighted* Gaussian monomial moments.
That radial integration and its analytic justification are not claimed.
-/

noncomputable section

open Complex MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- A true circular integral extracts the Taylor coefficient
f⁽ⁿ⁾(c)/n! of any entire function. -/
theorem entire_circleAverage_div_pow_eq_taylorCoeff
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (c : ℂ) (R : ℝ) (hR : 0 < R) (n : ℕ) :
    Real.circleAverage (fun z : ℂ => f z / (z - c) ^ n) c R =
      iteratedDeriv n f c / (Nat.factorial n : ℂ) := by
  have hCauchy :
      (∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z) =
        (2 * Real.pi * Complex.I / (Nat.factorial n : ℂ)) •
          iteratedDeriv n f c :=
    (hf.differentiableOn (s := Metric.closedBall c R)).circleIntegral_one_div_sub_center_pow_smul hR n
  have hkernel :
      (∮ z in C(c, R), (z - c)⁻¹ • (f z / (z - c) ^ n)) =
        (∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    simp [smul_eq_mul, div_eq_mul_inv, pow_succ,
      mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  rw [Real.circleAverage_eq_circleIntegral hR.ne', hkernel, hCauchy]
  simp only [smul_eq_mul]
  have hscalar : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hfact : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hscalar, hfact]

/-- Intrinsic Gaussian holomorphic Taylor coefficients are recovered
by genuine circular means at every positive radius. -/
theorem intrinsicEntire_circleAverage_div_pow_eq_taylorCoeff
    (alpha : ℝ) (x : entireGaussianL2Submodule alpha)
    (c : ℂ) (R : ℝ) (hR : 0 < R) (n : ℕ) :
    Real.circleAverage
        (fun z : ℂ => entireRepresentative alpha x z / (z - c) ^ n)
        c R =
      iteratedDeriv n (entireRepresentative alpha x) c /
        (Nat.factorial n : ℂ) := by
  exact entire_circleAverage_div_pow_eq_taylorCoeff
    (entireRepresentative alpha x)
    (entireRepresentative_differentiable alpha x) c R hR n

#print axioms GegenbauerFock.GaussianArea.entire_circleAverage_div_pow_eq_taylorCoeff
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_circleAverage_div_pow_eq_taylorCoeff

end GegenbauerFock.GaussianArea
