import GegenbauerFock.GaussianAreaRadialGammaMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# V007 — radial integration of genuine entire circular Taylor moments

The circle-average Cauchy identity and the exact radial Gamma integral
combine into an unconditional formula for the radially integrated
angular moments of any entire complex function. This is an actual
Bochner integral on the positive real ray, not a formal coefficient
functional. Identifying this iterated integral with the genuine planar
Gaussian monomial moment via polar Fubini remains a separate obligation.
-/

noncomputable section

open Complex MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The weighted radial integral of the genuine circle average extracts
the nth Taylor coefficient with the exact Gaussian Gamma factor. -/
theorem integral_radial_circleAverage_eq_taylorCoeff
    (alpha : ℝ) (ha : 0 < alpha)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (n : ℕ) :
    (∫ r in Set.Ioi (0 : ℝ),
      ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
        Real.circleAverage
          (fun z : ℂ => f z * star (z ^ n)) 0 r) =
      ((alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
        (Nat.factorial n : ℝ) : ℝ) : ℂ) *
        (iteratedDeriv n f 0 / (Nat.factorial n : ℂ)) := by
  let c : ℂ := iteratedDeriv n f 0 / (Nat.factorial n : ℂ)
  have hpoint (r : ℝ) (hr : 0 < r) :
      ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
        Real.circleAverage
          (fun z : ℂ => f z * star (z ^ n)) 0 r =
      ((r ^ (2 * n + 1) * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) * c := by
    rw [entire_circleAverage_conj_monomial_eq_taylorCoeff f hf r hr n]
    change ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
      (((r ^ (2 * n) : ℝ) : ℂ) * c) = _
    rw [show 2 * n + 1 = 2 * n + 1 by omega, pow_succ]
    push_cast
    ring
  calc
    (∫ r in Set.Ioi (0 : ℝ),
      ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
        Real.circleAverage
          (fun z : ℂ => f z * star (z ^ n)) 0 r) =
      (∫ r in Set.Ioi (0 : ℝ),
        ((r ^ (2 * n + 1) * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) * c) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        exact hpoint r hr
    _ = (((∫ r in Set.Ioi (0 : ℝ),
        (r ^ (2 * n + 1) * Real.exp (-alpha * r ^ 2) : ℝ)) : ℝ) : ℂ) * c := by
        rw [integral_mul_const]
        congr 1
        simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using
          (integral_complex_ofReal
            (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
            (f := fun r : ℝ =>
              r ^ (2 * n + 1) * Real.exp (-alpha * r ^ 2)))
    _ = ((alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
        (Nat.factorial n : ℝ) : ℝ) : ℂ) *
        (iteratedDeriv n f 0 / (Nat.factorial n : ℂ)) := by
        rw [integral_radial_gaussian_even_power alpha ha n]
        rfl

#print axioms GegenbauerFock.GaussianArea.integral_radial_circleAverage_eq_taylorCoeff

end GegenbauerFock.GaussianArea
