import GegenbauerFock.GaussianAreaRadialCircleTaylor

/-!
# V007 — uniqueness from genuine radially integrated circle moments

The previously certified radial-circle Taylor identity has a strictly
positive Gamma coefficient. Therefore its zero moments imply vanishing
Taylor derivatives, and all such moments separate entire Gaussian L²
representatives.

This is a statement about *iterated radial-circle integrals*. It does
not yet identify them with genuine planar Gaussian monomial moments;
the polar Fubini step remains a separate obligation.
-/

noncomputable section

open Complex MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The actual radial-circle Gaussian moment at degree n vanishes only
if the nth complex Taylor derivative of an entire function vanishes. -/
theorem iteratedDeriv_zero_of_radial_circleAverage_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (n : ℕ)
    (hz :
      (∫ r in Set.Ioi (0 : ℝ),
        ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
          Real.circleAverage
            (fun z : ℂ => f z * star (z ^ n)) 0 r) = 0) :
    iteratedDeriv n f 0 = 0 := by
  have hfacpos :
      0 < alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
        (Nat.factorial n : ℝ) := by
    have hp : 0 < alpha ^ (-((n : ℝ) + 1)) :=
      Real.rpow_pos_of_pos ha _
    have hn : 0 < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    exact mul_pos (mul_pos hp (by norm_num)) hn
  have hfac :
      (((alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
        (Nat.factorial n : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hfacpos.ne'
  have hfact : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hmul :
      ((alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
        (Nat.factorial n : ℝ) : ℝ) : ℂ) *
        (iteratedDeriv n f 0 / (Nat.factorial n : ℂ)) = 0 := by
    rw [← integral_radial_circleAverage_eq_taylorCoeff alpha ha f hf n]
    exact hz
  have hdiv :
      iteratedDeriv n f 0 / (Nat.factorial n : ℂ) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hfac
  have hnum :
      iteratedDeriv n f 0 * (Nat.factorial n : ℂ)⁻¹ = 0 := by
    simpa only [div_eq_mul_inv] using hdiv
  exact (mul_eq_zero.mp hnum).resolve_right (inv_ne_zero hfact)

/-- All genuine radial-circle moments determine an intrinsic entire
Gaussian L² class uniquely. This does not assume polynomial density. -/
theorem intrinsicGaussian_zero_of_radial_circleMoments_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha)
    (hz : ∀ n : ℕ,
      (∫ r in Set.Ioi (0 : ℝ),
        ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
          Real.circleAverage
            (fun z : ℂ =>
              entireRepresentative alpha x z * star (z ^ n)) 0 r) = 0) :
    x = 0 := by
  apply (intrinsicGaussian_zero_iff_taylor_derivs_zero alpha ha x).2
  intro n
  exact iteratedDeriv_zero_of_radial_circleAverage_zero alpha ha
    (entireRepresentative alpha x)
    (entireRepresentative_differentiable alpha x) n (hz n)

#print axioms GegenbauerFock.GaussianArea.iteratedDeriv_zero_of_radial_circleAverage_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicGaussian_zero_of_radial_circleMoments_zero

end GegenbauerFock.GaussianArea
