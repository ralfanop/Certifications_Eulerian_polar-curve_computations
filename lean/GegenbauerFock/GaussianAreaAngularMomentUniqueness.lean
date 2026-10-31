import GegenbauerFock.GaussianAreaEntireAngularMoments

/-!
# V007 — uniqueness from genuine angular Gaussian monomial moments

At any fixed positive radius, the full sequence of normalized circle
averages against conjugate monomials separates entire functions.
This combines the previously certified Cauchy angular extraction
identity with the global Taylor uniqueness theorem.

The corresponding area-weighted Gaussian moments still require the
radial Fubini/integration bridge; this file makes no assertion about
that bridge or full onto Bargmann–Fock surjectivity.
-/

noncomputable section

open Complex MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- If one angular conjugate-monomial moment vanishes at a positive
radius, the corresponding Taylor derivative vanishes. -/
theorem entire_iteratedDeriv_zero_of_circleAverage_conj_monomial_zero
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (R : ℝ) (hR : 0 < R) (n : ℕ)
    (h : Real.circleAverage
      (fun z : ℂ => f z * star (z ^ n)) 0 R = 0) :
    iteratedDeriv n f 0 = 0 := by
  have hRne : ((R ^ (2 * n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero (2 * n) (ne_of_gt hR))
  have hfact : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hprod :
      ((R ^ (2 * n) : ℝ) : ℂ) *
        (iteratedDeriv n f 0 / (Nat.factorial n : ℂ)) = 0 := by
    simpa only [entire_circleAverage_conj_monomial_eq_taylorCoeff
      f hf R hR n] using h
  by_contra hn
  exact (mul_ne_zero hRne (div_ne_zero hn hfact)) hprod

/-- An entire function is determined by all its genuine angular
conjugate-monomial moments on *one* circle of positive radius. -/
theorem entireFunction_eq_zero_of_all_circleAverage_conj_monomial_zero
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (R : ℝ) (hR : 0 < R)
    (h : ∀ n : ℕ,
      Real.circleAverage (fun z : ℂ => f z * star (z ^ n)) 0 R = 0) :
    f = 0 := by
  apply entireFunction_eq_zero_of_iteratedDeriv_zero f hf
  intro n
  exact entire_iteratedDeriv_zero_of_circleAverage_conj_monomial_zero
    f hf R hR n (h n)

/-- For every positive radius, angular moments separate points of the
independently defined intrinsic Gaussian holomorphic L² submodule. -/
theorem intrinsicGaussian_eq_zero_of_all_circleAverage_conj_monomial_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha)
    (R : ℝ) (hR : 0 < R)
    (h : ∀ n : ℕ,
      Real.circleAverage
        (fun z : ℂ =>
          entireRepresentative alpha x z * star (z ^ n)) 0 R = 0) :
    x = 0 := by
  apply (intrinsicGaussian_zero_iff_taylor_derivs_zero alpha ha x).2
  intro n
  exact entire_iteratedDeriv_zero_of_circleAverage_conj_monomial_zero
    (entireRepresentative alpha x)
    (entireRepresentative_differentiable alpha x) R hR n (h n)

#print axioms GegenbauerFock.GaussianArea.entire_iteratedDeriv_zero_of_circleAverage_conj_monomial_zero
#print axioms GegenbauerFock.GaussianArea.entireFunction_eq_zero_of_all_circleAverage_conj_monomial_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicGaussian_eq_zero_of_all_circleAverage_conj_monomial_zero

end GegenbauerFock.GaussianArea
