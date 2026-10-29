import GegenbauerFock.GaussianAreaEntireRadialInner
import GegenbauerFock.GaussianAreaRadialCircleMomentUniqueness
import GegenbauerFock.GaussianAreaIntrinsicResidualCriterion
import GegenbauerFock.GaussianAreaEntireMomentInner

/-!
# V007 — intrinsic Gaussian entire completeness from radial L² coefficients

This independent proof of polynomial density avoids extracting the
polar scalar from nested circle averages. The genuine Hilbert-space
monomial inner product is already the Gaussian radial-circle integral,
and the scalar weights are nonzero. Thus a zero coefficient-analysis
sequence forces all Taylor derivatives to vanish.

No polynomial-density or onto assumption occurs in the proof.
The result must pass an exact-head Lean compilation and axiom audit
before it is reported as a kernel certificate.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- For any intrinsic entire Gaussian L² vector, vanishing of the
genuine Hilbert-space coefficient analysis forces the zero vector. -/
theorem intrinsicEntire_analysis_injective_via_radial_inner
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha)
    (hz : coefficientAnalysisL2 alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) = 0) :
    x = 0 := by
  apply intrinsicGaussian_zero_of_radial_circleMoments_zero alpha ha x
  intro n
  have hcoeff :
      inner ℂ (normalizedMonomialL2Vector alpha ha n)
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) = 0 :=
    (coefficientAnalysisL2_eq_zero_iff alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha))).1 hz n
  rw [normalizedMonomial_inner_eq_radial_circleAverage alpha ha x n] at hcoeff
  have hrad :
      (2 * alpha) •
        (∫ r in Set.Ioi (0 : ℝ),
          (r * Real.exp (-alpha * r ^ 2)) •
            Real.circleAverage
              (fun z : ℂ => entireRepresentative alpha x z * star (z ^ n))
              0 r) = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_left (monomialWeight_ne_zero alpha ha n)
  have htwo : ((2 * alpha : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ha))
  have hrad' :
      (∫ r in Set.Ioi (0 : ℝ),
        (r * Real.exp (-alpha * r ^ 2)) •
          Real.circleAverage
            (fun z : ℂ => entireRepresentative alpha x z * star (z ^ n))
            0 r) = 0 := by
    simp only [Complex.real_smul] at hrad
    exact (mul_eq_zero.mp hrad).resolve_left htwo
  simpa only [Complex.real_smul] using hrad'

/-- The independent holomorphic Gaussian L² submodule is contained
in the closed complex span of the genuine normalized monomials. -/
theorem intrinsicEntire_le_polynomialClosure_via_radial_inner
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha ≤ gaussianPolynomialClosure alpha ha := by
  apply (intrinsicEntire_le_polynomialClosure_iff_analysis_unique alpha ha).2
  intro x hx hz
  have hy : (⟨x, hx⟩ : entireGaussianL2Submodule alpha) = 0 :=
    intrinsicEntire_analysis_injective_via_radial_inner alpha ha ⟨x, hx⟩ hz
  exact congrArg Subtype.val hy

/-- Full equality of the intrinsically defined holomorphic Gaussian L²
space and the closed polynomial Hilbert subspace. -/
theorem intrinsicEntire_eq_polynomialClosure_via_radial_inner
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha = gaussianPolynomialClosure alpha ha := by
  apply le_antisymm
  · exact intrinsicEntire_le_polynomialClosure_via_radial_inner alpha ha
  · exact gaussianPolynomialClosure_le_entireGaussianL2Submodule alpha ha

#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_analysis_injective_via_radial_inner
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_le_polynomialClosure_via_radial_inner
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_eq_polynomialClosure_via_radial_inner

end GegenbauerFock.GaussianArea
