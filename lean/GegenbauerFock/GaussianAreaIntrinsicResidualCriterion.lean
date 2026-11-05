import GegenbauerFock.GaussianAreaCoherentIntrinsicAgreement
import GegenbauerFock.GaussianAreaPolynomialProjector

/-!
# V007 — intrinsic Gaussian holomorphic residual and exact density criterion

This module isolates the remaining analytic obstruction to the ONTO
Bargmann–Fock isometry. Every intrinsic entire Gaussian L² class splits
into its coherent polynomial projection and an *intrinsic entire*
orthogonal residual. The residual has zero Gaussian monomial moments.

Consequently polynomial density in the independently defined entire
Gaussian L² space is EQUIVALENT to uniqueness of an intrinsic entire
Gaussian L² vector with all Gaussian moments zero. The latter uniqueness
is an analytic obligation, NOT proved or assumed here. These theorems
do not assert full surjectivity.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The residual of the canonical Gaussian polynomial projection of
an entire-representative L² vector still has an entire representative. -/
theorem intrinsicResidual_mem_entireGaussianL2Submodule
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha))
    (hx : x ∈ entireGaussianL2Submodule alpha) :
    x - gaussianPolynomialProjector alpha ha x ∈
      entireGaussianL2Submodule alpha := by
  exact (entireGaussianL2Submodule alpha).sub_mem hx
    (gaussianPolynomialClosure_le_entireGaussianL2Submodule alpha ha
      (gaussianPolynomialProjector_mem_closure alpha ha x))

/-- Every intrinsic entire Gaussian L² vector admits a decomposition
into its synthesized polynomial projection and an intrinsic entire
residual whose full coefficient-analysis sequence vanishes. -/
theorem intrinsicResidual_analysis_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    coefficientAnalysisL2 alpha ha
      (x - gaussianPolynomialProjector alpha ha x) = 0 := by
  exact (coefficientAnalysisL2_eq_zero_iff_orthogonal alpha ha _).2
    (gaussianPolynomialProjector_residual_orthogonal alpha ha x)

/-- Full polynomial density in the INDEPENDENTLY defined entire
Gaussian L² submodule is equivalent to injectivity of Gaussian
coefficient analysis when restricted to that submodule.

The equivalence is unconditional; it does NOT establish either side.
-/
theorem intrinsicEntire_le_polynomialClosure_iff_analysis_unique
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha ≤ gaussianPolynomialClosure alpha ha ↔
      ∀ x : Lp ℂ 2 (gaussianAreaMeasure alpha),
        x ∈ entireGaussianL2Submodule alpha →
        coefficientAnalysisL2 alpha ha x = 0 → x = 0 := by
  constructor
  · intro h x hx hzero
    have hspan : x ∈ gaussianPolynomialClosure alpha ha := h hx
    have horth : x ∈ (gaussianPolynomialClosure alpha ha)ᗮ :=
      (coefficientAnalysisL2_eq_zero_iff_orthogonal alpha ha x).1 hzero
    have hbot :
        x ∈ (⊥ : Submodule ℂ (Lp ℂ 2 (gaussianAreaMeasure alpha))) := by
      have hboth :
          x ∈ (gaussianPolynomialClosure alpha ha) ⊓
            (gaussianPolynomialClosure alpha ha)ᗮ := ⟨hspan, horth⟩
      simpa only [(gaussianPolynomialClosure alpha ha).inf_orthogonal_eq_bot]
        using hboth
    exact (Submodule.mem_bot ℂ).1 hbot
  · intro h x hx
    have hres : x - gaussianPolynomialProjector alpha ha x ∈
        entireGaussianL2Submodule alpha :=
      intrinsicResidual_mem_entireGaussianL2Submodule alpha ha x hx
    have hzero : x - gaussianPolynomialProjector alpha ha x = 0 :=
      h _ hres (intrinsicResidual_analysis_zero alpha ha x)
    have hfixed : gaussianPolynomialProjector alpha ha x = x :=
      (sub_eq_zero.mp hzero).symm
    exact (gaussianPolynomialProjector_eq_self_iff alpha ha x).1 hfixed

/-- Equivalent analytic form: the onto problem is exactly uniqueness
of entire Gaussian L² classes from all normalized holomorphic moments.
No moment-uniqueness hypothesis is smuggled into the proof. -/
theorem intrinsicEntire_le_polynomialClosure_iff_moment_unique
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha ≤ gaussianPolynomialClosure alpha ha ↔
      ∀ x : Lp ℂ 2 (gaussianAreaMeasure alpha),
        x ∈ entireGaussianL2Submodule alpha →
        (∀ n : ℕ,
          inner ℂ (normalizedMonomialL2Vector alpha ha n) x = 0) →
        x = 0 := by
  rw [intrinsicEntire_le_polynomialClosure_iff_analysis_unique alpha ha]
  constructor
  · intro h x hx hm
    exact h x hx ((coefficientAnalysisL2_eq_zero_iff alpha ha x).2 hm)
  · intro h x hx hz
    exact h x hx ((coefficientAnalysisL2_eq_zero_iff alpha ha x).1 hz)

#print axioms GegenbauerFock.GaussianArea.intrinsicResidual_mem_entireGaussianL2Submodule
#print axioms GegenbauerFock.GaussianArea.intrinsicResidual_analysis_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_le_polynomialClosure_iff_analysis_unique
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_le_polynomialClosure_iff_moment_unique

end GegenbauerFock.GaussianArea
