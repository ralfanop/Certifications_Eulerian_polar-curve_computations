import GegenbauerFock.ConcreteFockOperator
import GegenbauerFock.UltrasphericalMeasure

/-!
# V007: specific general-parameter ultraspherical -> infinite Fock coefficient operator

This SPECIALIZES the fully bounded Hilbert operator (ConcreteFockOperator)
to the explicitly constructed symmetric Beta-pushforward ultraspherical
probability law. Parameters λ>0, α>0 are genuine hypotheses.

The resulting operator is a continuous complex-linear map
L²(ν_λ) -> ℓ²(ℕ;ℂ), with explicitly verified factorial-weighted
monomial Fourier coefficients and its genuine Hilbert adjoint.

This is NOT yet an isometric realization as Gaussian holomorphic
Fock functions; the Hilbert–Schmidt integral trace identity and
compactness still require independent certified analytic arguments.
-/

open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The concrete Beta-pushforward ultraspherical measure is supported
in the unit interval for every λ (normalization requires λ>0). -/
theorem ae_abs_le_one (lam : ℝ) :
    ∀ᵐ u ∂Ultraspherical.measure lam, |u| ≤ 1 := by
  filter_upwards [Ultraspherical.ae_mem_unit_interval lam] with u hu
  exact abs_le.mpr ⟨hu.1, hu.2⟩

/-- Concrete and genuinely bounded Hilbert operator from ultraspherical
L² to the infinite Gaussian-Fock coefficient Hilbert space ℓ². -/
noncomputable def C (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      InfiniteAnalysis.FockCoefficients := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  exact ConcreteFock.operator (Ultraspherical.measure lam)
    (ae_abs_le_one lam) alpha ha

/-- Every coefficient agrees with the exact weighted Riesz monomial
functional on the concrete general-λ ultraspherical L² measure. -/
theorem C_coefficient (lam alpha : ℝ) (hlam : 0 < lam)
    (ha : 0 < alpha) (f : Lp ℂ 2 (Ultraspherical.measure lam)) (n : ℕ) :
    C lam alpha hlam ha f n =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      WeightedMoments.coefficient
        (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n f := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  change (ConcreteFock.operator (Ultraspherical.measure lam)
    (ae_abs_le_one lam) alpha ha) f n =
    WeightedMoments.coefficient (Ultraspherical.measure lam)
      (ae_abs_le_one lam) alpha n f
  exact ConcreteFock.operator_coefficient
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha f n

/-- Genuine adjoint of the fully specified ultraspherical Hilbert map. -/
noncomputable def C_adjoint (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    InfiniteAnalysis.FockCoefficients →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) :=
  (C lam alpha hlam ha).adjoint

/-- Certified defining Hilbert-adjoint identity. -/
theorem C_adjoint_pairing (lam alpha : ℝ) (hlam : 0 < lam)
    (ha : 0 < alpha) (F : InfiniteAnalysis.FockCoefficients)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    inner ℂ (C_adjoint lam alpha hlam ha F) f =
      inner ℂ F (C lam alpha hlam ha f) :=
  (C lam alpha hlam ha).adjoint_inner_left f F

/-- Concrete Gram C†C, selfadjoint and positive by construction. -/
noncomputable def gram (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) :=
  HilbertGram.gram (C lam alpha hlam ha)

theorem gram_selfadjoint (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (gram lam alpha hlam ha).adjoint = gram lam alpha hlam ha :=
  HilbertGram.gram_adjoint (C lam alpha hlam ha)

theorem gram_positive (lam alpha : ℝ) (hlam : 0 < lam)
    (ha : 0 < alpha) (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    0 ≤ RCLike.re (inner ℂ (gram lam alpha hlam ha f) f) :=
  HilbertGram.gram_re_nonneg (C lam alpha hlam ha) f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ae_abs_le_one
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_coefficient
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_pairing
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_selfadjoint
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_positive

end GegenbauerFock.GeneralUltrasphericalFock
