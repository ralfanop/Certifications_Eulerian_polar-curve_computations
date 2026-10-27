import GegenbauerFock.GeneralUltrasphericalFock
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# V007: continuous-function density for the actual ultraspherical probability

The ultraspherical measure ν_λ is a finite Borel measure on the real
line, hence weakly regular. Pinned Mathlib's continuous-function
density theorem therefore applies directly to the *same* weighted
L²(ν_λ) source used by the Gegenbauer--Fock analysis operator.

This establishes the first analytic density stage. The second stage,
uniform polynomial approximation on the compact support and
identification of its L² monomials, remains a separate obligation.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open MeasureTheory

/-- The actual ultraspherical probability measure is weakly regular,
so bounded continuous functions approximate arbitrary L² vectors. -/
theorem measure_weaklyRegular (lam : ℝ) (hlam : 0 < lam) :
    Measure.WeaklyRegular (measure lam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  infer_instance

/-- Every L²(ν_λ) function with complex values can be approximated
in the true L² norm by bounded continuous functions on the real line.
No finite-dimensional or auxiliary Gaussian target is substituted. -/
theorem boundedContinuous_toLp_denseRange
    (lam : ℝ) (hlam : 0 < lam) :
    DenseRange
      (BoundedContinuousFunction.toLp
        (E := ℂ) (p := 2) (measure lam) ℂ :
        (ℝ →ᵇ ℂ) →L[ℂ] Lp ℂ 2 (measure lam)) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  letI : Measure.WeaklyRegular (measure lam) :=
    measure_weaklyRegular lam hlam
  exact BoundedContinuousFunction.toLp_denseRange
    ℂ (measure lam) ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

#print axioms GegenbauerFock.Ultraspherical.measure_weaklyRegular
#print axioms GegenbauerFock.Ultraspherical.boundedContinuous_toLp_denseRange

end GegenbauerFock.Ultraspherical
