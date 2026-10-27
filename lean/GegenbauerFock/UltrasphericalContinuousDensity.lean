import GegenbauerFock.GeneralUltrasphericalFock
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

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
open scoped ENNReal

/-- The actual ultraspherical probability measure is weakly regular,
so bounded continuous functions approximate arbitrary L² vectors. -/
theorem measure_weaklyRegular (lam : ℝ) (hlam : 0 < lam) :
    Measure.WeaklyRegular (measure lam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  infer_instance

/-- The bounded-continuous-to-L² operator for the *concrete*
ultraspherical probability measure. Constructing it with the certified
probability instance avoids an unfulfilled finite-measure instance in
the statement of its dense-range theorem. -/
noncomputable def boundedContinuousToLp
    (lam : ℝ) (hlam : 0 < lam) :
    BoundedContinuousFunction ℝ ℂ →L[ℂ] Lp ℂ 2 (measure lam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  exact BoundedContinuousFunction.toLp
    (2 : ℝ≥0∞) (measure lam) ℂ

/-- Bounded continuous complex functions have dense image under the
actual L²(ν_λ) embedding, for every λ>0; the finite-measure
hypothesis is discharged using the explicit Beta pushforward law. -/
theorem boundedContinuous_toLp_denseRange
    (lam : ℝ) (hlam : 0 < lam) :
    DenseRange (boundedContinuousToLp lam hlam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  letI : Measure.WeaklyRegular (measure lam) :=
    measure_weaklyRegular lam hlam
  change DenseRange
    (BoundedContinuousFunction.toLp
      (2 : ℝ≥0∞) (measure lam) ℂ :
      BoundedContinuousFunction ℝ ℂ →L[ℂ] Lp ℂ 2 (measure lam))
  exact BoundedContinuousFunction.toLp_denseRange
    ℂ (measure lam) ℂ (by norm_num)

/-- Real polynomial functions are uniformly dense among all
real-valued continuous functions on the *actual compact support*
[-1,1]. This is the Weierstrass stage of the L²-density argument.
The remaining transfer to complex-valued L² monomials is not
claimed by this theorem. -/
theorem polynomial_uniform_dense_on_unit_interval :
    (polynomialFunctions (Set.Icc (-1 : ℝ) 1)).topologicalClosure =
      ⊤ := by
  exact polynomialFunctions.topologicalClosure
    (Set.Icc (-1 : ℝ) 1)

#print axioms GegenbauerFock.Ultraspherical.measure_weaklyRegular
#print axioms GegenbauerFock.Ultraspherical.boundedContinuousToLp
#print axioms GegenbauerFock.Ultraspherical.boundedContinuous_toLp_denseRange
#print axioms GegenbauerFock.Ultraspherical.polynomial_uniform_dense_on_unit_interval

end GegenbauerFock.Ultraspherical
