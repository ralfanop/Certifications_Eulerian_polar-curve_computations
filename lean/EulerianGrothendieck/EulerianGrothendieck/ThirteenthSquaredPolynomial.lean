import EulerianGrothendieck.ThirteenthDefinitions
noncomputable section
open scoped BigOperators
open Finset Polynomial MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck.Order13
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096
theorem squared_moment_polynomial_13 (x : ℚ) :
    (∑ j ∈ range 14, gPolynomial j x*gPolynomial (13-j) x) = qPolynomial 13 x := by
  norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, EulerianGrothendieck.pCoeff,
    EulerianGrothendieck.qFallingCoeff, fallingPoly, Finset.sum_range_succ]
  <;> ring

end EulerianGrothendieck.Order13
