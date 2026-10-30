import EulerianGrothendieck.ThirteenthDefinitions
noncomputable section
open scoped BigOperators
open Finset Polynomial MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck.Order13
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096
theorem exactMomentPolynomial_recurrence_13 (x : ℝ) :
    exactMomentPolynomial 13 (x+1) =
      ∑ j ∈ range 14, 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (13-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, EulerianGrothendieck.pCoeff,
    EulerianGrothendieck.cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

end EulerianGrothendieck.Order13
