import EulerianGrothendieck.ThirteenthDefinitions
noncomputable section
open scoped BigOperators
open Finset Polynomial MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck.Order13
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096
theorem norm_coefficient_13 : normB 13 =
    ∑ q ∈ range 27, qFallingCoeff 13 q*nbFactorial q := by
  norm_num [normB, qFallingCoeff, nbFactorial, Finset.sum_range_succ, Nat.factorial]

theorem reciprocal_coefficient_13 : (∑ j ∈ range 14, normB j*vacuumD (13-j)) = 0 := by
  norm_num [normB, vacuumD, EulerianGrothendieck.normB, EulerianGrothendieck.vacuumD,
    Finset.sum_range_succ]

end EulerianGrothendieck.Order13
