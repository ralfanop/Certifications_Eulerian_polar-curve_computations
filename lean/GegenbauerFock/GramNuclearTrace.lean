import GegenbauerFock.GramIntegralComplete
import GegenbauerFock.GramKernelSeries
import GegenbauerFock.RowEnergyExpIntegral

/-!
# V007: operator-norm summable nuclear Gram decomposition

A trace-class positive Gram operator can be presented as an absolutely
operator-norm-summable series of positive rank-one terms. The row
functionals are the genuine ultraspherical Fourier moments. This
module certifies absolute convergence of the rank-one operators,
not just convergence after applying to a fixed L² vector.

Note: identifying this constructive nuclear presentation with a
separately bundled Schatten S₁ API is a further formal bridge.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Each rank-one positive Gram summand of the genuine operator. -/
noncomputable def gramNuclearTerm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let r := WeightedMoments.coefficient
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n
  exact r.adjoint.comp r

/-- Operator-norm bound for each concrete positive rank-one term. -/
theorem gramNuclearTerm_norm_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    ‖gramNuclearTerm lam alpha hlam ha n‖ ≤
      WeightedMoments.squareWeight alpha n := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let r := WeightedMoments.coefficient
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n
  change ‖r.adjoint.comp r‖ ≤ _
  calc
    ‖r.adjoint.comp r‖ ≤ ‖r.adjoint‖ * ‖r‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖r‖ ^ 2 := by
      rw [show ‖r.adjoint‖ = ‖r‖ from
        ContinuousLinearMap.adjointAux_norm r]
      ring
    _ ≤ WeightedMoments.squareWeight alpha n :=
      WeightedMoments.coefficient_norm_sq_le
        (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha n

/-- The *actual* infinite family of positive rank-one Gram pieces
is absolutely summable in the full Banach operator norm. -/
theorem gramNuclearTerm_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Summable (gramNuclearTerm lam alpha hlam ha) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (gramNuclearTerm_norm_le lam alpha hlam ha)
    (WeightedMoments.squareWeight_summable alpha)

/-- Exact identity of the Gram map with the infinite positive
rank-one sum, now as an equality of *bounded operators*, not merely
as separate convergent vectors. -/
theorem gram_eq_nuclear_tsum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    gram lam alpha hlam ha =
      ∑' n : ℕ, gramNuclearTerm lam alpha hlam ha n := by
  apply ContinuousLinearMap.ext
  intro f
  rw [gram_eq_tsum_rows lam alpha hlam ha f]
  have hs := gramNuclearTerm_summable lam alpha hlam ha
  have heval :
      (∑' n : ℕ, gramNuclearTerm lam alpha hlam ha n) f =
        ∑' n : ℕ, gramNuclearTerm lam alpha hlam ha n f := by
    exact (ContinuousLinearMap.apply ℂ
      (Lp ℂ 2 (Ultraspherical.measure lam)) f).map_tsum hs
  rw [heval]
  apply tsum_congr
  intro n
  rfl

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearTerm_norm_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearTerm_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_eq_nuclear_tsum

end GegenbauerFock.GeneralUltrasphericalFock
