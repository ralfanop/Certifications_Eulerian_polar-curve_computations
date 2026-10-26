import GegenbauerFock.ConcreteFockOperator

/-!
# V007: concrete Fock Hilbert–Schmidt row-energy identity

The codomain is the genuine infinite Hilbert space ℓ²(ℕ;ℂ).
Its canonical ONB permits the *row-energy* characterization of
Hilbert–Schmidt operators: sum over coordinate functionals of
their squared operator norms. We check the concrete operator's
summability and the exact factorially weighted monomial formula.

An independent kernel proof that this row-energy definition agrees
with a general Hilbert–Schmidt class norm, as well as its equality
to the confluent hypergeometric integral, remains to be completed.
-/

open MeasureTheory

namespace GegenbauerFock.FockEnergy

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))
variable (alpha : ℝ) (ha : 0 < alpha)

/-- The genuine coordinate functionals on the infinite ℓ² Hilbert target. -/
noncomputable def coordinate (n : ℕ) :
    InfiniteAnalysis.FockCoefficients →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n

/-- Square-summable rows characterize the HS property into ℓ². -/
def HasSummableRows (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients) : Prop :=
  Summable (fun n : ℕ => ‖(coordinate n).comp T‖ ^ 2)

/-- Exact row-energy series, evaluated in the canonical ℓ² coordinates. -/
noncomputable def squaredRowEnergy
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients) : ℝ :=
  ∑' n, ‖(coordinate n).comp T‖ ^ 2

include hsupport

/-- Identifies each actual Fourier-moment row of the bounded operator. -/
theorem coordinate_comp_operator (n : ℕ) :
    (coordinate n).comp (ConcreteFock.operator μ hsupport alpha ha) =
      WeightedMoments.coefficient μ hsupport alpha n := by
  apply ContinuousLinearMap.ext
  intro f
  exact ConcreteFock.operator_coefficient μ hsupport alpha ha f n

/-- The concrete operator has square-summable Hilbert coefficient rows. -/
theorem concrete_summable_rows :
    HasSummableRows μ (ConcreteFock.operator μ hsupport alpha ha) := by
  unfold HasSummableRows
  simpa only [coordinate_comp_operator μ hsupport alpha ha] using
    (WeightedMoments.coefficient_norm_sq_summable μ hsupport alpha ha)

/-- Exact norm formula for each single weighted moment functional. -/
theorem coefficient_energy_exact (n : ℕ) :
    ‖WeightedMoments.coefficient μ hsupport alpha n‖ ^ 2 =
      WeightedMoments.squareWeight alpha n *
        ‖WeightedMoments.monomial μ hsupport n‖ ^ 2 := by
  unfold WeightedMoments.coefficient
  rw [norm_smul, innerSL_apply_norm, mul_pow,
    WeightedMoments.complexWeight_norm_sq alpha ha n]

/-- Full actual Hilbert row-energy is the weighted L² monomial series. -/
theorem concrete_squared_row_energy :
    squaredRowEnergy μ (ConcreteFock.operator μ hsupport alpha ha) =
      ∑' n, WeightedMoments.squareWeight alpha n *
        ‖WeightedMoments.monomial μ hsupport n‖ ^ 2 := by
  unfold squaredRowEnergy
  apply tsum_congr
  intro n
  rw [coordinate_comp_operator μ hsupport alpha ha n]
  exact coefficient_energy_exact μ hsupport alpha ha n

#print axioms GegenbauerFock.FockEnergy.coordinate_comp_operator
#print axioms GegenbauerFock.FockEnergy.concrete_summable_rows
#print axioms GegenbauerFock.FockEnergy.coefficient_energy_exact
#print axioms GegenbauerFock.FockEnergy.concrete_squared_row_energy

end GegenbauerFock.FockEnergy
