import GegenbauerFock.PhyslibTraceClassConjugationPerturbation

/-!
# V007 — Lipschitz control of the first-order Schatten S₁ term

The first-order bilinear term of conjugation is
L_U(K)(T) = K† T U + U† T K.
For every complex Hilbert H, this true S₁ continuous-linear action
satisfies ‖L_U(K)‖ ≤ 2 ‖U‖ ‖K‖ and
‖L_U(K) - L_V(K)‖ ≤ 2 ‖U-V‖ ‖K‖.

These are operator-norm estimates on the genuine trace-normed space,
and do not alone assert the Lean HasFDerivAt predicate.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The order-one term is an actual continuous complex-linear
endomorphism in the trace-class variable. -/
noncomputable def conjugationFirstOrder_v007
    (U K : H →L[ℂ] H) :
    TraceClass H →L[ℂ] TraceClass H :=
  sandwichContinuous K.adjoint U + sandwichContinuous U.adjoint K

/-- Uniform two-sided ideal bound for the first-order term. -/
theorem conjugationFirstOrder_norm_le_v007
    (U K : H →L[ℂ] H) :
    ‖conjugationFirstOrder_v007 U K‖ ≤ 2 * ‖U‖ * ‖K‖ := by
  have hAdjU : ‖U.adjoint‖ = ‖U‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star U
  have hAdjK : ‖K.adjoint‖ = ‖K‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star K
  change ‖sandwichContinuous K.adjoint U +
    sandwichContinuous U.adjoint K‖ ≤ 2 * ‖U‖ * ‖K‖
  calc
    ‖sandwichContinuous K.adjoint U +
        sandwichContinuous U.adjoint K‖ ≤
      ‖sandwichContinuous K.adjoint U‖ +
        ‖sandwichContinuous U.adjoint K‖ := norm_add_le _ _
    _ ≤ ‖K.adjoint‖ * ‖U‖ + ‖U.adjoint‖ * ‖K‖ :=
      add_le_add (sandwichContinuous_norm_le _ _)
        (sandwichContinuous_norm_le _ _)
    _ = 2 * ‖U‖ * ‖K‖ := by rw [hAdjU, hAdjK]; ring

/-- The order-one term is 2-Lipschitz in the base multiplier U,
uniformly in any bounded direction K. -/
theorem conjugationFirstOrder_base_lipschitz_v007
    (U V K : H →L[ℂ] H) :
    ‖conjugationFirstOrder_v007 U K -
      conjugationFirstOrder_v007 V K‖ ≤
    2 * ‖U - V‖ * ‖K‖ := by
  have hAdjK : ‖K.adjoint‖ = ‖K‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star K
  have hOne :
      ‖sandwichContinuous K.adjoint U -
        sandwichContinuous K.adjoint V‖ ≤
      ‖K‖ * ‖U - V‖ := by
    have h := sandwichContinuous_multiplier_sub_norm_le
      K.adjoint U K.adjoint V
    simpa only [sub_self, norm_zero, zero_mul, zero_add, hAdjK] using h
  have hTwo :
      ‖sandwichContinuous U.adjoint K -
        sandwichContinuous V.adjoint K‖ ≤
      ‖U - V‖ * ‖K‖ := by
    have h := sandwichContinuous_multiplier_sub_norm_le
      U.adjoint K V.adjoint K
    simpa only [sub_self, norm_zero, mul_zero, add_zero,
      conjugation_adjoint_sub_norm_eq_v007 U V] using h
  have hSplit :
      (sandwichContinuous K.adjoint U + sandwichContinuous U.adjoint K) -
        (sandwichContinuous K.adjoint V + sandwichContinuous V.adjoint K) =
      (sandwichContinuous K.adjoint U - sandwichContinuous K.adjoint V) +
        (sandwichContinuous U.adjoint K - sandwichContinuous V.adjoint K) := by
    abel
  change ‖(sandwichContinuous K.adjoint U + sandwichContinuous U.adjoint K) -
      (sandwichContinuous K.adjoint V + sandwichContinuous V.adjoint K)‖ ≤
    2 * ‖U - V‖ * ‖K‖
  rw [hSplit]
  calc
    ‖(sandwichContinuous K.adjoint U - sandwichContinuous K.adjoint V) +
      (sandwichContinuous U.adjoint K - sandwichContinuous V.adjoint K)‖ ≤
      ‖sandwichContinuous K.adjoint U - sandwichContinuous K.adjoint V‖ +
        ‖sandwichContinuous U.adjoint K - sandwichContinuous V.adjoint K‖ :=
      norm_add_le _ _
    _ ≤ ‖K‖ * ‖U - V‖ + ‖U - V‖ * ‖K‖ :=
      add_le_add hOne hTwo
    _ = 2 * ‖U - V‖ * ‖K‖ := by ring

#print axioms ProbabilisticTheory.TraceClass.conjugationFirstOrder_norm_le_v007
#print axioms ProbabilisticTheory.TraceClass.conjugationFirstOrder_base_lipschitz_v007

end ProbabilisticTheory.TraceClass
