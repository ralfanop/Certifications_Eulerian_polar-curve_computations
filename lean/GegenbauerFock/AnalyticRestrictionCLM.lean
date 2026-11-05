import GegenbauerFock.AdjointSummability

/-!
# V007 — analytic restriction as a genuine bounded complex-linear operator

This file proves that imaginary-axis point evaluation of every Fock
coefficient vector is complex-linear and norm bounded as an L² class.
The resulting operator is defined independently of the abstract
Hilbert adjoint, which will subsequently be identified by density.
-/

open MeasureTheory
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockAnalyticRestriction

/-- Addition of the true analytic imaginary-axis restriction in L². -/
theorem restrictionLp_add
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F G : InfiniteAnalysis.FockCoefficients) :
    restrictionLp lam alpha hlam ha (F + G) =
      restrictionLp lam alpha hlam ha F +
        restrictionLp lam alpha hlam ha G := by
  let μ := Ultraspherical.measure lam
  have hpoint :
      evaluate alpha ha (F + G) =
        evaluate alpha ha F + evaluate alpha ha G := by
    funext u
    change FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u)
      (F + G) = _
    exact map_add _ F G
  change (memLp_evaluate lam alpha hlam ha (F + G)).toLp
      (evaluate alpha ha (F + G)) = _
  calc
    _ = ((memLp_evaluate lam alpha hlam ha F).add
      (memLp_evaluate lam alpha hlam ha G)).toLp
        (evaluate alpha ha F + evaluate alpha ha G) := by
        apply MemLp.toLp_congr
        exact Filter.Eventually.of_forall (fun u => congrFun hpoint u)
    _ = _ := MemLp.toLp_add _ _

/-- Scalar linearity of the true analytic imaginary-axis restriction. -/
theorem restrictionLp_smul
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (c : ℂ) (F : InfiniteAnalysis.FockCoefficients) :
    restrictionLp lam alpha hlam ha (c • F) =
      c • restrictionLp lam alpha hlam ha F := by
  have hpoint :
      evaluate alpha ha (c • F) = c • evaluate alpha ha F := by
    funext u
    change FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u)
      (c • F) = _
    exact map_smul _ c F
  change (memLp_evaluate lam alpha hlam ha (c • F)).toLp
    (evaluate alpha ha (c • F)) = _
  calc
    _ = ((memLp_evaluate lam alpha hlam ha F).const_smul c).toLp
        (c • evaluate alpha ha F) := by
        apply MemLp.toLp_congr
        exact Filter.Eventually.of_forall (fun u => congrFun hpoint u)
    _ = _ := MemLp.toLp_const_smul _ _

/-- Explicit global L² operator-bound inherited from Fock coherent
vectors; only the proven support and mass-one hypotheses are used. -/
theorem restrictionLp_norm_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    ‖restrictionLp lam alpha hlam ha F‖ ≤
      Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖F‖ := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  have hbound : ∀ᵐ u ∂Ultraspherical.measure lam,
      ‖(restrictionLp lam alpha hlam ha F : ℝ → ℂ) u‖ ≤
        Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖F‖ := by
    filter_upwards [
      (memLp_evaluate lam alpha hlam ha F).coeFn_toLp,
      Ultraspherical.ae_mem_unit_interval lam] with u he hu
    change ‖((memLp_evaluate lam alpha hlam ha F).toLp
      (evaluate alpha ha F) : ℝ → ℂ) u‖ ≤ _
    rw [he]
    exact norm_evaluate_le alpha ha F u (abs_le.mpr ⟨hu.1, hu.2⟩)
  have h := Lp.norm_le_of_ae_bound
    (f := restrictionLp lam alpha hlam ha F)
    (C := Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖F‖)
    (by positivity) hbound
  have hm : measureUnivNNReal (Ultraspherical.measure lam) = 1 := by
    unfold measureUnivNNReal
    simp
  simpa [hm] using h

/-- The entire-coefficient Fock restriction is a genuine continuous
complex-linear map, not merely a separately defined L² class. -/
noncomputable def restrictionCLM
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    InfiniteAnalysis.FockCoefficients →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) :=
  ({ toFun := restrictionLp lam alpha hlam ha
     map_add' := restrictionLp_add lam alpha hlam ha
     map_smul' := restrictionLp_smul lam alpha hlam ha } :
       InfiniteAnalysis.FockCoefficients →ₗ[ℂ]
         Lp ℂ 2 (Ultraspherical.measure lam)).mkContinuous
      (Real.sqrt (Real.exp (1 / (4 * alpha)))) (by
        intro F
        exact restrictionLp_norm_le lam alpha hlam ha F)

#print axioms GegenbauerFock.FockAnalyticRestriction.restrictionLp_add
#print axioms GegenbauerFock.FockAnalyticRestriction.restrictionLp_smul
#print axioms GegenbauerFock.FockAnalyticRestriction.restrictionLp_norm_le

end GegenbauerFock.FockAnalyticRestriction
