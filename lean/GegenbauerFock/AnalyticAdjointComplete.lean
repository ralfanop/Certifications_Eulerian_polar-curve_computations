import GegenbauerFock.AnalyticRestrictionCLM
import GegenbauerFock.AdjointPolynomial

/-!
# V007: full analytic adjoint by continuity and canonical Fock basis density

Every step is an equality of actual bounded maps on Hilbert spaces:
1. the exact imaginary-axis coherent coefficient on each monomial;
2. equality with the genuine row-adjoint L² representer on each basis;
3. extension from the canonical basis to arbitrary ℓ² by continuity.
No equality of merely formal pointwise L² representatives is assumed.
-/

open MeasureTheory
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockAnalyticRestriction

/-- The coherent evaluation at the imaginary Gegenbauer point,
applied to one canonical Fock coordinate, gives exactly the
conjugated Fourier moment amplitude multiplied by the real monomial. -/
theorem evaluation_single_imaginary (alpha : ℝ) (ha : 0 < alpha)
    (n : ℕ) (a : ℂ) (u : ℝ) :
    evaluation alpha ha (imaginaryPoint alpha u)
      (lp.single 2 n a) =
      (star (WeightedMoments.complexWeight alpha n) * a) * (u : ℂ) ^ n := by
  let w : ℂ := WeightedMoments.complexWeight alpha n
  have hpositive : 0 < WeightedMoments.squareWeight alpha n := by
    unfold WeightedMoments.squareWeight
    positivity
  have hw0 : w ≠ 0 := by
    intro hzero
    have hs := WeightedMoments.complexWeight_norm_sq alpha ha n
    change ‖w‖ ^ 2 = _ at hs
    rw [hzero] at hs
    simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
    linarith
  have hnormsq :
      star w * w = (WeightedMoments.squareWeight alpha n : ℂ) := by
    calc
      star w * w = (Complex.normSq w : ℂ) := by
        simpa only [Complex.star_def] using
          (Complex.normSq_eq_conj_mul_self (z := w)).symm
      _ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_norm_sq]
      _ = (WeightedMoments.squareWeight alpha n : ℂ) := by
        exact_mod_cast
          (WeightedMoments.complexWeight_norm_sq alpha ha n)
  have hz : Complex.I * imaginaryPoint alpha u / 2 =
      (u : ℂ) / (4 * (alpha : ℂ)) := by
    unfold imaginaryPoint
    have hα : (alpha : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt ha)
    field_simp
    simp [Complex.I_mul_I]
    ring
  have hfactor :
      (Complex.I * imaginaryPoint alpha u / 2) ^ n /
        (Nat.factorial n : ℂ) =
      (WeightedMoments.squareWeight alpha n : ℂ) * (u : ℂ) ^ n := by
    rw [hz]
    unfold WeightedMoments.squareWeight
    push_cast
    rw [div_pow]
    ring
  have hfromKernel := GeneralUltrasphericalFock.fock_kernel_weight
    alpha ha (imaginaryPoint alpha u) n
  rw [RCLike.inner_apply'] at hfromKernel
  change star (FockEvaluation.kernelCoordinate alpha
    (imaginaryPoint alpha u) n) * w = _ at hfromKernel
  rw [hfactor] at hfromKernel
  have hpoint :
      star (FockEvaluation.kernelCoordinate alpha
        (imaginaryPoint alpha u) n) =
        star w * (u : ℂ) ^ n := by
    apply (mul_right_cancel₀ hw0)
    calc
      star (FockEvaluation.kernelCoordinate alpha
          (imaginaryPoint alpha u) n) * w =
        (WeightedMoments.squareWeight alpha n : ℂ) * (u : ℂ) ^ n :=
          hfromKernel
      _ = (star w * (u : ℂ) ^ n) * w := by
        rw [← hnormsq]
        ring
  change inner ℂ
    (FockEvaluation.kernelVector alpha ha (imaginaryPoint alpha u))
    (lp.single 2 n a) = _
  rw [lp.inner_single_right]
  change inner ℂ
    (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n) a = _
  rw [RCLike.inner_apply', hpoint]
  ring

/-- At a canonical coordinate vector, the actual L² restriction is
exactly the conjugated-weight monomial Riesz representer. -/
theorem restrictionLp_single
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) (a : ℂ) :
    restrictionLp lam alpha hlam ha (lp.single 2 n a) =
      (star (WeightedMoments.complexWeight alpha n) * a) •
        WeightedMoments.monomial
          (Ultraspherical.measure lam)
          (GeneralUltrasphericalFock.ae_abs_le_one lam) n := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let c : ℂ := star (WeightedMoments.complexWeight alpha n) * a
  have hpoint :
      evaluate alpha ha (lp.single 2 n a) =
        fun u : ℝ => c • ((u : ℂ) ^ n) := by
    funext u
    exact evaluation_single_imaginary alpha ha n a u
  change (memLp_evaluate lam alpha hlam ha (lp.single 2 n a)).toLp
    (evaluate alpha ha (lp.single 2 n a)) = _
  have hm := WeightedMoments.monomial_memLp
    (Ultraspherical.measure lam)
    (GeneralUltrasphericalFock.ae_abs_le_one lam) n
  calc
    _ = (hm.const_smul c).toLp (fun u : ℝ => c • ((u : ℂ) ^ n)) := by
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall (fun u => congrFun hpoint u)
    _ = c • WeightedMoments.monomial
        (Ultraspherical.measure lam)
        (GeneralUltrasphericalFock.ae_abs_le_one lam) n := by
      exact MemLp.toLp_const_smul c hm

/-- The *whole* infinite-dimensional analytic restriction is exactly
the Hilbert adjoint of the ultraspherical Gegenbauer–Fock operator.
The basis test is extended by Mathlib's certified lp-basis density
and continuity theorem; there is no cutoff and no extra axiom. -/
theorem restrictionCLM_eq_C_adjoint
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    restrictionCLM lam alpha hlam ha =
      GeneralUltrasphericalFock.C_adjoint lam alpha hlam ha := by
  apply lp.ext_continuousLinearMap
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro n
  apply ContinuousLinearMap.ext
  intro a
  change restrictionLp lam alpha hlam ha (lp.single 2 n a) =
    GeneralUltrasphericalFock.C_adjoint lam alpha hlam ha
      (lp.single 2 n a)
  rw [restrictionLp_single lam alpha hlam ha n a]
  change
    (star (WeightedMoments.complexWeight alpha n) * a) •
      WeightedMoments.monomial
        (Ultraspherical.measure lam)
        (GeneralUltrasphericalFock.ae_abs_le_one lam) n =
    (ConcreteFock.operator (Ultraspherical.measure lam)
      (GeneralUltrasphericalFock.ae_abs_le_one lam) alpha ha).adjoint
      (lp.single 2 n a)
  rw [FockAdjointBasis.adjoint_single
    (Ultraspherical.measure lam)
    (GeneralUltrasphericalFock.ae_abs_le_one lam) alpha ha n a]
  exact (AdjointPolynomial.coefficient_adjoint_explicit
    (Ultraspherical.measure lam)
    (GeneralUltrasphericalFock.ae_abs_le_one lam) alpha n a).symm

/-- Final exact Hilbert-space analytic-adjoint identity for arbitrary
Fock coefficient vector F, not only finite-support approximants. -/
theorem adjoint_eq_analytic_restriction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    GeneralUltrasphericalFock.C_adjoint lam alpha hlam ha F =
      restrictionLp lam alpha hlam ha F := by
  have h := restrictionCLM_eq_C_adjoint lam alpha hlam ha
  exact congrArg (fun T : InfiniteAnalysis.FockCoefficients →L[ℂ]
    Lp ℂ 2 (Ultraspherical.measure lam) => T F) h.symm

#print axioms GegenbauerFock.FockAnalyticRestriction.evaluation_single_imaginary
#print axioms GegenbauerFock.FockAnalyticRestriction.restrictionLp_single
#print axioms GegenbauerFock.FockAnalyticRestriction.restrictionCLM_eq_C_adjoint
#print axioms GegenbauerFock.FockAnalyticRestriction.adjoint_eq_analytic_restriction

end GegenbauerFock.FockAnalyticRestriction
