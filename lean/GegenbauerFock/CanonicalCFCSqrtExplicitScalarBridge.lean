import GegenbauerFock.PositivePolarAmplitude
import GegenbauerFock.FullUnitaryPolarAdjointOutputGram
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# V007 — explicit real-scalar instance for the canonical CFC polar square root

The true positive polar amplitude P is already certified on the full
ultraspherical source Hilbert space. This module supplies the real-scalar
commutation required by the non-unital continuous functional calculus
*explicitly inside the proposition*, so its construction does not rely on
synthesizing the measure parameter lambda from a continuous-linear-map type.

No spectral gap, bounded inverse, or surjectivity of C is assumed.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Real scalar multiplication commutes with complex-linear operator
composition on the genuine ultraspherical L² source space. -/
private def polarScalarComm (lam : ℝ) :
    SMulCommClass ℝ
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) where
  smul_comm r S T := by
    apply ContinuousLinearMap.ext
    intro x
    change r • S (T x) = S (r • T x)
    exact (S.map_smul_of_tower r (T x)).symm

/-- The same real scalar multiplication associates with composition of
complex-linear bounded operators, a second CFC requirement. -/
private def polarScalarTower (lam : ℝ) :
    IsScalarTower ℝ
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) where
  smul_assoc r S T := by
    apply ContinuousLinearMap.ext
    intro x
    change (r • S) (T x) = r • S (T x)
    rfl

/-- On the actual full Hilbert space, the positive polar amplitude
is the canonical CFC square root of C†C. The explicit local instance
in the proposition avoids non-injective measure-parameter inference. -/
theorem exists_cfc_sqrt_with_explicit_scalar_commutation
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : SMulCommClass ℝ
        (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))
        (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)) := polarScalarComm lam
     letI : IsScalarTower ℝ
        (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))
        (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)) := polarScalarTower lam
     ∃ P : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
         Lp ℂ 2 (Ultraspherical.measure lam),
       0 ≤ P ∧
       P * P = gram lam alpha hlam ha ∧
       CFC.sqrt (gram lam alpha hlam ha) = P) := by
  letI : SMulCommClass ℝ
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) := polarScalarComm lam
  letI : IsScalarTower ℝ
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) := polarScalarTower lam
  classical
  obtain ⟨ι, u, mu, W, P, hp, hsum, hK, hPu, hC, hP2,
      hinj, hself, hPpos⟩ :=
    exists_positive_polar_amplitude_kummer lam alpha hlam ha
  have hPnonneg : (0 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) ≤ P := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff P).mp hPpos
  have hPmul : P * P = gram lam alpha hlam ha := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply] using (hP2 f).symm
  refine ⟨P, hPnonneg, hPmul, ?_⟩
  exact CFC.sqrt_unique hPmul hPnonneg

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_cfc_sqrt_with_explicit_scalar_commutation


/-- The SAME canonical positive square root controls the full-Hilbert
polar transform, the Hilbert adjoint, and the output Gram operator.
Both real-scalar algebra instances are fixed at the actual
ultraspherical source space and its explicit measure parameter. -/
theorem exists_cfc_sqrt_full_polar_adjoint_outputGram_explicit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : SMulCommClass ℝ
        (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))
        (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)) := polarScalarComm lam
     letI : IsScalarTower ℝ
        (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))
        (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)) := polarScalarTower lam
     ∃ (ι : Type) (mu : ι → ℝ)
       (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
         InfiniteAnalysis.FockCoefficients),
       (∀ i, 0 < mu i) ∧
       Summable mu ∧
       (∑' i : ι, mu i) =
         KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
       (∀ f, C lam alpha hlam ha f =
         W (CFC.sqrt (gram lam alpha hlam ha) f)) ∧
       (∀ F : InfiniteAnalysis.FockCoefficients,
         C_adjoint lam alpha hlam ha F =
           CFC.sqrt (gram lam alpha hlam ha) (W.symm F)) ∧
       (∀ F : InfiniteAnalysis.FockCoefficients,
         outputGram lam alpha hlam ha F =
           W (CFC.sqrt (gram lam alpha hlam ha)
             (CFC.sqrt (gram lam alpha hlam ha) (W.symm F))))) := by
  letI : SMulCommClass ℝ
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) := polarScalarComm lam
  letI : IsScalarTower ℝ
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))
      (Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) := polarScalarTower lam
  classical
  obtain ⟨ι, u, mu, W, P, hp, hsum, hK, hC, hP2,
      hself, hPos, hAdj, hOut⟩ :=
    exists_full_unitary_polar_adjoint_and_outputGram_kummer
      lam alpha hlam ha
  have hPnonneg : (0 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) ≤ P := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff P).mp hPos
  have hPmul : P * P = gram lam alpha hlam ha := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply] using (hP2 f).symm
  have hCFC : CFC.sqrt (gram lam alpha hlam ha) = P :=
    CFC.sqrt_unique hPmul hPnonneg
  refine ⟨ι, mu, W, hp, hsum, hK, ?_, ?_, ?_⟩
  · intro f
    rw [hCFC]
    exact hC f
  · intro F
    rw [hCFC]
    exact hAdj F
  · intro F
    rw [hCFC]
    exact hOut F

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_cfc_sqrt_full_polar_adjoint_outputGram_explicit

end GegenbauerFock.GeneralUltrasphericalFock
