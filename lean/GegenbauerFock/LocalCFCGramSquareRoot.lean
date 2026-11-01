import GegenbauerFock.PositivePolarAmplitude
import GegenbauerFock.CompactPositivePolarNonclosedRange
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# V007 — local scalar actions for the canonical CFC Gram square root

The pinned non-unital real CFC requires scalar commutation and tower
classes on the complex bounded endomorphism algebra. We construct both
classes explicitly for the actual ultraspherical L² space and apply
`CFC.sqrt_unique` without global instances or added mathematical axioms.

The named operator `localCFCGramSqrt` is definitionally the Mathlib
`CFC.sqrt` of the true Gram, with the real scalar algebra instances
selected locally; the public theorem has no extra class hypotheses.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev Source (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

private def cfcComm (lam : ℝ) :
    SMulCommClass ℝ (Source lam →L[ℂ] Source lam)
      (Source lam →L[ℂ] Source lam) where
  smul_comm r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change r • S (T f) = S (r • T f)
    exact (S.map_smul_of_tower r (T f)).symm

private def cfcTower (lam : ℝ) :
    IsScalarTower ℝ (Source lam →L[ℂ] Source lam)
      (Source lam →L[ℂ] Source lam) where
  smul_assoc r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change (r • S) (T f) = r • S (T f)
    rfl

/-- The actual non-unital CFC positive square root of the source Gram.
Its two real operator-algebra scalar compatibility witnesses are local,
not mathematical assumptions supplied by the caller. -/
noncomputable def localCFCGramSqrt
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Source lam →L[ℂ] Source lam := by
  letI : SMulCommClass ℝ (Source lam →L[ℂ] Source lam)
    (Source lam →L[ℂ] Source lam) := cfcComm lam
  letI : IsScalarTower ℝ (Source lam →L[ℂ] Source lam)
    (Source lam →L[ℂ] Source lam) := cfcTower lam
  letI : ContinuousFunctionalCalculus ℂ
    (Source lam →L[ℂ] Source lam) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : IsometricContinuousFunctionalCalculus ℝ
    (Source lam →L[ℂ] Source lam) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
    (Source lam →L[ℂ] Source lam) IsSelfAdjoint :=
    IsometricContinuousFunctionalCalculus.toNonUnital
  exact CFC.sqrt (gram lam alpha hlam ha)

/-- The local CFC square root is the certified positive polar
amplitude and gives the full unitary polar factorization. -/
theorem exists_local_cfc_sqrt_polar_unitary_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Source lam))
      (mu : ι → ℝ)
      (W : Source lam ≃ₗᵢ[ℂ] InfiniteAnalysis.FockCoefficients),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, localCFCGramSqrt lam alpha hlam ha (u i) =
        (Real.sqrt (mu i) : ℂ) • u i) ∧
      (∀ f, C lam alpha hlam ha f =
        W (localCFCGramSqrt lam alpha hlam ha f)) := by
  classical
  obtain ⟨ι, u, mu, W, P, hp, hsum, hK, hPu, hC, hP2, hinj, hself, hPos⟩ :=
    exists_positive_polar_amplitude_kummer lam alpha hlam ha
  have hPnonneg : (0 : Source lam →L[ℂ] Source lam) ≤ P := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff P).mp hPos
  have hPmul : P * P = gram lam alpha hlam ha := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply] using (hP2 f).symm
  have hRoot : localCFCGramSqrt lam alpha hlam ha = P := by
    letI : SMulCommClass ℝ (Source lam →L[ℂ] Source lam)
      (Source lam →L[ℂ] Source lam) := cfcComm lam
    letI : IsScalarTower ℝ (Source lam →L[ℂ] Source lam)
      (Source lam →L[ℂ] Source lam) := cfcTower lam
    letI : ContinuousFunctionalCalculus ℂ
      (Source lam →L[ℂ] Source lam) IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    letI : IsometricContinuousFunctionalCalculus ℝ
      (Source lam →L[ℂ] Source lam) IsSelfAdjoint :=
      IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
    letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (Source lam →L[ℂ] Source lam) IsSelfAdjoint :=
      IsometricContinuousFunctionalCalculus.toNonUnital
    change CFC.sqrt (gram lam alpha hlam ha) = P
    exact CFC.sqrt_unique hPmul hPnonneg
  refine ⟨ι, u, mu, W, hp, hsum, hK, ?_, ?_⟩
  · intro i
    rw [hRoot]
    exact hPu i
  · intro f
    rw [hRoot]
    exact hC f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_local_cfc_sqrt_polar_unitary_kummer

/-- The named canonical CFC Gram square root is a compact quasiaffinity:
it is injective, has dense nonclosed range, and factors the actual
Gegenbauer--Fock transform through a unitary. No extra CFC scalar
instances are required in the statement or by its callers. -/
theorem exists_local_cfc_sqrt_compact_dense_nonclosed
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (W : Source lam ≃ₗᵢ[ℂ] InfiniteAnalysis.FockCoefficients),
      IsCompactOperator (localCFCGramSqrt lam alpha hlam ha) ∧
      Function.Injective (localCFCGramSqrt lam alpha hlam ha) ∧
      (localCFCGramSqrt lam alpha hlam ha).range.topologicalClosure =
        (⊤ : Submodule ℂ (Source lam)) ∧
      ¬ IsClosed ((localCFCGramSqrt lam alpha hlam ha).range :
        Set (Source lam)) ∧
      (∀ f, C lam alpha hlam ha f =
        W (localCFCGramSqrt lam alpha hlam ha f)) := by
  classical
  obtain ⟨W, P, hcompact, hinj, hself, hpositive,
      hdense, hnotclosed, hC, hP2⟩ :=
    exists_positive_polar_amplitude_nonclosed_range lam alpha hlam ha
  have hPnonneg : (0 : Source lam →L[ℂ] Source lam) ≤ P := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff P).mp hpositive
  have hPmul : P * P = gram lam alpha hlam ha := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply] using (hP2 f).symm
  have hRoot : localCFCGramSqrt lam alpha hlam ha = P := by
    letI : SMulCommClass ℝ (Source lam →L[ℂ] Source lam)
      (Source lam →L[ℂ] Source lam) := cfcComm lam
    letI : IsScalarTower ℝ (Source lam →L[ℂ] Source lam)
      (Source lam →L[ℂ] Source lam) := cfcTower lam
    letI : ContinuousFunctionalCalculus ℂ
      (Source lam →L[ℂ] Source lam) IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    letI : IsometricContinuousFunctionalCalculus ℝ
      (Source lam →L[ℂ] Source lam) IsSelfAdjoint :=
      IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
    letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (Source lam →L[ℂ] Source lam) IsSelfAdjoint :=
      IsometricContinuousFunctionalCalculus.toNonUnital
    change CFC.sqrt (gram lam alpha hlam ha) = P
    exact CFC.sqrt_unique hPmul hPnonneg
  rw [hRoot]
  exact ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_local_cfc_sqrt_compact_dense_nonclosed

end GegenbauerFock.GeneralUltrasphericalFock
