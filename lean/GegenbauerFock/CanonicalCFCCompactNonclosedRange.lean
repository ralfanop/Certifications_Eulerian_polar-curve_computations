import GegenbauerFock.CanonicalCFCSqrtExplicitScalarBridge
import GegenbauerFock.CompactPositivePolarNonclosedRange

/-!
# V007 — the canonical CFC Gram square root is a compact quasiaffinity

The actual positive polar amplitude P has a verified compact, injective,
dense nonclosed range. The pinned Mathlib real nonunital continuous functional
calculus identifies P with the unique positive CFC square root of C†C,
once the real scalar operator-algebra instances are installed explicitly.

Unlike the abstract existence statements for P, this theorem states
compactness and nonclosed range for the canonical CFC.sqrt operator itself.
No bounded inverse or spectral gap is assumed.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev PolarH (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

private def polarRootComm (lam : ℝ) :
    SMulCommClass ℝ (PolarH lam →L[ℂ] PolarH lam)
      (PolarH lam →L[ℂ] PolarH lam) where
  smul_comm r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change r • S (T f) = S (r • T f)
    exact (S.map_smul_of_tower r (T f)).symm

private def polarRootTower (lam : ℝ) :
    IsScalarTower ℝ (PolarH lam →L[ℂ] PolarH lam)
      (PolarH lam →L[ℂ] PolarH lam) where
  smul_assoc r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change (r • S) (T f) = r • S (T f)
    rfl

/-- The genuine CFC positive square root of the ultraspherical Gram
is compact and injective, with dense nonclosed image; it is precisely
the factor appearing in the full unitary polar factorization. -/
theorem exists_canonical_cfc_compact_nonclosed_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : SMulCommClass ℝ (PolarH lam →L[ℂ] PolarH lam)
        (PolarH lam →L[ℂ] PolarH lam) := polarRootComm lam
     letI : IsScalarTower ℝ (PolarH lam →L[ℂ] PolarH lam)
        (PolarH lam →L[ℂ] PolarH lam) := polarRootTower lam
     letI : ContinuousFunctionalCalculus ℂ
         (PolarH lam →L[ℂ] PolarH lam) IsStarNormal :=
       IsStarNormal.instContinuousFunctionalCalculus
     letI : IsometricContinuousFunctionalCalculus ℝ
         (PolarH lam →L[ℂ] PolarH lam) IsSelfAdjoint :=
       IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
     letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
         (PolarH lam →L[ℂ] PolarH lam) IsSelfAdjoint :=
       IsometricContinuousFunctionalCalculus.toNonUnital
     ∃ (W : PolarH lam ≃ₗᵢ[ℂ] InfiniteAnalysis.FockCoefficients),
       IsCompactOperator
         (CFC.sqrt (gram lam alpha hlam ha) :
           PolarH lam →L[ℂ] PolarH lam) ∧
       Function.Injective
         (CFC.sqrt (gram lam alpha hlam ha) :
           PolarH lam →L[ℂ] PolarH lam) ∧
       ((CFC.sqrt (gram lam alpha hlam ha) :
           PolarH lam →L[ℂ] PolarH lam)).range.topologicalClosure =
         (⊤ : Submodule ℂ (PolarH lam)) ∧
       ¬ IsClosed (((CFC.sqrt (gram lam alpha hlam ha) :
           PolarH lam →L[ℂ] PolarH lam)).range :
         Set (PolarH lam)) ∧
       (∀ f, C lam alpha hlam ha f =
         W (CFC.sqrt (gram lam alpha hlam ha) f))) := by
  letI : SMulCommClass ℝ (PolarH lam →L[ℂ] PolarH lam)
    (PolarH lam →L[ℂ] PolarH lam) := polarRootComm lam
  letI : IsScalarTower ℝ (PolarH lam →L[ℂ] PolarH lam)
    (PolarH lam →L[ℂ] PolarH lam) := polarRootTower lam
  letI : ContinuousFunctionalCalculus ℂ
      (PolarH lam →L[ℂ] PolarH lam) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : IsometricContinuousFunctionalCalculus ℝ
      (PolarH lam →L[ℂ] PolarH lam) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (PolarH lam →L[ℂ] PolarH lam) IsSelfAdjoint :=
    IsometricContinuousFunctionalCalculus.toNonUnital
  classical
  obtain ⟨W, P, hcompact, hinj, hself, hpositive,
      hdense, hnotclosed, hC, hP2⟩ :=
    exists_positive_polar_amplitude_nonclosed_range lam alpha hlam ha
  have hPnonneg : (0 : PolarH lam →L[ℂ] PolarH lam) ≤ P := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff P).mp hpositive
  have hPmul : P * P = gram lam alpha hlam ha := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply] using (hP2 f).symm
  have hroot : CFC.sqrt (gram lam alpha hlam ha) = P :=
    CFC.sqrt_unique hPmul hPnonneg
  rw [hroot]
  exact ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_canonical_cfc_compact_nonclosed_range


/-- The canonical CFC square root is not onto the complete ultraspherical
Hilbert space.  Its dense nonclosed range rules out an everywhere-defined
bounded linear inverse; no spectral gap is used. -/
theorem canonical_cfc_root_not_surjective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : SMulCommClass ℝ (PolarH lam →L[ℂ] PolarH lam)
        (PolarH lam →L[ℂ] PolarH lam) := polarRootComm lam
     letI : IsScalarTower ℝ (PolarH lam →L[ℂ] PolarH lam)
        (PolarH lam →L[ℂ] PolarH lam) := polarRootTower lam
     letI : ContinuousFunctionalCalculus ℂ
         (PolarH lam →L[ℂ] PolarH lam) IsStarNormal :=
       IsStarNormal.instContinuousFunctionalCalculus
     letI : IsometricContinuousFunctionalCalculus ℝ
         (PolarH lam →L[ℂ] PolarH lam) IsSelfAdjoint :=
       IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
     letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
         (PolarH lam →L[ℂ] PolarH lam) IsSelfAdjoint :=
       IsometricContinuousFunctionalCalculus.toNonUnital
     ¬ Function.Surjective
         (CFC.sqrt (gram lam alpha hlam ha) :
            PolarH lam →L[ℂ] PolarH lam)) := by
  letI : SMulCommClass ℝ (PolarH lam →L[ℂ] PolarH lam)
    (PolarH lam →L[ℂ] PolarH lam) := polarRootComm lam
  letI : IsScalarTower ℝ (PolarH lam →L[ℂ] PolarH lam)
    (PolarH lam →L[ℂ] PolarH lam) := polarRootTower lam
  letI : ContinuousFunctionalCalculus ℂ
      (PolarH lam →L[ℂ] PolarH lam) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : IsometricContinuousFunctionalCalculus ℝ
      (PolarH lam →L[ℂ] PolarH lam) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (PolarH lam →L[ℂ] PolarH lam) IsSelfAdjoint :=
    IsometricContinuousFunctionalCalculus.toNonUnital
  obtain ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩ :=
    exists_canonical_cfc_compact_nonclosed_range lam alpha hlam ha
  intro hsurj
  have htop :
      ((CFC.sqrt (gram lam alpha hlam ha) :
           PolarH lam →L[ℂ] PolarH lam)).range =
        (⊤ : Submodule ℂ (PolarH lam)) :=
    LinearMap.range_eq_top.mpr hsurj
  apply hnotclosed
  rw [htop]
  exact isClosed_univ

#print axioms GegenbauerFock.GeneralUltrasphericalFock.canonical_cfc_root_not_surjective

end GegenbauerFock.GeneralUltrasphericalFock
