import GegenbauerFock.CanonicalCFCCompactNonclosedRange
import GegenbauerFock.GramApproximateZeroSpectrum

/-!
# V007 — normalized approximate-zero vectors for the canonical CFC root

The genuine canonical square root P = CFC.sqrt(C†C) has unit vectors
u_n with P u_n converging strongly to zero. The construction transfers
the previously certified approximate-null vectors of the true
Gegenbauer–Fock transform C through the unitary polar factor W.
This is not a zero eigenvector: P remains injective.
-/

noncomputable section
open MeasureTheory Module End Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev RootApproxH (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

private def rootApproxComm (lam : ℝ) :
    SMulCommClass ℝ (RootApproxH lam →L[ℂ] RootApproxH lam)
      (RootApproxH lam →L[ℂ] RootApproxH lam) where
  smul_comm r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change r • S (T f) = S (r • T f)
    exact (S.map_smul_of_tower r (T f)).symm

private def rootApproxTower (lam : ℝ) :
    IsScalarTower ℝ (RootApproxH lam →L[ℂ] RootApproxH lam)
      (RootApproxH lam →L[ℂ] RootApproxH lam) where
  smul_assoc r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change (r • S) (T f) = r • S (T f)
    rfl

/-- Zero belongs to the approximate point spectrum of the genuine
canonical CFC Gram root, witnessed by a unit-vector sequence. -/
theorem canonical_cfc_sqrt_exists_normalized_approximate_zero_vectors
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : SMulCommClass ℝ (RootApproxH lam →L[ℂ] RootApproxH lam)
        (RootApproxH lam →L[ℂ] RootApproxH lam) := rootApproxComm lam
     letI : IsScalarTower ℝ (RootApproxH lam →L[ℂ] RootApproxH lam)
        (RootApproxH lam →L[ℂ] RootApproxH lam) := rootApproxTower lam
     letI : ContinuousFunctionalCalculus ℂ
         (RootApproxH lam →L[ℂ] RootApproxH lam) IsStarNormal :=
       IsStarNormal.instContinuousFunctionalCalculus
     letI : IsometricContinuousFunctionalCalculus ℝ
         (RootApproxH lam →L[ℂ] RootApproxH lam) IsSelfAdjoint :=
       IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
     letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
         (RootApproxH lam →L[ℂ] RootApproxH lam) IsSelfAdjoint :=
       IsometricContinuousFunctionalCalculus.toNonUnital
     ∃ u : ℕ → RootApproxH lam,
       (∀ n : ℕ, ‖u n‖ = 1) ∧
       Tendsto (fun n : ℕ =>
         CFC.sqrt (gram lam alpha hlam ha) (u n))
         atTop (nhds (0 : RootApproxH lam))) := by
  letI : SMulCommClass ℝ (RootApproxH lam →L[ℂ] RootApproxH lam)
    (RootApproxH lam →L[ℂ] RootApproxH lam) := rootApproxComm lam
  letI : IsScalarTower ℝ (RootApproxH lam →L[ℂ] RootApproxH lam)
    (RootApproxH lam →L[ℂ] RootApproxH lam) := rootApproxTower lam
  letI : ContinuousFunctionalCalculus ℂ
      (RootApproxH lam →L[ℂ] RootApproxH lam) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : IsometricContinuousFunctionalCalculus ℝ
      (RootApproxH lam →L[ℂ] RootApproxH lam) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (RootApproxH lam →L[ℂ] RootApproxH lam) IsSelfAdjoint :=
    IsometricContinuousFunctionalCalculus.toNonUnital
  classical
  obtain ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩ :=
    exists_canonical_cfc_compact_nonclosed_range lam alpha hlam ha
  obtain ⟨u, hunit, himage⟩ :=
    C_exists_normalized_approximate_null_sequence lam alpha hlam ha
  refine ⟨u, hunit, ?_⟩
  have hW : Tendsto
      (fun n : ℕ => W.symm (C lam alpha hlam ha (u n)))
      atTop (nhds (W.symm (0 : InfiniteAnalysis.FockCoefficients))) :=
    W.symm.continuous.continuousAt.tendsto.comp himage
  have heq :
      (fun n : ℕ => W.symm (C lam alpha hlam ha (u n))) =
      (fun n : ℕ => CFC.sqrt (gram lam alpha hlam ha) (u n)) := by
    funext n
    rw [hC (u n)]
    exact W.symm_apply_apply _
  rw [heq] at hW
  simpa using hW

#print axioms GegenbauerFock.GeneralUltrasphericalFock.canonical_cfc_sqrt_exists_normalized_approximate_zero_vectors

end GegenbauerFock.GeneralUltrasphericalFock
