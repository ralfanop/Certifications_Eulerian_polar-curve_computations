import GegenbauerFock.CanonicalCFCCompactNonclosedRange
import GegenbauerFock.GramApproximateZeroSpectrum
import Mathlib.Topology.Constructions

/-!
# V007 — no continuous exact inverse on the canonical CFC root range

For the true positive root P = CFC.sqrt (C†C), an exact reconstruction
defined on P.range (with its actual subtype topology) cannot be
continuous at zero. This rules out nonlinear continuous inverse maps,
not merely bounded linear inverses. No global extension of an inverse
to the whole ambient Hilbert space is postulated.
-/

noncomputable section
open MeasureTheory Module End Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev RootInvH (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

private def rootInvComm (lam : ℝ) :
    SMulCommClass ℝ (RootInvH lam →L[ℂ] RootInvH lam)
      (RootInvH lam →L[ℂ] RootInvH lam) where
  smul_comm r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change r • S (T f) = S (r • T f)
    exact (S.map_smul_of_tower r (T f)).symm

private def rootInvTower (lam : ℝ) :
    IsScalarTower ℝ (RootInvH lam →L[ℂ] RootInvH lam)
      (RootInvH lam →L[ℂ] RootInvH lam) where
  smul_assoc r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change (r • S) (T f) = r • S (T f)
    rfl

/-- Exact reconstruction from the actual range of the canonical
CFC square root is discontinuous at zero, including for nonlinear
candidate reconstruction functions. -/
theorem canonical_cfc_sqrt_inverse_on_range_discontinuous_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : SMulCommClass ℝ (RootInvH lam →L[ℂ] RootInvH lam)
        (RootInvH lam →L[ℂ] RootInvH lam) := rootInvComm lam
     letI : IsScalarTower ℝ (RootInvH lam →L[ℂ] RootInvH lam)
        (RootInvH lam →L[ℂ] RootInvH lam) := rootInvTower lam
     letI : ContinuousFunctionalCalculus ℂ
         (RootInvH lam →L[ℂ] RootInvH lam) IsStarNormal :=
       IsStarNormal.instContinuousFunctionalCalculus
     letI : IsometricContinuousFunctionalCalculus ℝ
         (RootInvH lam →L[ℂ] RootInvH lam) IsSelfAdjoint :=
       IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
     letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
         (RootInvH lam →L[ℂ] RootInvH lam) IsSelfAdjoint :=
       IsometricContinuousFunctionalCalculus.toNonUnital
     let P : RootInvH lam →L[ℂ] RootInvH lam :=
       CFC.sqrt (gram lam alpha hlam ha)
     ∀ (r : P.range → RootInvH lam),
       (∀ x : RootInvH lam, r ⟨P x, ⟨x, rfl⟩⟩ = x) →
       ¬ ContinuousAt r (0 : P.range)) := by
  letI : SMulCommClass ℝ (RootInvH lam →L[ℂ] RootInvH lam)
    (RootInvH lam →L[ℂ] RootInvH lam) := rootInvComm lam
  letI : IsScalarTower ℝ (RootInvH lam →L[ℂ] RootInvH lam)
    (RootInvH lam →L[ℂ] RootInvH lam) := rootInvTower lam
  letI : ContinuousFunctionalCalculus ℂ
      (RootInvH lam →L[ℂ] RootInvH lam) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : IsometricContinuousFunctionalCalculus ℝ
      (RootInvH lam →L[ℂ] RootInvH lam) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (RootInvH lam →L[ℂ] RootInvH lam) IsSelfAdjoint :=
    IsometricContinuousFunctionalCalculus.toNonUnital
  classical
  obtain ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩ :=
    exists_canonical_cfc_compact_nonclosed_range lam alpha hlam ha
  let P : RootInvH lam →L[ℂ] RootInvH lam :=
    CFC.sqrt (gram lam alpha hlam ha)
  obtain ⟨u, hunit, himage⟩ :=
    C_exists_normalized_approximate_null_sequence lam alpha hlam ha
  have hPzero : Tendsto (fun n : ℕ => P (u n))
      atTop (nhds (0 : RootInvH lam)) := by
    have hW : Tendsto
        (fun n : ℕ => W.symm (C lam alpha hlam ha (u n)))
        atTop (nhds (W.symm (0 : InfiniteAnalysis.FockCoefficients))) :=
      W.symm.continuous.continuousAt.tendsto.comp himage
    have heq : (fun n : ℕ => W.symm (C lam alpha hlam ha (u n))) =
        (fun n : ℕ => P (u n)) := by
      funext n
      rw [hC (u n)]
      exact W.symm_apply_apply (P (u n))
    rw [heq] at hW
    simpa using hW
  change ∀ (r : P.range → RootInvH lam),
      (∀ x : RootInvH lam, r ⟨P x, ⟨x, rfl⟩⟩ = x) →
      ¬ ContinuousAt r (0 : P.range)
  intro r hleft hcont
  have hsub : Tendsto
      (fun n : ℕ => (⟨P (u n), ⟨u n, rfl⟩⟩ : P.range))
      atTop (nhds (0 : P.range)) := by
    apply tendsto_subtype_rng.mpr
    simpa using hPzero
  have hrec : Tendsto
      (fun n : ℕ => r (⟨P (u n), ⟨u n, rfl⟩⟩ : P.range))
      atTop (nhds (r (0 : P.range))) :=
    hcont.tendsto.comp hsub
  have heq : (fun n : ℕ =>
      r (⟨P (u n), ⟨u n, rfl⟩⟩ : P.range)) = u := by
    funext n
    exact hleft (u n)
  rw [heq] at hrec
  have hrzero : r (0 : P.range) = 0 := by
    have hzero : (⟨P (0 : RootInvH lam),
        ⟨(0 : RootInvH lam), rfl⟩⟩ : P.range) = 0 := by
      apply Subtype.ext
      exact map_zero P
    calc
      r (0 : P.range) =
          r (⟨P (0 : RootInvH lam),
              ⟨(0 : RootInvH lam), rfl⟩⟩ : P.range) :=
        congrArg r hzero.symm
      _ = 0 := hleft 0
  rw [hrzero] at hrec
  have hnormzero : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (0 : ℝ)) := by
    simpa using hrec.norm
  have hnormone : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (1 : ℝ)) := by
    have heqnorm : (fun n : ℕ => ‖u n‖) =
        (fun _ : ℕ => (1 : ℝ)) := funext hunit
    rw [heqnorm]
    exact tendsto_const_nhds
  have himpossible : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hnormzero hnormone
  norm_num at himpossible

#print axioms GegenbauerFock.GeneralUltrasphericalFock.canonical_cfc_sqrt_inverse_on_range_discontinuous_at_zero

end GegenbauerFock.GeneralUltrasphericalFock
