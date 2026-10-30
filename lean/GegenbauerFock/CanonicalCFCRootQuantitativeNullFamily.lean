import GegenbauerFock.CanonicalCFCCompactNonclosedRange
import GegenbauerFock.FockApproximateNullConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# V007 — quantitative normalized approximate zero vectors for the canonical CFC root

For each n, the genuine full-Hilbert positive CFC square root
P = CFC.sqrt (C†C) has a unit source vector u_n with
‖P u_n‖ < 1/(n+1). This strengthens the root's approximate-spectrum
assertion by an exact, uniform modulus of decay, without constructing
a nonzero zero-eigenvector or assuming a bounded inverse.

The proof transfers the independently verified quantitative C-null
family through the exact unitary polar factorization C = W P.
-/

noncomputable section
open MeasureTheory Module End Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev QuantRootH (lam : ℝ) := Lp ℂ 2 (Ultraspherical.measure lam)

private def quantRootComm (lam : ℝ) :
    SMulCommClass ℝ (QuantRootH lam →L[ℂ] QuantRootH lam)
      (QuantRootH lam →L[ℂ] QuantRootH lam) where
  smul_comm r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change r • S (T f) = S (r • T f)
    exact (S.map_smul_of_tower r (T f)).symm

private def quantRootTower (lam : ℝ) :
    IsScalarTower ℝ (QuantRootH lam →L[ℂ] QuantRootH lam)
      (QuantRootH lam →L[ℂ] QuantRootH lam) where
  smul_assoc r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change (r • S) (T f) = r • S (T f)
    rfl

/-- Sharp explicit per-index approximate-zero decay for the canonical
CFC square root on its actual ultraspherical source Hilbert space. -/
theorem canonical_cfc_sqrt_quantitative_normalized_approximate_null_family
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : SMulCommClass ℝ (QuantRootH lam →L[ℂ] QuantRootH lam)
        (QuantRootH lam →L[ℂ] QuantRootH lam) := quantRootComm lam
     letI : IsScalarTower ℝ (QuantRootH lam →L[ℂ] QuantRootH lam)
        (QuantRootH lam →L[ℂ] QuantRootH lam) := quantRootTower lam
     letI : ContinuousFunctionalCalculus ℂ
         (QuantRootH lam →L[ℂ] QuantRootH lam) IsStarNormal :=
       IsStarNormal.instContinuousFunctionalCalculus
     letI : IsometricContinuousFunctionalCalculus ℝ
         (QuantRootH lam →L[ℂ] QuantRootH lam) IsSelfAdjoint :=
       IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
     letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
         (QuantRootH lam →L[ℂ] QuantRootH lam) IsSelfAdjoint :=
       IsometricContinuousFunctionalCalculus.toNonUnital
     ∃ u : ℕ → QuantRootH lam,
       ∀ n : ℕ,
         ‖u n‖ = 1 ∧
         ‖CFC.sqrt (gram lam alpha hlam ha) (u n)‖ <
           1 / ((n : ℝ) + 1)) := by
  letI : SMulCommClass ℝ (QuantRootH lam →L[ℂ] QuantRootH lam)
    (QuantRootH lam →L[ℂ] QuantRootH lam) := quantRootComm lam
  letI : IsScalarTower ℝ (QuantRootH lam →L[ℂ] QuantRootH lam)
    (QuantRootH lam →L[ℂ] QuantRootH lam) := quantRootTower lam
  letI : ContinuousFunctionalCalculus ℂ
      (QuantRootH lam →L[ℂ] QuantRootH lam) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : IsometricContinuousFunctionalCalculus ℝ
      (QuantRootH lam →L[ℂ] QuantRootH lam) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (QuantRootH lam →L[ℂ] QuantRootH lam) IsSelfAdjoint :=
    IsometricContinuousFunctionalCalculus.toNonUnital
  classical
  obtain ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩ :=
    exists_canonical_cfc_compact_nonclosed_range lam alpha hlam ha
  obtain ⟨u, hunitSmall⟩ :=
    C_exists_normalized_approximate_null_family lam alpha hlam ha
  refine ⟨u, ?_⟩
  intro n
  refine ⟨(hunitSmall n).1, ?_⟩
  have hnorm :
      ‖CFC.sqrt (gram lam alpha hlam ha) (u n)‖ =
      ‖C lam alpha hlam ha (u n)‖ := by
    calc
      ‖CFC.sqrt (gram lam alpha hlam ha) (u n)‖ =
          ‖W (CFC.sqrt (gram lam alpha hlam ha) (u n))‖ :=
        (W.norm_map _).symm
      _ = ‖C lam alpha hlam ha (u n)‖ :=
        congrArg norm (hC (u n)).symm
  rw [hnorm]
  exact (hunitSmall n).2

#print axioms GegenbauerFock.GeneralUltrasphericalFock.canonical_cfc_sqrt_quantitative_normalized_approximate_null_family

end GegenbauerFock.GeneralUltrasphericalFock
