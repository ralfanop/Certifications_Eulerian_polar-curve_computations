import GegenbauerFock.CanonicalCFCCompactNonclosedRange
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — zero in the continuous spectrum of the canonical CFC Gram root

The genuine canonical positive square root of C†C is compact, injective,
and has dense nonclosed range by the kernel-certified CFC compact
quasiaffinity theorem. Hence zero belongs to its operator spectrum,
but not to its point spectrum. The argument does not use an inverse
or assume a spectral gap.

The local operator-algebra instances are explicitly fixed at the actual
ultraspherical L² measure, avoiding non-injective typeclass inference.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev ZeroRootH (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

private def zeroRootComm (lam : ℝ) :
    SMulCommClass ℝ (ZeroRootH lam →L[ℂ] ZeroRootH lam)
      (ZeroRootH lam →L[ℂ] ZeroRootH lam) where
  smul_comm r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change r • S (T f) = S (r • T f)
    exact (S.map_smul_of_tower r (T f)).symm

private def zeroRootTower (lam : ℝ) :
    IsScalarTower ℝ (ZeroRootH lam →L[ℂ] ZeroRootH lam)
      (ZeroRootH lam →L[ℂ] ZeroRootH lam) where
  smul_assoc r S T := by
    apply ContinuousLinearMap.ext
    intro f
    change (r • S) (T f) = r • S (T f)
    rfl

/-- Zero is in the spectrum of the canonical CFC square root of
the source Gram, although its kernel is trivial and its range dense.
Thus it is an actual continuous-spectrum point of the infinite
Hilbert-space operator, not an eigenvalue. -/
theorem canonical_cfc_sqrt_zero_continuous_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : SMulCommClass ℝ (ZeroRootH lam →L[ℂ] ZeroRootH lam)
        (ZeroRootH lam →L[ℂ] ZeroRootH lam) := zeroRootComm lam
     letI : IsScalarTower ℝ (ZeroRootH lam →L[ℂ] ZeroRootH lam)
        (ZeroRootH lam →L[ℂ] ZeroRootH lam) := zeroRootTower lam
     letI : ContinuousFunctionalCalculus ℂ
         (ZeroRootH lam →L[ℂ] ZeroRootH lam) IsStarNormal :=
       IsStarNormal.instContinuousFunctionalCalculus
     letI : IsometricContinuousFunctionalCalculus ℝ
         (ZeroRootH lam →L[ℂ] ZeroRootH lam) IsSelfAdjoint :=
       IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
     letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
         (ZeroRootH lam →L[ℂ] ZeroRootH lam) IsSelfAdjoint :=
       IsometricContinuousFunctionalCalculus.toNonUnital
     let P : ZeroRootH lam →L[ℂ] ZeroRootH lam :=
       CFC.sqrt (gram lam alpha hlam ha)
     (0 : ℂ) ∈ spectrum ℂ P ∧
     P.ker = ⊥ ∧
     P.range.topologicalClosure = (⊤ : Submodule ℂ (ZeroRootH lam))) := by
  letI : SMulCommClass ℝ (ZeroRootH lam →L[ℂ] ZeroRootH lam)
    (ZeroRootH lam →L[ℂ] ZeroRootH lam) := zeroRootComm lam
  letI : IsScalarTower ℝ (ZeroRootH lam →L[ℂ] ZeroRootH lam)
    (ZeroRootH lam →L[ℂ] ZeroRootH lam) := zeroRootTower lam
  letI : ContinuousFunctionalCalculus ℂ
      (ZeroRootH lam →L[ℂ] ZeroRootH lam) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : IsometricContinuousFunctionalCalculus ℝ
      (ZeroRootH lam →L[ℂ] ZeroRootH lam) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (ZeroRootH lam →L[ℂ] ZeroRootH lam) IsSelfAdjoint :=
    IsometricContinuousFunctionalCalculus.toNonUnital
  classical
  obtain ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩ :=
    exists_canonical_cfc_compact_nonclosed_range lam alpha hlam ha
  let P : ZeroRootH lam →L[ℂ] ZeroRootH lam :=
    CFC.sqrt (gram lam alpha hlam ha)
  have hnotSurj : ¬ Function.Surjective P := by
    intro hsurj
    have hrange : P.range = (⊤ : Submodule ℂ (ZeroRootH lam)) :=
      LinearMap.range_eq_top.mpr hsurj
    have hclosed : IsClosed (P.range : Set (ZeroRootH lam)) := by
      rw [hrange]
      exact isClosed_univ
    exact hnotclosed hclosed
  have hzero : (0 : ℂ) ∈ spectrum ℂ P := by
    apply spectrum.zero_mem ℂ
    intro hunit
    exact hnotSurj (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).2
  have hker : P.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  exact ⟨hzero, hker, hdense⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.canonical_cfc_sqrt_zero_continuous_spectrum

end GegenbauerFock.GeneralUltrasphericalFock
