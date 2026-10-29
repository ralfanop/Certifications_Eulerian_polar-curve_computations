import GegenbauerFock.PositivePolarAmplitude
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# V007 — canonical continuous-functional-calculus square root

For the actual Gegenbauer–Fock transform C, the polar amplitude P
is a positive bounded complex-linear operator with P² = C†C.
The uniqueness theorem `CFC.sqrt_unique` for the non-unital
continuous functional calculus identifies P with CFC.sqrt (C†C) as an operator
on the ORIGINAL infinite source L² Hilbert space.

No inverse of compact C and no spectral gap are asserted.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/- The real scalar action on complex-linear Hilbert endomorphisms
commutes with composition, as required by the real non-unital CFC. -/
private instance (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] :
    SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) where
  smul_comm r S T := by
    apply ContinuousLinearMap.ext
    intro x
    change r • S (T x) = S (r • T x)
    exact (S.map_smul_of_tower r (T x)).symm

/-- The true C admits a full-Hilbert unitary polar factorization
C = W ∘ CFC.sqrt (C†C), and the unique positive CFC square root has
strictly positive eigenvalues and Kummer squared-singular-value mass. -/
theorem exists_cfc_sqrt_polar_unitary_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (mu : ι → ℝ)
      (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, CFC.sqrt (gram lam alpha hlam ha) (u i) =
        (Real.sqrt (mu i) : ℂ) • u i) ∧
      (∀ f, C lam alpha hlam ha f =
        W (CFC.sqrt (gram lam alpha hlam ha) f)) := by
  classical
  obtain ⟨ι, u, mu, W, P, hp, hsum, hK, hPu, hC, hP2, hinj, hself, hPpos⟩ :=
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
  have hCFC : CFC.sqrt (gram lam alpha hlam ha) = P :=
    CFC.sqrt_unique hPmul hPnonneg
  refine ⟨ι, u, mu, W, hp, hsum, hK, ?_, ?_⟩
  · intro i
    rw [hCFC]
    exact hPu i
  · intro f
    rw [hCFC]
    exact hC f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_cfc_sqrt_polar_unitary_kummer

end GegenbauerFock.GeneralUltrasphericalFock
