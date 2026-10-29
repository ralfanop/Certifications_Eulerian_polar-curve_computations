import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramSpectral
import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramContinuousSpectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# V007 — actual holomorphic Gaussian output Gram spectrum is nonnegative real

The genuine entire Gaussian L² output Gram H_hol is compact,
self-adjoint and positive by the exact-source checked theorem group.
Every nonzero spectral parameter is an actual eigenvalue by the
Fredholm alternative, and hence must be a strictly positive real
number. Zero is already known to lie in continuous spectrum.

These statements characterize the location of ALL spectral values
without identifying the ultraspherical source Hilbert space with
the holomorphic Gaussian output Hilbert space, or using finite
truncations of the operator.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every nonzero complex spectral value of the actual holomorphic
Gaussian L² output Gram is a strictly positive real value. -/
theorem C_intrinsicEntire_outputGram_nonzero_spectral_value_positive_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     mu ∈ spectrum ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha) →
       (mu.re : ℂ) = mu ∧ 0 < mu.re) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  intro hmem
  have hEig : HasEigenvalue
      (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu :=
    ((C_intrinsicEntire_outputGram_compact lam alpha hlam ha)
      .hasEigenvalue_iff_mem_spectrum hmu).mpr hmem
  have hreal : (mu.re : ℂ) = mu := by
    change (RCLike.re mu : ℂ) = mu
    exact RCLike.conj_eq_iff_re.mp
      ((C_intrinsicEntire_outputGram_symmetric lam alpha hlam ha)
        .conj_eigenvalue_eq_self hEig)
  have hEigReal : HasEigenvalue
      (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap
        (mu.re : ℂ) := by
    rw [hreal]
    exact hEig
  have hnn : 0 ≤ mu.re :=
    eigenvalue_nonneg_of_nonneg hEigReal
      (fun F =>
        (C_intrinsicEntire_outputGram_isPositive lam alpha hlam ha)
          .toLinearMap.re_inner_nonneg_right F)
  have hne : mu.re ≠ 0 := by
    intro hz
    apply hmu
    rw [← hreal, hz]
    simp
  exact ⟨hreal, lt_of_le_of_ne hnn hne.symm⟩

/-- Every spectral value of the ACTUAL holomorphic Gaussian Fock
output Gram belongs to the nonnegative real axis of ℂ. -/
theorem C_intrinsicEntire_outputGram_spectrum_nonnegative_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     ∀ mu ∈ spectrum ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha),
       (mu.re : ℂ) = mu ∧ 0 ≤ mu.re) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  intro mu hmem
  by_cases hz : mu = 0
  · subst mu
    simp
  · obtain ⟨hr, hp⟩ :=
      C_intrinsicEntire_outputGram_nonzero_spectral_value_positive_real
        lam alpha hlam ha mu hz hmem
    exact ⟨hr, hp.le⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_nonzero_spectral_value_positive_real
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_spectrum_nonnegative_real

end GegenbauerFock.GeneralUltrasphericalFock
