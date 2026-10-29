import GegenbauerFock.TwoSidedGramSpectrumEquality
import GegenbauerFock.GramSpectralTheorem
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# V007 — positive-real localization of the full bilateral Gram spectra

Both true compact Grams C†C and CC† are positive selfadjoint
endomorphisms on distinct infinite-dimensional Hilbert spaces.
A nonzero spectral value of the source Gram is a genuine eigenvalue
by Fredholm's alternative; symmetry makes it real and positivity
makes its real value strictly positive.

The previously established equality of entire Gram spectra transfers
this localization to the coefficient-side Gram. Zero remains in
the continuous spectrum of each, not in either point spectrum.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every nonzero spectral value of the genuine source Gram is
a strictly positive real number, embedded into ℂ. -/
theorem source_gram_nonzero_spectral_value_positive_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (hmem : mu ∈ spectrum ℂ (gram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧ 0 < mu.re := by
  have hmem' : mu ∈ spectrum ℂ (gramIntegralOperator lam alpha hlam ha) := by
    rw [← gram_eq_gramIntegralOperator lam alpha hlam ha]
    exact hmem
  have hEig : HasEigenvalue
      (gramIntegralOperator lam alpha hlam ha).toLinearMap mu :=
    ((gramIntegralOperator_compact lam alpha hlam ha).hasEigenvalue_iff_mem_spectrum
      hmu).mpr hmem'
  have hreal : (mu.re : ℂ) = mu := by
    change (RCLike.re mu : ℂ) = mu
    rw [← RCLike.conj_eq_iff_re]
    exact (gramIntegralOperator_symmetric lam alpha hlam ha).conj_eigenvalue_eq_self hEig
  have hEigReal : HasEigenvalue
      (gramIntegralOperator lam alpha hlam ha).toLinearMap (mu.re : ℂ) := by
    rw [hreal]
    exact hEig
  have hnn : 0 ≤ mu.re :=
    eigenvalue_nonneg_of_nonneg hEigReal
      (fun x =>
        (gramIntegralOperator_isPositive lam alpha hlam ha).toLinearMap.re_inner_nonneg_right x)
  have hne : mu.re ≠ 0 := by
    intro hz
    apply hmu
    rw [← hreal, hz]
    simp
  exact ⟨hreal, lt_of_le_of_ne hnn hne.symm⟩

/-- The same strict-positive-real spectral localization holds for
the actual full Fock-output Gram, without identifying the Hilbert
spaces or replacing the operator by a finite truncation. -/
theorem output_gram_nonzero_spectral_value_positive_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (hmem : mu ∈ spectrum ℂ (outputGram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧ 0 < mu.re := by
  have hsource : mu ∈ spectrum ℂ (gram lam alpha hlam ha) :=
    (two_sided_gram_spectrum_eq lam alpha hlam ha).symm ▸ hmem
  exact source_gram_nonzero_spectral_value_positive_real
    lam alpha hlam ha mu hmu hsource

/-- Complete geometric description: on each Hilbert side every
spectral value lies on the nonnegative real axis, including the
zero continuous-spectral point. -/
theorem two_sided_gram_spectra_nonnegative_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∀ mu ∈ spectrum ℂ (gram lam alpha hlam ha),
        (mu.re : ℂ) = mu ∧ 0 ≤ mu.re) ∧
    (∀ mu ∈ spectrum ℂ (outputGram lam alpha hlam ha),
        (mu.re : ℂ) = mu ∧ 0 ≤ mu.re) := by
  constructor
  · intro mu hm
    by_cases hz : mu = 0
    · subst mu
      simp
    · obtain ⟨hr, hp⟩ :=
        source_gram_nonzero_spectral_value_positive_real lam alpha hlam ha mu hz hm
      exact ⟨hr, hp.le⟩
  · intro mu hm
    by_cases hz : mu = 0
    · subst mu
      simp
    · obtain ⟨hr, hp⟩ :=
        output_gram_nonzero_spectral_value_positive_real lam alpha hlam ha mu hz hm
      exact ⟨hr, hp.le⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.source_gram_nonzero_spectral_value_positive_real
#print axioms GegenbauerFock.GeneralUltrasphericalFock.output_gram_nonzero_spectral_value_positive_real
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_spectra_nonnegative_real

end GegenbauerFock.GeneralUltrasphericalFock
