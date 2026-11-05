import GegenbauerFock.TwoSidedGramFredholmEssentialSpectrum
import GegenbauerFock.TwoSidedGramNegativeResolvent
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — Fredholm essential spectrum is contained in ordinary spectrum

An invertible bounded operator on a complex Hilbert space is Fredholm:
its continuous linear inverse makes it a continuous linear equivalence,
whose IsFredholm instance is available in Mathlib. Therefore a scalar
parameter outside the ordinary spectrum cannot be Fredholm-essential.

For the two genuine positive Grams, all strictly negative real
parameters are in their independently certified resolvent sets. This
places the complete negative real axis outside BOTH Fredholm
essential spectra, complementing the certified essential point 0.

We do not claim here the stronger global equality sigma_ess={0}.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every Fredholm-essential spectral value of a bounded Hilbert
endomorphism is an ordinary spectral value. -/
theorem fredholmEssentialSpectrum_subset_spectrum
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    fredholmEssentialSpectrum T ⊆ spectrum ℂ T := by
  intro z hz
  by_contra hnot
  have hres : z ∈ resolventSet ℂ T := by
    simpa only [spectrum, Set.mem_compl_iff, not_not] using hnot
  have hunit : IsUnit (z • (1 : H →L[ℂ] H) - T) := by
    simpa only [resolventSet, Set.mem_setOf_eq,
      Algebra.algebraMap_eq_smul_one] using hres
  have hunit' : IsUnit (T - z • (1 : H →L[ℂ] H)) := by
    simpa only [neg_sub] using hunit.neg
  change ¬ ContinuousLinearMap.IsFredholm
    (T - z • (1 : H →L[ℂ] H)) at hz
  rcases hunit' with ⟨u, hu⟩
  rw [← hu] at hz
  exact hz (ContinuousLinearEquiv.ofUnit u).isFredholm

/-- Every strictly negative real scalar is outside the Fredholm
essential spectrum of the actual ultraspherical source Gram. -/
theorem sourceGram_negative_not_fredholm_essential_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (t : ℝ) (ht : 0 < t) :
    (-(t : ℂ)) ∉ fredholmEssentialSpectrum (gram lam alpha hlam ha) := by
  have hres := source_gram_negative_real_mem_resolventSet
    lam alpha hlam ha t ht
  have hnot : (-(t : ℂ)) ∉ spectrum ℂ (gram lam alpha hlam ha) := by
    simpa only [spectrum, Set.mem_compl_iff, not_not] using hres
  exact fun h => hnot
    (fredholmEssentialSpectrum_subset_spectrum (gram lam alpha hlam ha) h)

/-- The same strictly negative scalars are outside the Fredholm
essential spectrum of the complete Fock-output Gram. -/
theorem outputGram_negative_not_fredholm_essential_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (t : ℝ) (ht : 0 < t) :
    (-(t : ℂ)) ∉ fredholmEssentialSpectrum (outputGram lam alpha hlam ha) := by
  have hres := output_gram_negative_real_mem_resolventSet
    lam alpha hlam ha t ht
  have hnot : (-(t : ℂ)) ∉ spectrum ℂ (outputGram lam alpha hlam ha) := by
    simpa only [spectrum, Set.mem_compl_iff, not_not] using hres
  exact fun h => hnot
    (fredholmEssentialSpectrum_subset_spectrum (outputGram lam alpha hlam ha) h)

/-- The Fredholm essential spectra of both true Grams contain zero,
but exclude every strictly negative real scalar. -/
theorem two_sided_gram_essential_zero_and_negative_exclusion
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((0 : ℂ) ∈
      fredholmEssentialSpectrum (gram lam alpha hlam ha) ∩
      fredholmEssentialSpectrum (outputGram lam alpha hlam ha)) ∧
    (∀ t : ℝ, 0 < t →
      (-(t : ℂ)) ∉ fredholmEssentialSpectrum (gram lam alpha hlam ha) ∧
      (-(t : ℂ)) ∉ fredholmEssentialSpectrum (outputGram lam alpha hlam ha)) := by
  refine ⟨two_sided_gram_zero_mem_fredholm_essential_spectra lam alpha hlam ha, ?_⟩
  intro t ht
  exact ⟨sourceGram_negative_not_fredholm_essential_spectrum lam alpha hlam ha t ht,
    outputGram_negative_not_fredholm_essential_spectrum lam alpha hlam ha t ht⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.fredholmEssentialSpectrum_subset_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_negative_not_fredholm_essential_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_negative_not_fredholm_essential_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_essential_zero_and_negative_exclusion

end GegenbauerFock.GeneralUltrasphericalFock
