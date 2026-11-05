import GegenbauerFock.TwoSidedGramRieszSchauderClassification
import Mathlib.Algebra.Module.LinearMap.Index

/-!
# V007 — zero Fredholm index on the true bilateral resolvent

At any resolvent parameter of a bounded endomorphism on a complex
Hilbert space, its spectral shift is bijective and hence has
Fredholm index zero. The result is specialized to the two genuine
ultraspherical/Fock Gram operators at every point outside their
common spectrum.

This is a first checkpoint toward an index-zero theorem on all
nonzero spectral shifts, including isolated nonzero eigenvalues.
No index claim is made at eigenvalues in this module.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A bounded complex Hilbert-space endomorphism has index zero at
every point of its resolvent set. -/
theorem fredholmShift_index_zero_of_mem_resolvent
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (mu : ℂ)
    (hmu : mu ∈ resolventSet ℂ T) :
    (T - mu • (1 : H →L[ℂ] H)).index = 0 := by
  have hunit : IsUnit (mu • (1 : H →L[ℂ] H) - T) := by
    simpa only [resolventSet, Set.mem_ofPred_eq,
      Algebra.algebraMap_eq_smul_one] using hmu
  have hunit' : IsUnit (T - mu • (1 : H →L[ℂ] H)) := by
    simpa only [neg_sub] using hunit.neg
  exact LinearMap.index_of_bijective
    (ContinuousLinearMap.isUnit_iff_bijective.mp hunit')

/-- The original ultraspherical source Gram has zero Fredholm index
at every nonspectral complex parameter. -/
theorem sourceGram_outside_spectrum_fredholm_index_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hnot : mu ∉ spectrum ℂ (gram lam alpha hlam ha)) :
    (gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))).index = 0 := by
  have hres : mu ∈ resolventSet ℂ (gram lam alpha hlam ha) := by
    simpa only [spectrum, Set.mem_compl_iff, not_not] using hnot
  exact fredholmShift_index_zero_of_mem_resolvent
    (gram lam alpha hlam ha) mu hres

/-- The actual Gaussian Fock coefficient output Gram has zero
Fredholm index at every nonspectral complex parameter. -/
theorem outputGram_outside_spectrum_fredholm_index_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hnot : mu ∉ spectrum ℂ (outputGram lam alpha hlam ha)) :
    (outputGram lam alpha hlam ha -
      mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)).index = 0 := by
  have hres : mu ∈ resolventSet ℂ (outputGram lam alpha hlam ha) := by
    simpa only [spectrum, Set.mem_compl_iff, not_not] using hnot
  exact fredholmShift_index_zero_of_mem_resolvent
    (outputGram lam alpha hlam ha) mu hres

/-- Outside the common true Gram spectrum, both shifted Fredholm
indices are exactly zero, independently in the two Hilbert spaces. -/
theorem two_sided_gram_outside_spectrum_fredholm_indices_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (hnot : mu ∉ spectrum ℂ (gram lam alpha hlam ha)) :
    (gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))).index = 0 ∧
    (outputGram lam alpha hlam ha -
      mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)).index = 0 := by
  have hout : mu ∉ spectrum ℂ (outputGram lam alpha hlam ha) := by
    intro h
    exact hnot ((two_sided_gram_nonzero_spectrum_iff
      lam alpha hlam ha mu hmu).mpr h)
  exact ⟨sourceGram_outside_spectrum_fredholm_index_zero
      lam alpha hlam ha mu hnot,
    outputGram_outside_spectrum_fredholm_index_zero
      lam alpha hlam ha mu hout⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.fredholmShift_index_zero_of_mem_resolvent
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_outside_spectrum_fredholm_index_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_outside_spectrum_fredholm_index_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_outside_spectrum_fredholm_indices_zero

end GegenbauerFock.GeneralUltrasphericalFock
