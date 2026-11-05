import GegenbauerFock.TwoSidedGramEssentialSpectrumSingleton
import GegenbauerFock.TwoSidedGramPositiveSpectrum
import GegenbauerFock.TwoSidedGramNonzeroFiniteEigenspaces
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# V007 — concrete bilateral Riesz–Schauder classification away from zero

This module makes explicit the operator-level alternative at every
nonzero complex parameter for both genuine Hilbert-space Grams:
a nonzero spectral parameter is a strictly positive real eigenvalue
with finite-dimensional eigenspace, and a nonspectral parameter
belongs to both resolvent sets. In either case the shifted operators
are Fredholm. These are statements about the full infinite-dimensional
operators, not their finite truncations.

The kernel and axiom audit, not the presence of source, determine
certification status.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A nonzero point of the true ultraspherical Gram spectrum is exactly
a strictly positive real eigenvalue of the actual source Gram. -/
theorem sourceGram_nonzero_spectrum_iff_positive_eigenvalue
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    mu ∈ spectrum ℂ (gram lam alpha hlam ha) ↔
      HasEigenvalue (gram lam alpha hlam ha).toLinearMap mu ∧
      (mu.re : ℂ) = mu ∧ 0 < mu.re := by
  constructor
  · intro hspec
    have heig : HasEigenvalue (gram lam alpha hlam ha).toLinearMap mu :=
      ((gram_compact_concrete lam alpha hlam ha).hasEigenvalue_iff_mem_spectrum
        hmu).mpr hspec
    obtain ⟨hreal, hpos⟩ :=
      source_gram_nonzero_spectral_value_positive_real lam alpha hlam ha mu hmu hspec
    exact ⟨heig, hreal, hpos⟩
  · rintro ⟨heig, _, _⟩
    exact ((gram_compact_concrete lam alpha hlam ha).hasEigenvalue_iff_mem_spectrum
      hmu).mp heig

/-- The same precise nonzero spectral classification holds on the full
Fock coefficient Hilbert space, not only its finite-dimensional slices. -/
theorem outputGram_nonzero_spectrum_iff_positive_eigenvalue
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    mu ∈ spectrum ℂ (outputGram lam alpha hlam ha) ↔
      HasEigenvalue (outputGram lam alpha hlam ha).toLinearMap mu ∧
      (mu.re : ℂ) = mu ∧ 0 < mu.re := by
  constructor
  · intro hspec
    have heig : HasEigenvalue (outputGram lam alpha hlam ha).toLinearMap mu :=
      ((outputGram_compact lam alpha hlam ha).hasEigenvalue_iff_mem_spectrum
        hmu).mpr hspec
    obtain ⟨hreal, hpos⟩ :=
      output_gram_nonzero_spectral_value_positive_real lam alpha hlam ha mu hmu hspec
    exact ⟨heig, hreal, hpos⟩
  · rintro ⟨heig, _, _⟩
    exact ((outputGram_compact lam alpha hlam ha).hasEigenvalue_iff_mem_spectrum
      hmu).mp heig

/-- Outside the common spectrum a nonzero complex parameter belongs
to the resolvent of BOTH concrete Gram operators. -/
theorem two_sided_gram_nonzero_outside_spectrum_resolvent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (hnot : mu ∉ spectrum ℂ (gram lam alpha hlam ha)) :
    mu ∈ resolventSet ℂ (gram lam alpha hlam ha) ∧
    mu ∈ resolventSet ℂ (outputGram lam alpha hlam ha) := by
  have hout : mu ∉ spectrum ℂ (outputGram lam alpha hlam ha) := by
    intro h
    exact hnot ((two_sided_gram_nonzero_spectrum_iff
      lam alpha hlam ha mu hmu).mpr h)
  constructor
  · simpa only [spectrum, Set.mem_compl_iff, not_not] using hnot
  · simpa only [spectrum, Set.mem_compl_iff, not_not] using hout

/-- Complete concrete bilateral Riesz–Schauder dichotomy:
the nonzero spectra agree, all their spectral points are strictly
positive finite-multiplicity eigenvalues, and both shifts are Fredholm
for every nonzero complex parameter. -/
theorem two_sided_gram_nonzero_riesz_schauder_classification
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (mu ∈ spectrum ℂ (gram lam alpha hlam ha) ↔
      mu ∈ spectrum ℂ (outputGram lam alpha hlam ha)) ∧
    (mu ∈ spectrum ℂ (gram lam alpha hlam ha) →
      HasEigenvalue (gram lam alpha hlam ha).toLinearMap mu ∧
      HasEigenvalue (outputGram lam alpha hlam ha).toLinearMap mu ∧
      (mu.re : ℂ) = mu ∧ 0 < mu.re) ∧
    FiniteDimensional ℂ (eigenspace (gram lam alpha hlam ha).toLinearMap mu) ∧
    FiniteDimensional ℂ (eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) ∧
    ContinuousLinearMap.IsFredholm
      (gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))) ∧
    ContinuousLinearMap.IsFredholm
      (outputGram lam alpha hlam ha -
        mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)) := by
  refine ⟨two_sided_gram_nonzero_spectrum_iff lam alpha hlam ha mu hmu,
    ?_, sourceGram_nonzero_eigenspace_finiteDimensional lam alpha hlam ha mu hmu,
    outputGram_nonzero_eigenspace_finiteDimensional lam alpha hlam ha mu hmu,
    sourceGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu,
    outputGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu⟩
  intro hspec
  obtain ⟨heig, hreal, hpos⟩ :=
    (sourceGram_nonzero_spectrum_iff_positive_eigenvalue
      lam alpha hlam ha mu hmu).mp hspec
  exact ⟨heig, (two_sided_gram_hasEigenvalue_iff
    lam alpha hlam ha mu hmu).mp heig, hreal, hpos⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_nonzero_spectrum_iff_positive_eigenvalue
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_spectrum_iff_positive_eigenvalue
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonzero_outside_spectrum_resolvent
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonzero_riesz_schauder_classification

end GegenbauerFock.GeneralUltrasphericalFock
