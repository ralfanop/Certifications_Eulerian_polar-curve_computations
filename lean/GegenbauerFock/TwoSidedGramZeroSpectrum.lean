import GegenbauerFock.GramZeroInSpectrum
import GegenbauerFock.OutputGramSpectrum
import GegenbauerFock.CompactFockProperDenseRange
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# V007 — zero in both true Hilbert Gram spectra

For the actual Gegenbauer--Fock map C, the source Gram C†C has
normalized approximate-zero eigenvectors; zero therefore lies in
its spectrum even though its zero eigenspace is trivial.

On the coefficient side CC† is compact on the infinite-dimensional
Fock coefficient Hilbert space. If it were invertible, composition
with its bounded inverse would make the identity compact, forcing
finite dimensionality. Hence zero lies in its spectrum as well.

No finite spectral truncation, point spectrum at zero, or unproved
isometric equivalence of the two Hilbert spaces is assumed.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Zero belongs to the spectrum of the genuine output Gram CC† on
the infinite complex Fock coefficient Hilbert space. -/
theorem outputGram_zero_mem_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈ spectrum ℂ (outputGram lam alpha hlam ha) := by
  apply spectrum.zero_mem ℂ
  intro hunit
  have hbij : Function.Bijective (outputGram lam alpha hlam ha) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  have hker : (outputGram lam alpha hlam ha).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hbij.1
  have hrange : (outputGram lam alpha hlam ha).range = ⊤ :=
    LinearMap.range_eq_top.mpr hbij.2
  let e : InfiniteAnalysis.FockCoefficients ≃L[ℂ]
      InfiniteAnalysis.FockCoefficients :=
    ContinuousLinearEquiv.ofBijective
      (outputGram lam alpha hlam ha) hker hrange
  have hcompact : IsCompactOperator
      ((outputGram lam alpha hlam ha) ∘
        (e.symm : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)) :=
    (outputGram_compact lam alpha hlam ha).comp_clm
      (e.symm : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)
  have hcomp_id :
      ((outputGram lam alpha hlam ha) ∘
        (e.symm : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)) =
        (id : InfiniteAnalysis.FockCoefficients →
          InfiniteAnalysis.FockCoefficients) := by
    funext F
    exact e.apply_symm_apply F
  rw [hcomp_id] at hcompact
  exact fockCoefficients_not_finiteDimensional
    (FiniteDimensional.of_isCompactOperator_id hcompact)

/-- Zero is in both operator spectra, despite the previously
kernel-certified vanishing of their two zero eigenspaces. -/
theorem two_sided_gram_zero_mem_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈ spectrum ℂ (gram lam alpha hlam ha) ∧
      (0 : ℂ) ∈ spectrum ℂ (outputGram lam alpha hlam ha) :=
  ⟨gram_zero_mem_spectrum lam alpha hlam ha,
    outputGram_zero_mem_spectrum lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_zero_mem_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_zero_mem_spectrum

end GegenbauerFock.GeneralUltrasphericalFock
