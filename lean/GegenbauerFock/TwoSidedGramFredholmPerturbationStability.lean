import GegenbauerFock.TwoSidedGramRieszSchauderClassification
import Mathlib.Analysis.Normed.Operator.Fredholm.Open

/-!
# V007 — local stability of both full Gram Fredholm shifts

Each nonzero spectral shift of the source and output Gram is Fredholm
by the kernel-certified bilateral compact-selfadjoint theorem.
Mathlib's openness of the Fredholm locus and local constancy of
the Fredholm index then yield robust neighborhoods in operator norm
around both genuine infinite-dimensional Gram shifts.

This does not assert an index value at any fixed shift; it certifies
local invariance of the index under bounded-operator perturbations.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Fredholmness and the Fredholm index of a nonzero source Gram shift
are locally stable under arbitrary bounded endomorphism perturbations. -/
theorem sourceGram_nonzero_shift_fredholm_index_locally_stable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    ∀ᶠ T : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam) in
      𝓝 (gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))),
      T.IsFredholm ∧
        T.index = (gram lam alpha hlam ha -
          mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
            Lp ℂ 2 (Ultraspherical.measure lam))).index := by
  have hf := sourceGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu
  exact hf.eventually_nhds.and hf.eventually_nhds_index_eq

/-- The complete Fock coefficient-side Gram has the same local
Fredholm and index stability under bounded endomorphism perturbations. -/
theorem outputGram_nonzero_shift_fredholm_index_locally_stable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    ∀ᶠ T : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients in
      𝓝 (outputGram lam alpha hlam ha -
        mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)),
      T.IsFredholm ∧
        T.index = (outputGram lam alpha hlam ha -
          mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
            InfiniteAnalysis.FockCoefficients)).index := by
  have hf := outputGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu
  exact hf.eventually_nhds.and hf.eventually_nhds_index_eq

/-- Both genuine Gram shifts have independent, locally constant
Fredholm indices at every common nonzero complex parameter. -/
theorem two_sided_gram_nonzero_fredholm_index_locally_stable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (∀ᶠ T : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam) in
        𝓝 (gram lam alpha hlam ha -
          mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
            Lp ℂ 2 (Ultraspherical.measure lam))),
        T.IsFredholm ∧
          T.index = (gram lam alpha hlam ha -
            mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
              Lp ℂ 2 (Ultraspherical.measure lam))).index) ∧
    (∀ᶠ T : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients in
        𝓝 (outputGram lam alpha hlam ha -
          mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
            InfiniteAnalysis.FockCoefficients)),
        T.IsFredholm ∧
          T.index = (outputGram lam alpha hlam ha -
            mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
              InfiniteAnalysis.FockCoefficients)).index) :=
  ⟨sourceGram_nonzero_shift_fredholm_index_locally_stable lam alpha hlam ha mu hmu,
    outputGram_nonzero_shift_fredholm_index_locally_stable lam alpha hlam ha mu hmu⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_nonzero_shift_fredholm_index_locally_stable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_shift_fredholm_index_locally_stable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonzero_fredholm_index_locally_stable

end GegenbauerFock.GeneralUltrasphericalFock
